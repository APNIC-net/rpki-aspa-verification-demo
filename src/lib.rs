//! Implementation of the version
//! [17](https://datatracker.ietf.org/doc/html/draft-ietf-sidrops-aspa-verification-17) of the
//! [draft for BGP AS_PATH Verification Based on Autonomous System Provider Authorization (ASPA)
//! Objects](https://datatracker.ietf.org/doc/draft-ietf-sidrops-aspa-verification/).
use std::collections::{HashMap, HashSet};

use bgpkit_parser::models::{AsPath, AsPathSegment};

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum VerificationResult {
    Valid,
    Invalid(InvalidReason),
    Unknown,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum InvalidReason {
    SetInAsPath,
    UpstreamNotProviderPlus,
    DownstreamTooManyApexes,
}

pub enum PathType {
    Upstream,
    Downstream,
}

/// Performs the ASPA verification for the given `as_path` according to the defined `path_type`
/// (i.e. upstream or downstream) and collection of validated ASPAs provided.
///
/// The ASPAs are provided as a [HashMap] having the Customer AS (CAS) as keys represented by [u32], and the Set of
/// Provider ASes (SPAS) as values represented by [HashSet] of [u32].
pub fn verify(
    as_path: &AsPath,
    path_type: PathType,
    aspas: &HashMap<u32, HashSet<u32>>,
) -> VerificationResult {
    match path_type {
        PathType::Upstream => verify_upstream(as_path, aspas),
        PathType::Downstream => verify_downstream(as_path, aspas),
    }
}

/// Performs the [algorithm for upstream paths](https://www.ietf.org/archive/id/draft-ietf-sidrops-aspa-verification-17.html#name-algorithm-for-upstream-path).
///
/// 1. If the AS_PATH has an AS_SET, then the procedure halts with the outcome "Invalid".
/// 2. Collapse prepends in the AS_SEQUENCE(s) in the AS_PATH (i.e., keep only the unique AS numbers). Let the resulting ordered sequence be represented by {AS(N), AS(N-1), ..., AS(2), AS(1)}, where AS(1) is the first-added (i.e., origin) AS and AS(N) is the last-added AS and neighbor to the receiving/validating AS.
/// 3. If N = 1, then the procedure halts with the outcome "Valid". Else, continue.
/// 4. At this step, N ≥ 2. If there is an i such that 2 ≤ i ≤ N and hop(AS(i-1), AS(i)) = "Not Provider+", then the procedure halts with the outcome "Invalid". Else, continue.
/// 5. If there is an i such that 2 ≤ i ≤ N and hop(AS(i-1), AS(i)) = "No Attestation", then the procedure halts with the outcome "Unknown". Else, the procedure halts with the outcome "Valid".
///
/// It is assumed that any VAP-SPAS which have AS0 combined with other ASes have already been
/// filtered out before using this.
pub fn verify_upstream(as_path: &AsPath, aspas: &HashMap<u32, HashSet<u32>>) -> VerificationResult {
    // step 1
    if as_path
        .iter_segments()
        .any(|seg| matches!(seg, AsPathSegment::AsSet(_) | AsPathSegment::ConfedSet(_)))
    {
        return VerificationResult::Invalid(InvalidReason::SetInAsPath);
    }

    // step 2
    let mut collapsed_as_path = as_path.clone();
    collapsed_as_path.dedup_coalesce();

    // step 3
    if collapsed_as_path.route_len() == 1 {
        return VerificationResult::Valid;
    }

    // step 4
    let mut collapsed_as_path: Vec<u32> = collapsed_as_path
        .iter_segments()
        .filter_map(|seg| match seg {
            AsPathSegment::AsSequence(asns) => Some(asns),
            AsPathSegment::ConfedSequence(asns) => Some(asns),
            AsPathSegment::AsSet(_) => None, // should be none of these
            AsPathSegment::ConfedSet(_) => None, // should be none of these
        })
        .flatten()
        .map(u32::from)
        .collect();
    collapsed_as_path.reverse();
    for pair in collapsed_as_path.windows(2) {
        let customer_as = pair[0];
        let provider_as = pair[1];
        match hop_check(customer_as, provider_as, aspas) {
            HopStatus::NoAttestation => return VerificationResult::Unknown,
            HopStatus::ProviderPlus => (),
            HopStatus::NotProviderPlus => {
                return VerificationResult::Invalid(InvalidReason::UpstreamNotProviderPlus)
            }
        }
    }

    VerificationResult::Valid
}

/// Performs the [algorithm for downstream paths](https://www.ietf.org/archive/id/draft-ietf-sidrops-aspa-verification-17.html#name-algorithm-for-downstream-pa).
///
/// 1. If the AS_PATH has an AS_SET, then the procedure halts with the outcome "Invalid".
/// 2. Collapse prepends in the AS_SEQUENCE(s) in the AS_PATH (i.e., keep only the unique AS numbers). Let the resulting ordered sequence be represented by {AS(N), AS(N-1), ..., AS(2), AS(1)}, where AS(1) is the first-added (i.e., origin) AS and AS(N) is the last-added AS and neighbor to the receiving/validating AS.
/// 3. If 1 ≤ N ≤ 2, then the procedure halts with the outcome "Valid". Else, continue.
/// 4. At this step, N ≥ 3. Given the above-mentioned ordered sequence, find the lowest value of u (2 ≤ u ≤ N) for which hop(AS(u-1), AS(u)) = "Not Provider+". Call it u_min. If no such u_min exists, set u_min = N+1. Find the highest value of v (N-1 ≥ v ≥ 1) for which hop(AS(v+1), AS(v)) = "Not Provider+". Call it v_max. If no such v_max exists, then set v_max = 0. If u_min ≤ v_max, then the procedure halts with the outcome "Invalid". Else, continue.
/// 5. Up-ramp: For 2 ≤ i ≤ N, determine the largest K such that hop(AS(i-1), AS(i)) = "Provider+" for each i in the range 2 ≤ i ≤ K. If such a largest K does not exist, then set K = 1.
/// 6. Down-ramp: For N-1 ≥ j ≥ 1, determine the smallest L such that hop(AS(j+1), AS(j)) = "Provider+" for each j in the range N-1 ≥ j ≥ L. If such smallest L does not exist, then set L = N.
/// 7. If L-K ≤ 1, then the procedure halts with the outcome "Valid". Else, the procedure halts with the outcome "Unknown".
pub fn verify_downstream(
    as_path: &AsPath,
    aspas: &HashMap<u32, HashSet<u32>>,
) -> VerificationResult {
    // step 1
    if as_path
        .iter_segments()
        .any(|seg| matches!(seg, AsPathSegment::AsSet(_) | AsPathSegment::ConfedSet(_)))
    {
        return VerificationResult::Invalid(InvalidReason::SetInAsPath);
    }

    // step 2 - Collapse prepends in the AS_SEQUENCE(s) in the AS_PATH
    let mut collapsed_as_path = as_path.clone();
    collapsed_as_path.dedup_coalesce();

    // step 3
    let n = collapsed_as_path.route_len();
    if n <= 2 {
        return VerificationResult::Valid;
    }

    let mut collapsed_as_path: Vec<u32> = collapsed_as_path
        .iter_segments()
        .filter_map(|seg| match seg {
            AsPathSegment::AsSequence(asns) => Some(asns),
            AsPathSegment::ConfedSequence(asns) => Some(asns),
            AsPathSegment::AsSet(_) => None, // should be none of these
            AsPathSegment::ConfedSet(_) => None, // should be none of these
        })
        .flatten()
        .map(u32::from)
        .collect();
    collapsed_as_path.reverse();

    // Step 4
    let mut u_min = n + 1;
    for u in 2..=n {
        let u_idx = u - 1;
        let customer_as = collapsed_as_path[u_idx - 1];
        let provider_as = collapsed_as_path[u_idx];
        match hop_check(customer_as, provider_as, aspas) {
            HopStatus::NotProviderPlus => {
                u_min = u;
                break;
            }
            HopStatus::NoAttestation => (),
            HopStatus::ProviderPlus => (),
        }
    }

    let mut v_max = 0;
    for v in (1..=n - 1).rev() {
        let v_idx = v - 1;
        let customer_as = collapsed_as_path[v_idx + 1];
        let provider_as = collapsed_as_path[v_idx];
        match hop_check(customer_as, provider_as, aspas) {
            HopStatus::NotProviderPlus => {
                v_max = v;
                break;
            }
            HopStatus::NoAttestation => (),
            HopStatus::ProviderPlus => (),
        }
    }

    if u_min <= v_max {
        // More than one apex / too many ramps
        return VerificationResult::Invalid(InvalidReason::DownstreamTooManyApexes);
    }

    // Step 5
    let mut k = 1;
    for i in 2..=n {
        let i_idx = i - 1;
        let customer_as = collapsed_as_path[i_idx - 1];
        let provider_as = collapsed_as_path[i_idx];
        if hop_check(customer_as, provider_as, aspas) != HopStatus::ProviderPlus {
            k = i - 1;
            break;
        }
    }

    // Step 6
    let mut l = n;
    for j in (1..=n - 1).rev() {
        let j_idx = j - 1;
        let customer_as = collapsed_as_path[j_idx + 1];
        let provider_as = collapsed_as_path[j_idx];
        if hop_check(customer_as, provider_as, aspas) != HopStatus::ProviderPlus {
            l = j + 1;
            break;
        }
    }

    // Step 7
    if (l - k) <= 1 {
        VerificationResult::Valid
    } else {
        VerificationResult::Unknown
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum HopStatus {
    /// No entry in VAP-SPAS table for customer AS.
    NoAttestation,
    /// VAP-SPAS entry for customer AS includes the provider AS.
    ProviderPlus,
    /// There is a VAP-SPAS entry for the customer AS, but it does not include the provider AS.
    NotProviderPlus,
}

/// Performs the hop check function according to the [draft
/// spec](https://www.ietf.org/archive/id/draft-ietf-sidrops-aspa-verification-17.html#name-hop-check-function).
///
/// ```text
///                      /
///                      | "No Attestation" if there is no entry
///                      |   in VAP-SPAS table for CAS = AS(i)
///                      |
/// hop(AS(i), AS(j)) =  / Else, "Provider+" if the VAP-SPAS entry
///                      \   for CAS = AS(i) includes AS(j)
///                      |
///                      | Else, "Not Provider+"
///                      \
/// ```
///
///  where AS(i) = `customer_as` and AS(j) = `provider_as`.
pub fn hop_check(
    customer_as: u32,
    provider_as: u32,
    aspas: &HashMap<u32, HashSet<u32>>,
) -> HopStatus {
    match aspas.get(&customer_as) {
        Some(providers) => {
            if providers.len() == 1 && providers.contains(&0) {
                // Only having AS0 means there are no providers
                HopStatus::NotProviderPlus
            } else if providers.contains(&provider_as) {
                HopStatus::ProviderPlus
            } else {
                HopStatus::NotProviderPlus
            }
        }
        None => HopStatus::NoAttestation,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Upstream path with a single AS is always valid.
    #[test]
    fn test_upstream_single_element() {
        let aspas = HashMap::new();
        let as_path = AsPath::from_sequence([1]);
        assert_eq!(verify_upstream(&as_path, &aspas), VerificationResult::Valid);
    }

    /// Upstream path with more than one AS has outcome [Unknown](VerificationResult::Unknown) if
    /// there aren't enough VAP-SPAS entries to cover the whole path.
    #[test]
    fn test_upstream_no_aspas() {
        let aspas = HashMap::new();
        let as_path = AsPath::from_sequence([3, 2, 1]);
        assert_eq!(
            verify_upstream(&as_path, &aspas),
            VerificationResult::Unknown
        );
    }

    /// Upstream path with AS_SET in the path is always invalid.
    #[test]
    fn test_upstream_set_invalid() {
        let aspas = HashMap::new();
        let as_path =
            AsPath::from_segments(vec![AsPathSegment::sequence([1]), AsPathSegment::set([2])]);
        assert_eq!(
            verify_upstream(&as_path, &aspas),
            VerificationResult::Invalid(InvalidReason::SetInAsPath)
        );
    }

    /// Upstream path is valid if each step in the path is customer-to-provider.
    #[test]
    fn test_upstream_valid() {
        let mut aspas = HashMap::new();
        aspas.insert(1, HashSet::from_iter([2]));
        aspas.insert(2, HashSet::from_iter([3]));
        let as_path = AsPath::from_sequence([3, 2, 1]);
        assert_eq!(verify_upstream(&as_path, &aspas), VerificationResult::Valid);
    }

    /// Upstream path is invalid if any step in the path is not customer-to-provider, and each
    /// each customer has a VAP-SPAS entry.
    #[test]
    fn test_upstream_invalid() {
        let mut aspas = HashMap::new();
        aspas.insert(1, HashSet::from_iter([3]));
        aspas.insert(2, HashSet::from_iter([3]));
        let as_path = AsPath::from_sequence([3, 2, 1]);
        assert_eq!(
            verify_upstream(&as_path, &aspas),
            VerificationResult::Invalid(InvalidReason::UpstreamNotProviderPlus)
        );
    }

    /// Only AS0 in VAP-SPAS means there are no providers, so if the only step in the path has this,
    /// it's not possible for the whole path to be customer-to-provider.
    #[test]
    fn test_upstream_as0() {
        let mut aspas = HashMap::new();
        aspas.insert(1, HashSet::from_iter([0]));
        let as_path = AsPath::from_sequence([2, 1]);
        assert_eq!(
            verify_upstream(&as_path, &aspas),
            VerificationResult::Invalid(InvalidReason::UpstreamNotProviderPlus)
        );
    }

    /// Downstream path with a single AS is always valid.
    #[test]
    fn test_downstream_single_element() {
        let aspas = HashMap::new();
        let as_path = AsPath::from_sequence([1]);
        assert_eq!(
            verify_downstream(&as_path, &aspas),
            VerificationResult::Valid
        );
    }

    /// Downstream path with two ASes is always valid.
    #[test]
    fn test_downstream_two_elements() {
        let aspas = HashMap::new();
        let as_path = AsPath::from_sequence([2, 1]);
        assert_eq!(
            verify_downstream(&as_path, &aspas),
            VerificationResult::Valid
        );
    }

    /// From section 6.2.1-2:
    ///
    /// If there exist indices u and v such that
    ///
    /// 1. u <= v,
    /// 2. hop(AS(u-1), AS(u)) = "Not Provider+", and
    /// 3. hop(AS(v+1), AS(v)) = "Not Provider+",
    ///
    /// then the AS_PATH is Invalid.
    #[test]
    fn test_downstream_no_aspas() {
        let aspas = HashMap::new();
        let as_path = AsPath::from_sequence([3, 2, 1]);
        assert_eq!(
            verify_downstream(&as_path, &aspas),
            VerificationResult::Unknown
        );
    }

    /// Downstream path with AS_SET in the path is always invalid.
    #[test]
    fn test_downstream_set_invalid() {
        let aspas = HashMap::new();
        let as_path =
            AsPath::from_segments(vec![AsPathSegment::sequence([1]), AsPathSegment::set([2])]);
        assert_eq!(
            verify_downstream(&as_path, &aspas),
            VerificationResult::Invalid(InvalidReason::SetInAsPath)
        );
    }

    /// - Three-element AS_PATH
    /// - ASPA exists for AS1 (origin) with AS2 as provider
    ///
    /// Route leak not possible.
    ///
    /// ```text
    ///      AS3 -?- AS2
    ///      /         \
    /// receiver       AS1
    /// ```
    #[test]
    fn test_downstream_valid_3_element_origin_has_aspa() {
        let mut aspas = HashMap::new();
        aspas.insert(1, HashSet::from_iter([2]));
        let as_path = AsPath::from_sequence([3, 2, 1]);
        assert_eq!(
            verify_downstream(&as_path, &aspas),
            VerificationResult::Valid
        );
    }

    /// - Three-element AS_PATH
    /// - ASPA exists for AS3 (neighbour) with AS2 as provider
    ///
    /// Route leak not possible.
    ///
    /// ```text
    ///        AS2 -?- AS1
    ///        /
    ///      AS3
    ///      /
    /// receiver
    /// ```
    #[test]
    fn test_downstream_valid_3_element_neighbour_has_aspa() {
        let mut aspas = HashMap::new();
        aspas.insert(3, HashSet::from_iter([2]));
        let as_path = AsPath::from_sequence([3, 2, 1]);
        assert_eq!(
            verify_downstream(&as_path, &aspas),
            VerificationResult::Valid
        );
    }

    /// - Three-element AS_PATH
    /// - ASPA exists for AS1 and AS3, each with AS2 as provider
    ///
    /// Route leak not possible.
    ///
    /// ```text
    ///         AS2
    ///        /   \
    ///      AS3   AS1
    ///      /
    /// receiver
    /// ```
    #[test]
    fn test_downstream_valid_3_element_neighbour_and_origin_have_aspa() {
        let mut aspas = HashMap::new();
        aspas.insert(1, HashSet::from_iter([2]));
        aspas.insert(3, HashSet::from_iter([2]));
        let as_path = AsPath::from_sequence([3, 2, 1]);
        assert_eq!(
            verify_downstream(&as_path, &aspas),
            VerificationResult::Valid
        );
    }

    /// - Three-element AS_PATH
    /// - ASPA exists for AS1 and AS3, each with AS2 as provider
    /// - ASPA exists for AS2 with no providers
    ///
    /// Route leak not possible.
    ///
    ///```text
    ///         AS2
    ///        /   \
    ///      AS3   AS1
    ///      /
    /// receiver
    /// ```
    #[test]
    fn test_downstream_valid_3_element_all_have_aspa() {
        let mut aspas = HashMap::new();
        aspas.insert(1, HashSet::from_iter([2]));
        aspas.insert(2, HashSet::from_iter([0]));
        aspas.insert(3, HashSet::from_iter([2]));
        let as_path = AsPath::from_sequence([3, 2, 1]);
        assert_eq!(
            verify_downstream(&as_path, &aspas),
            VerificationResult::Valid
        );
    }

    /// - Three-element AS_PATH
    /// - ASPA exists for AS1, but does not include AS2
    /// - ASPA exists for AS3, with AS2 as provider
    ///
    /// Route leak not possible.
    ///
    /// ```text
    ///        AS2 -X- AS1
    ///        /
    ///      AS3
    ///      /
    /// receiver
    /// ```
    #[test]
    fn test_downstream_valid_3_element_aspa_without_provider() {
        let mut aspas = HashMap::new();
        aspas.insert(1, HashSet::from_iter([4]));
        aspas.insert(3, HashSet::from_iter([2]));
        let as_path = AsPath::from_sequence([3, 2, 1]);
        assert_eq!(
            verify_downstream(&as_path, &aspas),
            VerificationResult::Valid
        );
    }

    /// - Three-element AS_PATH
    /// - ASPA exists for AS1, but does not include AS2
    /// - ASPA does not exist for AS3
    ///
    /// Unable to determine validity status.
    ///
    ///```text
    ///      AS3 -?- AS2 -X- AS1
    ///      /
    /// receiver
    ///```
    #[test]
    fn test_downstream_unknown_3_element_not_enough_good_aspas() {
        let mut aspas = HashMap::new();
        aspas.insert(1, HashSet::from_iter([4]));
        let as_path = AsPath::from_sequence([3, 2, 1]);
        assert_eq!(
            verify_downstream(&as_path, &aspas),
            VerificationResult::Unknown
        );
    }

    /// - Three-element AS_PATH
    /// - ASPA exists for AS1 and AS3, but neither includes AS2
    ///
    /// Route leak.
    ///
    ///```text
    ///      AS3 -X- AS2 -X- AS1
    ///      /
    /// receiver
    ///```
    #[test]
    fn test_downstream_invalid_3_element_path() {
        let mut aspas = HashMap::new();
        aspas.insert(1, HashSet::from_iter([4]));
        aspas.insert(3, HashSet::from_iter([5]));
        let as_path = AsPath::from_sequence([3, 2, 1]);
        assert_eq!(
            verify_downstream(&as_path, &aspas),
            VerificationResult::Invalid(InvalidReason::DownstreamTooManyApexes)
        );
    }

    /// Multiple apexes means invalid path.
    ///
    /// ```text
    ///          AS4     AS2
    ///         /   \   /   \
    /// receiver     AS3    AS1
    /// ```
    #[test]
    fn test_downstream_multiple_apexes() {
        let mut aspas = HashMap::new();
        aspas.insert(1, HashSet::from_iter([2]));
        aspas.insert(2, HashSet::from_iter([0]));
        aspas.insert(3, HashSet::from_iter([2, 4]));
        aspas.insert(4, HashSet::from_iter([0]));
        let as_path = AsPath::from_sequence([4, 3, 2, 1]);
        assert_eq!(
            verify_downstream(&as_path, &aspas),
            VerificationResult::Invalid(InvalidReason::DownstreamTooManyApexes)
        );
    }
}
