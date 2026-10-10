import OAI.Probability.MatroidProphet.Algorithm.Statistics

namespace OAI

namespace MatroidProphet.MainAlgorithm
open Set Finset
variable {n : ℕ}

lemma groupMask_function_eq_inter (M : Matroid (Fin n)) (d : MainMasks n)
    (w : Fin n → Option ℤ) (mask : Finset (Fin n)) :
    groupMask M d w mask = fun j => (mask : Set (Fin n)) ∩ (pathGroups M d w j : Set (Fin n)) := by
  funext j
  exact groupMask_eq_inter M d w mask j

lemma listedZ_update_T (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (d : MainMasks n) (w : Fin n → Option ℤ) (h : ℕ) (T : Finset (Fin n)) :
    listedZ M hE {d with T := T} w h =
      nominalRankStatistic M hE (2^100) (groupMask M d w d.D) (groupMask M d w d.C)
        (fun j => (T : Set (Fin n)) ∩ (pathGroups M d w j : Set (Fin n))) h (pathGroups M d w h)
        ((d.H ∪ d.D ∪ d.C : Finset (Fin n)) : Set (Fin n)) (boolParity d.odd) := by
  unfold listedZ
  change nominalRankStatistic M hE (2^100) (groupMask M d w d.D) (groupMask M d w d.C)
    (groupMask M d w T) h (groupMask M d w univ h)
      ((d.H ∪ d.D ∪ d.C : Finset (Fin n)) : Set (Fin n)) (boolParity d.odd) = _
  rw [groupMask_function_eq_inter M d w T, ← pathGroups_coe]

lemma listedLambda_update_T (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (d : MainMasks n) (w : Fin n → Option ℤ) (h : ℕ) (T : Finset (Fin n)) :
    listedLambda M hE {d with T := T} w h =
      finalRankStatistic M hE (2^100) (groupMask M d w d.D) (groupMask M d w d.C)
        (fun j => (T : Set (Fin n)) ∩ (pathGroups M d w j : Set (Fin n))) h (groups M d w).length
        (pathGroups M d w h) ((d.H ∪ d.D ∪ d.C : Finset (Fin n)) : Set (Fin n))
        (T : Set (Fin n)) (boolParity d.odd) := by
  unfold listedLambda
  change finalRankStatistic M hE (2^100) (groupMask M d w d.D) (groupMask M d w d.C)
    (groupMask M d w T) h (groups M d w).length (groupMask M d w univ h)
      ((d.H ∪ d.D ∪ d.C : Finset (Fin n)) : Set (Fin n)) (T : Set (Fin n)) (boolParity d.odd) = _
  rw [groupMask_function_eq_inter M d w T, ← pathGroups_coe]

theorem listed_expected_nominal_to_final (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (d : MainMasks n) (w : Fin n → Option ℤ) (h : ℕ) (hh : h < (groups M d w).length)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    densityThreshold * t * bitsExpectation (fun _ : Fin n => t) univ (fun T =>
      (listedZ M hE {d with T := T} w h : ℝ)) ≤
    densityThreshold * bitsExpectation (fun _ : Fin n => t) univ (fun T =>
      (listedLambda M hE {d with T := T} w h : ℝ)) +
      t * ((2^100) * (groupMask M d w d.C h).ncard +
        ∑ j ∈ range ((groups M d w).length-(h+1)),
          ((2^100) * (groupMask M d w d.C (h+1+j)).ncard +
            (groupMask M d w d.D (h+1+j)).ncard) : ℕ) := by
  have hc := expected_nominal_to_final M hE (2^100) (by positivity)
    (groupMask M d w d.D) (groupMask M d w d.C) (pathGroups M d w)
    (pathGroups_disjoint M d w) h ((groups M d w).length-(h+1))
    ((d.H ∪ d.D ∪ d.C : Finset (Fin n)) : Set (Fin n)) (boolParity d.odd) t ht0 ht1
  have hlen : h+1+((groups M d w).length-(h+1)) = (groups M d w).length := by omega
  rw [hlen] at hc
  simp only [listedZ_update_T, listedLambda_update_T]
  convert hc using 1 <;> norm_num [densityThreshold]

end MatroidProphet.MainAlgorithm

end OAI
