import OAI.Analysis.HyperbolicCones.DeformationRoots

namespace OAI

noncomputable section

open Set Polynomial

namespace Paper256

theorem intervalPolynomial_component (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    connectedComponentIn {x : ℝ | (intervalPolynomial a b).eval x ≠ 0} 0 =
      Ioo (-b) a := by
  let S := {x : ℝ | (intervalPolynomial a b).eval x ≠ 0}
  have h0 : (0 : ℝ) ∈ S := by simp [S, intervalPolynomial_eval]
  have hz := mem_connectedComponentIn h0
  have hc : OrdConnected (connectedComponentIn S 0) :=
    isPreconnected_connectedComponentIn.ordConnected
  apply subset_antisymm
  · intro x hx
    constructor
    · by_contra h
      have hm : -b ∈ connectedComponentIn S 0 :=
        hc.out hx hz ⟨le_of_not_gt h, by linarith⟩
      have hn := connectedComponentIn_subset S 0 hm
      simp [S, intervalPolynomial_eval, hb.ne'] at hn
    · by_contra h
      have hm : a ∈ connectedComponentIn S 0 :=
        hc.out hz hx ⟨ha.le, le_of_not_gt h⟩
      have hn := connectedComponentIn_subset S 0 hm
      simp [S, intervalPolynomial_eval, ha.ne'] at hn
  · apply isPreconnected_Ioo.subset_connectedComponentIn
    · exact ⟨by linarith, ha⟩
    · intro x hx hn
      have hr : (intervalPolynomial a b).IsRoot x := hn
      rcases (intervalPolynomial_isRoot_iff a b x ha.ne' hb.ne').mp hr with h | h
      · exact (ne_of_gt hx.1) h
      · exact (ne_of_lt hx.2) h

theorem intervalPolynomial_rigidlyConvexSet (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    rigidlyConvexSet (intervalPolynomial a b) = Icc (-b) a := by
  rw [rigidlyConvexSet, intervalPolynomial_component a b ha hb,
    closure_Ioo (by linarith : -b ≠ a)]

theorem deformedPolynomial_rigidlyConvexSet (a b η t : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hη : 0 < η) :
    rigidlyConvexSet (deformedPolynomial a b η t) =
      Icc (-b / timeScale η t) (a / timeScale η t) := by
  rw [deformedPolynomial_scaled, intervalPolynomial_rigidlyConvexSet _ _
    (div_pos ha (timeScale_positive η t hη))
    (div_pos hb (timeScale_positive η t hη)), neg_div]

theorem deformedPolynomial_strict_subset (a b η t : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hη : 0 < η) (ht : t ∈ Ioo (0 : ℝ) 1) :
    rigidlyConvexSet (deformedPolynomial a b η t) ⊂
      rigidlyConvexSet (intervalPolynomial a b) := by
  rw [deformedPolynomial_rigidlyConvexSet a b η t ha hb hη,
    intervalPolynomial_rigidlyConvexSet a b ha hb]
  have hc := timeScale_strict_interior η t hη ht
  have hleft : -b ≤ -b / timeScale η t := by
    rw [neg_div]
    exact neg_le_neg (div_le_self hb.le hc.le)
  have hright := div_lt_self ha hc
  refine ssubset_iff_subset_ne.mpr ⟨Icc_subset_Icc hleft hright.le, ?_⟩
  intro h
  have hm : a ∈ Icc (-b / timeScale η t) (a / timeScale η t) := by
    rw [h]
    exact ⟨by linarith, le_rfl⟩
  exact (not_le_of_gt hright) hm.2

theorem arbitrarily_small_deformation (a b ε : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ η < ε ∧ ∀ t ∈ Ioo (0 : ℝ) 1,
      rigidlyConvexSet (deformedPolynomial a b η t) ⊂
        rigidlyConvexSet (intervalPolynomial a b) := by
  refine ⟨ε / 2, by positivity, by linarith, ?_⟩
  intro t ht
  exact deformedPolynomial_strict_subset a b (ε / 2) t ha hb (by positivity) ht

end Paper256

end

end OAI
