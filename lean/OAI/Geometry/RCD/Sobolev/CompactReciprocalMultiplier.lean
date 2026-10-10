import Mathlib

namespace OAI

/-! # A compact multiplier divided by a locally positive continuous function -/

open Set Metric
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [TopologicalSpace X]

theorem compact_reciprocal_multiplier_bound (φ F : X → ℝ)
    (hφ : Continuous φ) (hs : HasCompactSupport φ) (hF : Continuous F)
    (hpos : ∀ x ∈ tsupport φ, 0 < F x) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |φ x/F x| ≤ C := by
  obtain ⟨M,hM⟩ := hs.exists_bound_of_continuous hφ
  obtain ⟨a,ha,haF⟩ := hs.exists_forall_le' hF.continuousOn hpos
  refine ⟨max 0 (M/a),le_max_left _ _,?_⟩
  intro x
  by_cases hx : x ∈ tsupport φ
  · have hFx := ha.trans_le (haF x hx)
    rw [abs_div,abs_of_pos hFx]
    exact ((div_le_div_of_nonneg_left (abs_nonneg _) ha (haF x hx)).trans
      (div_le_div_of_nonneg_right (by simpa only [Real.norm_eq_abs] using hM x) ha.le)).trans
        (le_max_right _ _)
  · rw [image_eq_zero_of_notMem_tsupport hx,zero_div,abs_zero]
    exact le_max_left _ _

end RegularPointCoordinates

end

end OAI
