import Mathlib

namespace OAI

namespace LargeIndependentSets.CubeGradient
open scoped BigOperators NNReal
open MeasureTheory

theorem sum_coordinate_norm_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : (ι → ℝ) →L[ℝ] ℝ) :
    (∑ i, |A (Pi.single i 1)|) ≤ ‖A‖ := by
  let v : ι → ℝ := fun i => if 0 ≤ A (Pi.single i 1) then 1 else -1
  have hv : ‖v‖ ≤ 1 := by
    apply (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ) ≤ 1)).mpr
    intro i
    dsimp [v]
    split_ifs <;> norm_num
  have hvsum : (∑ i, |A (Pi.single i 1)|) = A v := by
    conv_rhs => rw [← Finset.univ_sum_single v]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    have he : Pi.single i (v i) = v i • (Pi.single i (1:ℝ)) := by
      ext j
      by_cases hj : j = i
      · subst j; simp
      · simp [hj]
    rw [he, map_smul, smul_eq_mul]
    dsimp [v]
    split_ifs with hi
    · simp [abs_of_nonneg hi]
    · simp [abs_of_neg (lt_of_not_ge hi)]
  rw [hvsum]
  exact (le_abs_self (A v)).trans (by simpa only [Real.norm_eq_abs] using A.unit_le_opNorm v hv)

theorem lipschitz_sum_partials {n : ℕ} {L : ℝ≥0} {f : (Fin n → ℝ) → ℝ}
    (hf : LipschitzWith L f) (x : Fin n → ℝ) :
    (∑ i, |fderiv ℝ f x (Pi.single i 1)|) ≤ L :=
  (sum_coordinate_norm_le (fderiv ℝ f x)).trans (norm_fderiv_le_of_lipschitz ℝ hf)

end LargeIndependentSets.CubeGradient

end OAI
