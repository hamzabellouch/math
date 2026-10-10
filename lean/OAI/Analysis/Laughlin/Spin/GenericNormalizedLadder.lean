import OAI.Analysis.Laughlin.Spin.Basic

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators Matrix

theorem genericUnitDescendant_lowering (A B z n : ℕ) (hA : z ≤ A) (hB : z ≤ B)
    (hn : n < genericCoupledWeight A B z) :
    (totalRaise A B)ᵀ *ᵥ genericUnitDescendant A B z hA hB n =
      Real.sqrt (((n : ℝ)+1)*((genericCoupledWeight A B z : ℝ)-n)) •
        genericUnitDescendant A B z hA hB (n+1) := by
  have hp := genericDescendant_norm_pos A B z n hA hB (by omega)
  have hp₁ := genericDescendant_norm_pos A B z (n+1) hA hB (by omega)
  have hnreal : (n : ℝ) < genericCoupledWeight A B z := by exact_mod_cast hn
  have hc : 0 < ((n : ℝ)+1)*((genericCoupledWeight A B z : ℝ)-n) := by positivity
  have hden : Real.sqrt (vectorNormSq (genericDescendant A B z hA hB (n+1))) =
      Real.sqrt (((n : ℝ)+1)*((genericCoupledWeight A B z : ℝ)-n))*
        Real.sqrt (vectorNormSq (genericDescendant A B z hA hB n)) := by
    rw [genericDescendant_norm_step A B z n hA hB,Real.sqrt_mul (le_of_lt hc)]
  have hs : (Real.sqrt (vectorNormSq (genericDescendant A B z hA hB n)))⁻¹ =
      Real.sqrt (((n : ℝ)+1)*((genericCoupledWeight A B z : ℝ)-n))*
        (Real.sqrt (vectorNormSq (genericDescendant A B z hA hB (n+1))))⁻¹ := by
    rw [hden,mul_inv_rev]
    field_simp [ne_of_gt (Real.sqrt_pos.mpr hc)]
  unfold genericUnitDescendant
  rw [Matrix.mulVec_smul,← genericDescendant_succ,smul_smul,hs]

end Laughlin.Spin

end OAI
