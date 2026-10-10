import OAI.NumberTheory.CubicMoment.Estimates.SmallBCommonScale

namespace OAI

/-! A fixed power cutoff guarantees that every retained quotient row
satisfies the integer size requirements of the small-B estimate. -/
noncomputable section
namespace CubicFirstMoment

lemma smallB_common_floor_large {Z k : ℝ} (hZ : 65536 ≤ Z) (hk : 0 < k)
    (hkZ : k ≤ Z^(1/1000:ℝ)) :
    4 ≤ (⌊Z/k⌋₊:ℝ) ∧ 16 ≤ (⌊Z/k⌋₊:ℝ)^(3/4:ℝ) := by
  have hZ₁ : 1 ≤ Z := by linarith
  have hZp : 0 < Z := by linarith
  have hhalf : k ≤ Z^(1/2:ℝ) := hkZ.trans
    (Real.rpow_le_rpow_of_exponent_le hZ₁ (by norm_num))
  have hratio : Z^(1/2:ℝ) ≤ Z/k := by
    calc
      _ = Z/Z^(1/2:ℝ) := by
        have he := Real.rpow_sub hZp (1:ℝ) (1/2:ℝ)
        norm_num at he
        exact he
      _ ≤ _ := div_le_div_of_nonneg_left hZp.le hk hhalf
  have hroot : 256 ≤ Z^(1/2:ℝ) := by
    rw [← Real.sqrt_eq_rpow]
    nlinarith [Real.sq_sqrt hZp.le,Real.sqrt_nonneg Z]
  have hf : 256 ≤ ⌊Z/k⌋₊ := Nat.le_floor (by exact_mod_cast hroot.trans hratio)
  have hfr : (256:ℝ) ≤ (⌊Z/k⌋₊:ℝ) := by exact_mod_cast hf
  refine ⟨by linarith,?_⟩
  have hs : 16 ≤ (⌊Z/k⌋₊:ℝ)^(1/2:ℝ) := by
    rw [← Real.sqrt_eq_rpow]
    nlinarith [Real.sq_sqrt (show 0 ≤ (⌊Z/k⌋₊:ℝ) by positivity),
      Real.sqrt_nonneg (⌊Z/k⌋₊:ℝ)]
  exact hs.trans (Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num))

end CubicFirstMoment

end

end OAI
