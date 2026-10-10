import OAI.NumberTheory.CubicMoment.Estimates.PrimeCoordinatePowers

namespace OAI

noncomputable section
open Filter
namespace CubicFirstMoment

lemma eventual_dilated_shift_height_bound :
    ∃ Y₀ : ℝ, ∀ Y : ℝ, Y₀ ≤ Y → ∀ t τ : ℝ,
      |t| ≤ Y^(721/2000:ℝ) → |τ| ≤ Y^(1/1000:ℝ) → |t-τ| ≤ Y^(361/1000:ℝ) := by
  obtain ⟨T,hT⟩ := eventually_atTop.mp
    ((tendsto_rpow_atTop (show (0:ℝ) < 1/2000 by norm_num)).eventually_ge_atTop (2:ℝ))
  refine ⟨max 1 T,?_⟩
  intro Y hY t τ ht hτ
  have hY1 : 1 ≤ Y := (le_max_left _ _).trans hY
  have hYp : 0 < Y := zero_lt_one.trans_le hY1
  have hτ' : |τ| ≤ Y^(721/2000:ℝ) := hτ.trans
    (Real.rpow_le_rpow_of_exponent_le hY1 (by norm_num))
  calc
    _ ≤ |t|+|τ| := by simpa only [sub_zero,zero_sub,abs_neg] using abs_sub_le t 0 τ
    _ ≤ 2*Y^(721/2000:ℝ) := by linarith
    _ ≤ Y^(1/2000:ℝ)*Y^(721/2000:ℝ) :=
      mul_le_mul_of_nonneg_right (hT Y ((le_max_right _ _).trans hY)) (Real.rpow_nonneg hYp.le _)
    _ = _ := by rw [← Real.rpow_add hYp]; norm_num

end CubicFirstMoment

end

end OAI
