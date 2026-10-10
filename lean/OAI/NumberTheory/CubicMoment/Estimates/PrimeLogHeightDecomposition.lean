import OAI.NumberTheory.CubicMoment.Estimates.PrimeModelLogTail
import OAI.NumberTheory.CubicMoment.Estimates.PrimeLowHeight

namespace OAI

/-! The sharp prime comparison with the logarithmic central cutoff
needed for the low-height corrected estimates. -/
noncomputable section
open Filter
open scoped BigOperators
namespace CubicFirstMoment

theorem sharp_prime_comparison_log_height_remainder {C ρ : ℝ}
    (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hρ : 0 < ρ) (hρ1 : ρ < 5/6) (T : ℝ → ℝ)
    (hT : ∀ᶠ X : ℝ in atTop, (1+Real.log X)^8 ≤ T X) (ℓ : ℤ) :
    (fun X : ℝ => sharpDyadicPrimeComparison ℓ X -
      ((2*Real.pi:ℝ):ℂ)⁻¹*(primeComparisonLowHeight ℓ (X^(1/6+ρ:ℝ)) (T X) X +
        primeGaussHeightTail ℓ (X^(1/6+ρ:ℝ)) (T X) X))
      =o[atTop] firstMomentScale := by
  have hm := actual_prime_model_log_tail_isLittleO hMV hC
    (show 0 < (1/6:ℝ)+ρ by linarith) (show (1/6:ℝ)+ρ < 1 by linarith) T hT ℓ
  have he := prime_sharp_interval_error_isLittleO hρ hρ1.le
    (show 0 ≤ 1+cStar by linarith [cStar_pos])
    (fun X => primeCutoff (4*X)) (fun _ => primeComparisonCoefficient ℓ)
    (fun X _ p hp => mem_primeCutoff.mp hp)
    (fun X _ p hp => primeComparisonCoefficient_bound ℓ (mem_primeCutoff.mp hp).1)
  apply (he.sub (hm.const_mul_left (((2*Real.pi:ℝ):ℂ)⁻¹*(cStar:ℂ)))).congr'
    _ Filter.EventuallyEq.rfl
  filter_upwards [hT,eventually_gt_atTop (1:ℝ)] with X hT hX
  have hTp : 0 < T X := (pow_pos (by linarith [Real.log_pos hX]) 8).trans_le hT
  rw [sharp_prime_comparison_low_tail ℓ
    (Real.rpow_pos_of_pos (zero_lt_one.trans hX) _) hTp (zero_lt_one.trans hX)]
  ring

theorem sharp_prime_comparison_fixed_log_height_remainder {C ρ : ℝ}
    (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hρ : 0 < ρ) (hρ1 : ρ < 5/6) (Ct : ℕ) (hCt : 8 ≤ Ct) (ℓ : ℤ) :
    (fun X : ℝ => sharpDyadicPrimeComparison ℓ X -
      ((2*Real.pi:ℝ):ℂ)⁻¹*(primeComparisonLowHeight ℓ (X^(1/6+ρ:ℝ))
          ((1+Real.log X)^Ct) X +
        primeGaussHeightTail ℓ (X^(1/6+ρ:ℝ)) ((1+Real.log X)^Ct) X))
      =o[atTop] firstMomentScale := by
  apply sharp_prime_comparison_log_height_remainder hMV hC hρ hρ1 _ _ ℓ
  filter_upwards [eventually_ge_atTop (1:ℝ)] with X hX
  exact pow_le_pow_right₀ (by linarith [Real.log_nonneg hX]) hCt

end CubicFirstMoment

end

end OAI
