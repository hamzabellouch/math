import OAI.NumberTheory.CubicMoment.Decomposition.PrimeProductEnvelope
import OAI.NumberTheory.CubicMoment.Estimates.TypeIProductFourier
import OAI.NumberTheory.CubicMoment.Estimates.CenteredPrimeKernel

namespace OAI

/-! The exact sharp comparison through a smooth total-product weight.
The model tail and the endpoint error remain negligible uniformly in this
fixed weight, so the remaining integrals are precisely the detector kernels. -/
noncomputable section
open Filter
open scoped BigOperators
namespace CubicFirstMoment

def primeProductLowHeight (ℓ : ℤ) (H T X : ℝ) : ℂ :=
  ∑ p ∈ primeCutoff (4*X), centeredHeightKernel ℓ primeProductEnvelope H T X X p

def primeProductGaussTail (ℓ : ℤ) (H T X : ℝ) : ℂ :=
  finiteHeightTail (primeCutoff (4*X))
    (fun p => primeProductEnvelope (norm p/X)*theta ℓ p*gaussAtPrime p) H T X

lemma primeProductLowHeight_eq (ℓ : ℤ) (H T X : ℝ) :
    primeProductLowHeight ℓ H T X = finiteHeightLow (primeCutoff (4*X))
      (fun p => primeProductEnvelope (norm p/X)*primeComparisonCoefficient ℓ p) H T X := by
  unfold primeProductLowHeight finiteHeightLow
  apply Finset.sum_congr rfl
  intro p hp
  change (theta ℓ p*centeredGauss p)*primeProductEnvelope (norm p/X)*
      heightFourierIntegral (lowHeightWeight H T) (Real.log (norm p)-Real.log X) =
    (primeProductEnvelope (norm p/X)*primeComparisonCoefficient ℓ p)*
      heightFourierIntegral (lowHeightWeight H T) (Real.log (norm p)-Real.log X)
  rw [theta_centeredGauss_primaryPrime ℓ (mem_primeCutoff.mp hp).1]
  ring

lemma sharp_prime_product_low_tail (ℓ : ℤ) {H T X : ℝ}
    (hH : 0 < H) (hT : 0 < T) (hX : 0 < X) :
    sharpDyadicPrimeComparison ℓ X =
      ((2*Real.pi:ℝ):ℂ)⁻¹*(primeProductLowHeight ℓ H T X +
        primeProductGaussTail ℓ H T X - (cStar:ℂ)*
          primeModelWindowSum (primeCutoff (4*X))
            (fun p => primeProductEnvelope (norm p/X)) ℓ H T X) +
      ∑ p ∈ primeCutoff (4*X),
        (primeProductEnvelope (norm p/X)*primeComparisonCoefficient ℓ p)*
          sharpIntervalError X H (norm p) := by
  have hs : sharpDyadicPrimeComparison ℓ X =
      (∑ p ∈ primeCutoff (4*X),
        (primeProductEnvelope (norm p/X)*primeComparisonCoefficient ℓ p)*smoothLogInterval H (norm p/X)) +
      ∑ p ∈ primeCutoff (4*X),
        (primeProductEnvelope (norm p/X)*primeComparisonCoefficient ℓ p)*sharpIntervalError X H (norm p) := by
    rw [sharpDyadicPrimeComparison_envelope ℓ hX,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p _
    unfold sharpIntervalError
    ring
  have hc : (fun p => primeProductEnvelope (norm p/X)*primeComparisonCoefficient ℓ p) =
      (fun p => primeProductEnvelope (norm p/X)*theta ℓ p*gaussAtPrime p -
        (cStar:ℂ)*(primeProductEnvelope (norm p/X)*theta ℓ p*((norm p^(-1/6:ℝ):ℝ):ℂ))) := by
    funext p
    unfold primeComparisonCoefficient
    push_cast
    ring
  rw [hs,finite_smooth_low_tail _ _ hH hT hX
    (fun p hp => (mem_primeCutoff.mp hp).1.2.ne_zero),←primeProductLowHeight_eq,hc,
    finiteHeightTail_linear]
  simp only [primeProductGaussTail,primeModelWindowSum,finiteHeightTail]
  ring

theorem prime_product_model_log_tail_isLittleO {C a : ℝ}
    (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C) (ha : 0 < a) (ha1 : a < 1)
    (T : ℝ → ℝ) (hT : ∀ᶠ X : ℝ in atTop, (1+Real.log X)^8 ≤ T X) (ℓ : ℤ) :
    (fun X : ℝ => primeModelWindowSum (primeCutoff (4*X))
      (fun p => primeProductEnvelope (norm p/X)) ℓ (X^a) (T X) X)
        =o[atTop] firstMomentScale := by
  obtain ⟨K,hK,hbound⟩ := prime_model_log_window_sum_bound hMV hC
  apply Asymptotics.IsBigO.trans_isLittleO (g := fun X : ℝ => X^(5/6:ℝ)/(1+Real.log X)^3)
    ?_ cubic_log_saving_isLittleO
  apply Asymptotics.IsBigO.of_bound K
  filter_upwards [hT,eventually_ge_atTop (1:ℝ),
    (tendsto_rpow_atTop (show 0 < 1-a by linarith)).eventually_ge_atTop (2*Real.pi)] with X hT hX hgrow
  have hXp : 0 < X := zero_lt_one.trans_le hX
  have hcap : 2*Real.pi*X^a ≤ X := by
    apply (mul_le_mul_of_nonneg_right hgrow (Real.rpow_nonneg hXp.le a)).trans_eq
    rw [←Real.rpow_add hXp]
    have he : 1-a+a = (1:ℝ) := by ring
    rw [he,Real.rpow_one]
  have hb := hbound (primeCutoff (4*X)) (fun p => primeProductEnvelope (norm p/X))
    ℓ X X (T X) (X^a) 1 hX hXp (Real.one_le_rpow hX ha.le) hcap hT (by norm_num)
    (fun p hp => mem_primeCutoff.mp hp) (fun p _ => primeProductEnvelope_norm_le _)
  have hL : 0 ≤ 1+Real.log X := by linarith [Real.log_nonneg hX]
  rw [Real.norm_of_nonneg (by positivity)]
  simpa only [mul_one,mul_div_assoc] using hb

theorem sharp_prime_product_log_height_remainder {C ρ : ℝ}
    (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hρ : 0 < ρ) (hρ1 : ρ < 5/6) (T : ℝ → ℝ)
    (hT : ∀ᶠ X : ℝ in atTop, (1+Real.log X)^8 ≤ T X) (ℓ : ℤ) :
    (fun X : ℝ => sharpDyadicPrimeComparison ℓ X -
      ((2*Real.pi:ℝ):ℂ)⁻¹*(primeProductLowHeight ℓ (X^(1/6+ρ:ℝ)) (T X) X +
        primeProductGaussTail ℓ (X^(1/6+ρ:ℝ)) (T X) X))
      =o[atTop] firstMomentScale := by
  have hm := prime_product_model_log_tail_isLittleO hMV hC
    (show 0 < (1/6:ℝ)+ρ by linarith) (show (1/6:ℝ)+ρ < 1 by linarith) T hT ℓ
  have he := prime_sharp_interval_error_isLittleO hρ hρ1.le
    (show 0 ≤ 1+cStar by linarith [cStar_pos])
    (fun X => primeCutoff (4*X))
    (fun X p => primeProductEnvelope (norm p/X)*primeComparisonCoefficient ℓ p)
    (fun X _ p hp => mem_primeCutoff.mp hp)
    (fun X _ p hp => primeProductComparison_bound ℓ (mem_primeCutoff.mp hp).1 X)
  apply (he.sub (hm.const_mul_left (((2*Real.pi:ℝ):ℂ)⁻¹*(cStar:ℂ)))).congr'
    _ Filter.EventuallyEq.rfl
  filter_upwards [hT,eventually_gt_atTop (1:ℝ)] with X hT hX
  have hTp : 0 < T X := (pow_pos (by linarith [Real.log_pos hX]) 8).trans_le hT
  rw [sharp_prime_product_low_tail ℓ
    (Real.rpow_pos_of_pos (zero_lt_one.trans hX) _) hTp (zero_lt_one.trans hX)]
  ring

end CubicFirstMoment

end

end OAI
