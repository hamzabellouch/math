import OAI.NumberTheory.CubicMoment.Angular.AngularScaleFirstCentralNegligible

namespace OAI

/-! The sharp fixed-angular prime comparison is reduced to its literal Gauss
height tail. The entire low-height contribution has been discharged. -/
noncomputable section
open Filter
namespace CubicFirstMoment
variable (ℓ : ℤ)

theorem sharpAngularPrime_sub_gaussTail_isLittleO
    (hpnt : PrimaryPrimePNT) (hSW : AngularKummerPrimeExplicitEstimate) (hℓ : ℓ ≠ 0)
    (hpub : PrimitiveAngularHeckeInput) (hHuxley : HuxleyAdditiveLargeSieve)
    (hperiod : CubicSupplementaryPeriodicity)
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)+|(ℓ:ℝ)|/2) (2+|(ℓ:ℝ)|/2))
    (hGQ : ∀ m : ℕ, AngularGammaQuotientStripBound (|(ℓ:ℝ)|/2) (1/2-(m:ℝ)))
    {v : Eisenstein → MetaplecticDualArgument → ℂ} (hVor : MetaplecticVoronoiInput v)
    (hGamma : ∀ σ : ℝ, 0 < σ → σ < 1/10000 →
      AngularGammaQuotientStripBound (metaplecticAngularShift 0) (-σ-1/6))
    (hGammaℓ : ∀ σ : ℝ, 0 < σ → σ < 1/10000 →
      AngularGammaQuotientStripBound (metaplecticAngularShift ℓ) (-σ-1/6))
    {η : ℝ} (hη : 0 < η) (hη1 : η < 5/6) (Ct : ℕ) (hCt : 8 ≤ Ct) :
    (fun X => sharpDyadicPrimeComparison ℓ X-
      ((2*Real.pi:ℝ):ℂ)⁻¹*primeProductGaussTail ℓ (X^(1/6+η:ℝ))
        ((1+Real.log X)^Ct) X) =o[atTop] firstMomentScale := by
  have hH : ∀ᶠ X : ℝ in atTop, 0 < X^(1/6+η:ℝ) := by
    filter_upwards [eventually_gt_atTop (0:ℝ)] with X hX
    exact Real.rpow_pos_of_pos hX _
  have hT : ∀ᶠ X : ℝ in atTop, (1+Real.log X)^8 ≤ (1+Real.log X)^Ct := by
    filter_upwards [eventually_ge_atTop (1:ℝ)] with X hX
    exact pow_le_pow_right₀ (by linarith [Real.log_nonneg hX]) hCt
  have hl := primeProductLowHeight_angular_isLittleO ℓ (ξ := 1/1000)
    hpnt hSW hℓ hpub hHuxley hperiod hMV hC (by norm_num) (by norm_num)
    hGI hGQ hVor hGamma hGammaℓ Ct (fun X => X^(1/6+η:ℝ)) hH
  have hr := sharp_prime_product_log_height_remainder hMV hC hη hη1
    (fun X => (1+Real.log X)^Ct) hT ℓ
  apply (hr.add (hl.const_mul_left (((2*Real.pi:ℝ):ℂ)⁻¹))).congr'
    ?_ Filter.EventuallyEq.rfl
  exact Filter.Eventually.of_forall (fun X => by dsimp; ring)

end CubicFirstMoment

end

end OAI
