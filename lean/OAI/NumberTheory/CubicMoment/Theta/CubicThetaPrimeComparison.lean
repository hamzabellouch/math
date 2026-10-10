import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCentralScaleFirstCentralNegligible
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCentralAngularScaleFirstCentralNegligible
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaActualGaussTails

namespace OAI

/-! The centered prime comparison from the constructed arithmetic theta
transform, the actual low-height bounds and the actual high-height tails.
No published analytic input is retained as a hypothesis. -/
noncomputable section
open Filter Asymptotics
namespace CubicFirstMoment

lemma cubicTheta_primeProductLowHeight_isLittleO (ℓ : ℤ) (Ct : ℕ)
    (H : ℝ → ℝ) (hH : ∀ᶠ X : ℝ in atTop,0<H X) :
    (fun X => primeProductLowHeight ℓ (H X) ((1+Real.log X)^Ct) X)
      =o[atTop] firstMomentScale := by
  have hGI (m : ℕ) : GammaInverseFiniteOrder (1/2-(m:ℝ)+|(ℓ:ℝ)|/2) (2+|(ℓ:ℝ)|/2) :=
    gammaInverseFiniteOrder _ _
  have hGQ (m : ℕ) : AngularGammaQuotientStripBound (|(ℓ:ℝ)|/2) (1/2-(m:ℝ)) := by
    apply angularGammaQuotientStripBound_proved
    have hp : 0≤|(ℓ:ℝ)|/2 := by positivity
    linarith
  have hGamma (k : ℤ) (σ : ℝ) (_hσ : 0<σ) (_hs : σ<1/10000) :
      AngularGammaQuotientStripBound (metaplecticAngularShift k) (-σ-1/6) := by
    apply angularGammaQuotientStripBound_proved
    linarith [metaplecticAngularShift_nonneg k]
  by_cases hℓ : ℓ=0
  · subst ℓ
    have hGI0 (m : ℕ) : GammaInverseFiniteOrder (1/2-(m:ℝ)) 2 := by
      simpa only [Int.cast_zero,abs_zero,zero_div,add_zero] using hGI m
    have hGQ0 (m : ℕ) : GammaQuotientStripBound (1/2-(m:ℝ)) := by
      simpa only [Int.cast_zero,abs_zero,zero_div,AngularGammaQuotientStripBound,
        GammaQuotientStripBound,angularGammaFEQuotient,gammaFEQuotient,
        Complex.ofReal_zero,add_zero] using hGQ m
    exact primeProductLowHeight_radial_isLittleO_actual (ξ:=1/1000)
      primaryPrimePNT_proved (kummerPrimeSiegelWalfisz_of_primitive primitiveResidueHeckeInput_proved)
      primitiveResidueHeckeInput_proved huxleyAdditiveLargeSieve_proved
      cubicSupplementaryPeriodicity_proved montgomeryVaughanBound_proved
      ordinaryMeanValueConstant_pos.le (by norm_num) (by norm_num) hGI0 hGQ0 (hGamma 0) Ct H hH
  · exact primeProductLowHeight_angular_isLittleO_actual ℓ (ξ:=1/1000)
      primaryPrimePNT_proved (angularKummerPrimeExplicitEstimate_of_primitive primitiveAngularHeckeInput_proved)
      hℓ primitiveAngularHeckeInput_proved huxleyAdditiveLargeSieve_proved
      cubicSupplementaryPeriodicity_proved montgomeryVaughanBound_proved
      ordinaryMeanValueConstant_pos.le (by norm_num) (by norm_num) hGI hGQ
      (hGamma 0) (hGamma ℓ) Ct H hH

lemma cubicTheta_primeComparison (ℓ : ℤ) :
    primeCutoffSum (primeComparisonCoefficient ℓ)=o[atTop] firstMomentScale := by
  obtain ⟨η,Ct,hη,hηsmall,hCt,htail⟩ := cubicTheta_primeProductGaussTail_isLittleO ℓ
  have hH : ∀ᶠ X : ℝ in atTop,0<X^(1/6+η:ℝ) := by
    filter_upwards [eventually_gt_atTop (0:ℝ)] with X hX
    exact Real.rpow_pos_of_pos hX _
  have hT : ∀ᶠ X : ℝ in atTop,(1+Real.log X)^8≤(1+Real.log X)^Ct := by
    filter_upwards [eventually_ge_atTop (1:ℝ)] with X hX
    exact pow_le_pow_right₀ (by linarith [Real.log_nonneg hX]) hCt
  have hl := cubicTheta_primeProductLowHeight_isLittleO ℓ Ct (fun X => X^(1/6+η:ℝ)) hH
  have hr := sharp_prime_product_log_height_remainder montgomeryVaughanBound_proved
    ordinaryMeanValueConstant_pos.le hη hηsmall (fun X => (1+Real.log X)^Ct) hT ℓ
  have hred : (fun X => sharpDyadicPrimeComparison ℓ X-
      ((2*Real.pi:ℝ):ℂ)⁻¹*primeProductGaussTail ℓ (X^(1/6+η:ℝ))
        ((1+Real.log X)^Ct) X)=o[atTop] firstMomentScale := by
    apply (hr.add (hl.const_mul_left (((2*Real.pi:ℝ):ℂ)⁻¹))).congr' ?_ Filter.EventuallyEq.rfl
    exact Filter.Eventually.of_forall (fun X => by dsimp; ring)
  have hd : (fun X => sharpDyadicPrimeComparison ℓ X)=o[atTop] firstMomentScale := by
    apply (hred.add (htail.const_mul_left (((2*Real.pi:ℝ):ℂ)⁻¹))).congr' ?_ Filter.EventuallyEq.rfl
    exact Filter.Eventually.of_forall (fun X => by dsimp; ring)
  exact angularPrimeDifference_isLittleO_of_dyadic ℓ hd

end CubicFirstMoment

end

end OAI
