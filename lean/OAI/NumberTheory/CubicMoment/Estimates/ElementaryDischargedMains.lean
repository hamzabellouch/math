import OAI.NumberTheory.CubicMoment.Angular.AngularFirstMoment
import OAI.NumberTheory.CubicMoment.Estimates.GammaInverseGrowth
import OAI.NumberTheory.CubicMoment.Estimates.GammaQuotientGrowth
import OAI.NumberTheory.CubicMoment.Estimates.CubicSupplementaryPeriodicityProof

namespace OAI

/-! Exact main statements with the elementary Gamma and periodicity inputs discharged. -/
noncomputable section
open Filter
namespace CubicFirstMoment

theorem mainResults_of_remaining_inputs
    (hpnt : PrimaryPrimePNT) (hSWRadial : KummerPrimeSiegelWalfisz)
    (hSW : AngularKummerPrimeExplicitEstimate) (hModel : FixedAngularPrimeExplicitEstimate)
    (hpubRadial : PrimitiveResidueHeckeInput) (hpub : PrimitiveAngularHeckeInput)
    (hHuxley : HuxleyAdditiveLargeSieve)
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    {v : Eisenstein → MetaplecticDualArgument → ℂ} (hVor : MetaplecticVoronoiInput v)
    {F Ψ Zf : Eisenstein → ℂ → ℂ}
    (hF : MetaplecticContinuation F) (hZf : HeathBrownZBound Zf)
    (hfac : HeathBrownZFactorization Ψ Zf) (hdiv : HeathBrownFiniteDivisor F Ψ)
    (hpart : HeathBrownGaussPartialSums) (hHB : MetaplecticMeanSquare F) :
    FirstMomentStatement ∧ AngularComparisonStatement ∧ AngularCancellationStatement := by
  have hGI (ℓ : ℤ) (m : ℕ) :
      GammaInverseFiniteOrder (1/2-(m:ℝ)+|(ℓ:ℝ)|/2) (2+|(ℓ:ℝ)|/2) :=
    gammaInverseFiniteOrder _ _
  have hGQ (ℓ : ℤ) (m : ℕ) :
      AngularGammaQuotientStripBound (|(ℓ:ℝ)|/2) (1/2-(m:ℝ)) := by
    apply angularGammaQuotientStripBound_proved
    have : 0 ≤ |(ℓ:ℝ)|/2 := by positivity
    linarith
  have hGamma (ℓ : ℤ) (σ : ℝ) (_hσ : 0 < σ) (_hσsmall : σ < 1/10000) :
      AngularGammaQuotientStripBound (metaplecticAngularShift ℓ) (-σ-1/6) := by
    apply angularGammaQuotientStripBound_proved
    linarith [metaplecticAngularShift_nonneg ℓ]
  have hTail (ℓ : ℤ) (m : ℕ) :
      AngularGammaQuotientStripBound (metaplecticAngularShift ℓ-1/6) (-((m:ℝ)-1/2)) ∧
      AngularGammaQuotientStripBound (metaplecticAngularShift ℓ+1/6) (-((m:ℝ)-1/2)) := by
    constructor <;> apply angularGammaQuotientStripBound_proved <;>
      linarith [metaplecticAngularShift_nonneg ℓ]
  have hm := angularMainResults_of_published hpnt hSWRadial hSW hModel hpubRadial hpub
    hHuxley cubicSupplementaryPeriodicity_proved hMV hC hGI hGQ hVor hGamma hTail hF hZf hfac hdiv hpart hHB
  refine ⟨?_,hm⟩
  have hc := hm.1 0
  have hp := primeModel_asymptotic_of_PNT hpnt
  apply (hc.add hp).congr' ?_ Filter.EventuallyEq.rfl
  apply Filter.Eventually.of_forall
  intro X
  dsimp only
  have he : primeComparisonCoefficient 0 = fun p => gaussAtPrime p-angularPrimeModel 0 p := by
    funext p
    simp only [primeComparisonCoefficient,angularPrimeModel,theta_zero,one_mul]
  change primeCutoffSum (primeComparisonCoefficient 0) X + _ = _
  rw [he,primeCutoffSum_sub]
  ring

end CubicFirstMoment

end

end OAI
