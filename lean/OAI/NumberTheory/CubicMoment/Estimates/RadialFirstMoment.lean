import OAI.NumberTheory.CubicMoment.Estimates.RadialGaussTail
import OAI.NumberTheory.CubicMoment.Estimates.RadialPrimeTailReduction
import OAI.NumberTheory.CubicMoment.Estimates.PrimeDyadicComparison
import OAI.NumberTheory.CubicMoment.Estimates.ModelPartialSummation

namespace OAI

/-! Patterson's exact radial first moment, conditionally on the precisely
cited published inputs used by the analytic modules. -/
noncomputable section
open Filter
namespace CubicFirstMoment

theorem radialPrimeComparison_of_voronoi
    (hpnt : PrimaryPrimePNT) (hSW : KummerPrimeSiegelWalfisz)
    (hpub : PrimitiveResidueHeckeInput) (hHuxley : HuxleyAdditiveLargeSieve)
    (hperiod : CubicSupplementaryPeriodicity)
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)) 2)
    (hGQ : ∀ m : ℕ, GammaQuotientStripBound (1/2-(m:ℝ)))
    {v : Eisenstein → MetaplecticDualArgument → ℂ} (hVor : MetaplecticVoronoiInput v)
    (hGamma : ∀ σ : ℝ, 0 < σ → σ < 1/10000 →
      AngularGammaQuotientStripBound (metaplecticAngularShift 0) (-σ-1/6)) :
    primeCutoffSum (primeComparisonCoefficient 0) =o[atTop] firstMomentScale := by
  obtain ⟨η,Ct,hη,hηsmall,hCt,htail⟩ := primeProductGaussTail_radial_isLittleO
    hpnt hpub hHuxley hperiod hMV hC hGI hGQ hVor
  have hr := sharpRadialPrime_sub_gaussTail_isLittleO hpnt hSW hpub hHuxley hperiod
    hMV hC hGI hGQ hVor hGamma hη hηsmall Ct hCt
  have hd : (fun X => sharpDyadicPrimeComparison 0 X) =o[atTop] firstMomentScale := by
    apply (hr.add (htail.const_mul_left (((2*Real.pi:ℝ):ℂ)⁻¹))).congr'
      ?_ Filter.EventuallyEq.rfl
    exact Filter.Eventually.of_forall (fun X => by dsimp; ring)
  exact angularPrimeDifference_isLittleO_of_dyadic 0 hd

theorem radialPrimeComparison_of_polynomial
    (hpnt : PrimaryPrimePNT) (hSW : KummerPrimeSiegelWalfisz)
    (hpub : PrimitiveResidueHeckeInput) (hHuxley : HuxleyAdditiveLargeSieve)
    (hperiod : CubicSupplementaryPeriodicity)
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)) 2)
    (hGQ : ∀ m : ℕ, GammaQuotientStripBound (1/2-(m:ℝ)))
    {v : Eisenstein → MetaplecticDualArgument → ℂ} (hVor : MetaplecticVoronoiInput v)
    (hGamma : ∀ σ : ℝ, 0 < σ → σ < 1/10000 →
      AngularGammaQuotientStripBound (metaplecticAngularShift 0) (-σ-1/6))
    {F : Eisenstein → ℂ → ℂ}
    (_hF : MetaplecticContinuation F) (_hGrowth : MetaplecticPolynomialGrowth F) (_hHB : MetaplecticMeanSquare F) :
    primeCutoffSum (primeComparisonCoefficient 0) =o[atTop] firstMomentScale :=
  radialPrimeComparison_of_voronoi hpnt hSW hpub hHuxley hperiod hMV hC hGI hGQ hVor hGamma

theorem firstMoment_of_voronoi
    (hpnt : PrimaryPrimePNT) (hSW : KummerPrimeSiegelWalfisz)
    (hpub : PrimitiveResidueHeckeInput) (hHuxley : HuxleyAdditiveLargeSieve)
    (hperiod : CubicSupplementaryPeriodicity)
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)) 2)
    (hGQ : ∀ m : ℕ, GammaQuotientStripBound (1/2-(m:ℝ)))
    {v : Eisenstein → MetaplecticDualArgument → ℂ} (hVor : MetaplecticVoronoiInput v)
    (hGamma : ∀ σ : ℝ, 0 < σ → σ < 1/10000 →
      AngularGammaQuotientStripBound (metaplecticAngularShift 0) (-σ-1/6)) :
    FirstMomentStatement := by
  have hc := radialPrimeComparison_of_voronoi hpnt hSW hpub hHuxley hperiod
    hMV hC hGI hGQ hVor hGamma
  have hm := primeModel_asymptotic_of_PNT hpnt
  apply (hc.add hm).congr' ?_ Filter.EventuallyEq.rfl
  apply Filter.Eventually.of_forall
  intro X
  dsimp only
  have he : primeComparisonCoefficient 0 = fun p => gaussAtPrime p - angularPrimeModel 0 p := by
    funext p
    simp only [primeComparisonCoefficient,angularPrimeModel,theta_zero,one_mul]
  rw [he,primeCutoffSum_sub]
  ring

theorem firstMoment_of_polynomial
    (hpnt : PrimaryPrimePNT) (hSW : KummerPrimeSiegelWalfisz)
    (hpub : PrimitiveResidueHeckeInput) (hHuxley : HuxleyAdditiveLargeSieve)
    (hperiod : CubicSupplementaryPeriodicity)
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)) 2)
    (hGQ : ∀ m : ℕ, GammaQuotientStripBound (1/2-(m:ℝ)))
    {v : Eisenstein → MetaplecticDualArgument → ℂ} (hVor : MetaplecticVoronoiInput v)
    (hGamma : ∀ σ : ℝ, 0 < σ → σ < 1/10000 →
      AngularGammaQuotientStripBound (metaplecticAngularShift 0) (-σ-1/6))
    {F : Eisenstein → ℂ → ℂ}
    (_hF : MetaplecticContinuation F) (_hGrowth : MetaplecticPolynomialGrowth F) (_hHB : MetaplecticMeanSquare F) :
    FirstMomentStatement :=
  firstMoment_of_voronoi hpnt hSW hpub hHuxley hperiod hMV hC hGI hGQ hVor hGamma

theorem radialPrimeComparison_of_published
    (hpnt : PrimaryPrimePNT) (hSW : KummerPrimeSiegelWalfisz)
    (hpub : PrimitiveResidueHeckeInput) (hHuxley : HuxleyAdditiveLargeSieve)
    (hperiod : CubicSupplementaryPeriodicity)
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)) 2)
    (hGQ : ∀ m : ℕ, GammaQuotientStripBound (1/2-(m:ℝ)))
    {v : Eisenstein → MetaplecticDualArgument → ℂ} (hVor : MetaplecticVoronoiInput v)
    (hGamma : ∀ σ : ℝ, 0 < σ → σ < 1/10000 →
      AngularGammaQuotientStripBound (metaplecticAngularShift 0) (-σ-1/6))
    {F Ψ Zf : Eisenstein → ℂ → ℂ}
    (hF : MetaplecticContinuation F) (hZf : HeathBrownZBound Zf)
    (hfac : HeathBrownZFactorization Ψ Zf) (hdiv : HeathBrownFiniteDivisor F Ψ)
    (hpart : HeathBrownGaussPartialSums) (hHB : MetaplecticMeanSquare F) :
    primeCutoffSum (primeComparisonCoefficient 0) =o[atTop] firstMomentScale :=
  radialPrimeComparison_of_polynomial hpnt hSW hpub hHuxley hperiod
    hMV hC hGI hGQ hVor hGamma hF
    (metaplectic_polynomial_growth_of_published hF hZf hfac hdiv hpart) hHB

theorem firstMoment_of_published
    (hpnt : PrimaryPrimePNT) (hSW : KummerPrimeSiegelWalfisz)
    (hpub : PrimitiveResidueHeckeInput) (hHuxley : HuxleyAdditiveLargeSieve)
    (hperiod : CubicSupplementaryPeriodicity)
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)) 2)
    (hGQ : ∀ m : ℕ, GammaQuotientStripBound (1/2-(m:ℝ)))
    {v : Eisenstein → MetaplecticDualArgument → ℂ} (hVor : MetaplecticVoronoiInput v)
    (hGamma : ∀ σ : ℝ, 0 < σ → σ < 1/10000 →
      AngularGammaQuotientStripBound (metaplecticAngularShift 0) (-σ-1/6))
    {F Ψ Zf : Eisenstein → ℂ → ℂ}
    (hF : MetaplecticContinuation F) (hZf : HeathBrownZBound Zf)
    (hfac : HeathBrownZFactorization Ψ Zf) (hdiv : HeathBrownFiniteDivisor F Ψ)
    (hpart : HeathBrownGaussPartialSums) (hHB : MetaplecticMeanSquare F) :
    FirstMomentStatement :=
  firstMoment_of_polynomial hpnt hSW hpub hHuxley hperiod
    hMV hC hGI hGQ hVor hGamma hF
    (metaplectic_polynomial_growth_of_published hF hZf hfac hdiv hpart) hHB

end CubicFirstMoment

end

end OAI
