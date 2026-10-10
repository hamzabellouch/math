import OAI.NumberTheory.CubicMoment.Angular.AngularGaussTail
import OAI.NumberTheory.CubicMoment.Angular.AngularPrimeTailReduction
import OAI.NumberTheory.CubicMoment.Estimates.RadialFirstMoment
import OAI.NumberTheory.CubicMoment.Angular.AngularModel

namespace OAI

/-! The exact fixed nonzero angular comparison from the cited published inputs. -/
noncomputable section
open Filter
namespace CubicFirstMoment

theorem fixedAngularPrimeComparison_of_published (ℓ : ℤ) (hℓ : ℓ ≠ 0)
    (hpnt : PrimaryPrimePNT) (hSW : AngularKummerPrimeExplicitEstimate)
    (hpub : PrimitiveAngularHeckeInput) (hHuxley : HuxleyAdditiveLargeSieve)
    (hperiod : CubicSupplementaryPeriodicity)
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)+|(ℓ:ℝ)|/2) (2+|(ℓ:ℝ)|/2))
    (hGQ : ∀ m : ℕ, AngularGammaQuotientStripBound (|(ℓ:ℝ)|/2) (1/2-(m:ℝ)))
    {v : Eisenstein → MetaplecticDualArgument → ℂ} (hVor : MetaplecticVoronoiInput v)
    (hGamma0 : ∀ σ : ℝ, 0 < σ → σ < 1/10000 →
      AngularGammaQuotientStripBound (metaplecticAngularShift 0) (-σ-1/6))
    (hGammaℓ : ∀ σ : ℝ, 0 < σ → σ < 1/10000 →
      AngularGammaQuotientStripBound (metaplecticAngularShift ℓ) (-σ-1/6))
    (hGammaTail : ∀ m : ℕ,
      AngularGammaQuotientStripBound (metaplecticAngularShift ℓ-1/6) (-((m:ℝ)-1/2)) ∧
      AngularGammaQuotientStripBound (metaplecticAngularShift ℓ+1/6) (-((m:ℝ)-1/2))) :
    primeCutoffSum (primeComparisonCoefficient ℓ) =o[atTop] firstMomentScale := by
  obtain ⟨η,Ct,hη,hηsmall,hCt,htail⟩ := primeProductGaussTail_angular_isLittleO ℓ hℓ
    hpnt hpub hHuxley hperiod hMV hC hGI hGQ hVor hGammaTail
  have hr := sharpAngularPrime_sub_gaussTail_isLittleO ℓ hpnt hSW hℓ hpub hHuxley hperiod
    hMV hC hGI hGQ hVor hGamma0 hGammaℓ hη hηsmall Ct hCt
  have hd : (fun X => sharpDyadicPrimeComparison ℓ X) =o[atTop] firstMomentScale := by
    apply (hr.add (htail.const_mul_left (((2*Real.pi:ℝ):ℂ)⁻¹))).congr'
      ?_ Filter.EventuallyEq.rfl
    exact Filter.Eventually.of_forall (fun X => by dsimp; ring)
  exact angularPrimeDifference_isLittleO_of_dyadic ℓ hd

/-- Both exact angular main statements, with the zero mode supplied by the radial proof. -/
theorem angularMainResults_of_voronoi
    (hpnt : PrimaryPrimePNT) (hSWRadial : KummerPrimeSiegelWalfisz)
    (hSW : AngularKummerPrimeExplicitEstimate)
    (hModel : FixedAngularPrimeExplicitEstimate)
    (hpubRadial : PrimitiveResidueHeckeInput) (hpub : PrimitiveAngularHeckeInput)
    (hHuxley : HuxleyAdditiveLargeSieve) (hperiod : CubicSupplementaryPeriodicity)
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hGI : ∀ (ℓ : ℤ) (m : ℕ),
      GammaInverseFiniteOrder (1/2-(m:ℝ)+|(ℓ:ℝ)|/2) (2+|(ℓ:ℝ)|/2))
    (hGQ : ∀ (ℓ : ℤ) (m : ℕ),
      AngularGammaQuotientStripBound (|(ℓ:ℝ)|/2) (1/2-(m:ℝ)))
    {v : Eisenstein → MetaplecticDualArgument → ℂ} (hVor : MetaplecticVoronoiInput v)
    (hGamma : ∀ (ℓ : ℤ) (σ : ℝ), 0 < σ → σ < 1/10000 →
      AngularGammaQuotientStripBound (metaplecticAngularShift ℓ) (-σ-1/6))
    (hGammaTail : ∀ (ℓ : ℤ) (m : ℕ),
      AngularGammaQuotientStripBound (metaplecticAngularShift ℓ-1/6) (-((m:ℝ)-1/2)) ∧
      AngularGammaQuotientStripBound (metaplecticAngularShift ℓ+1/6) (-((m:ℝ)-1/2))) :
    AngularComparisonStatement ∧ AngularCancellationStatement := by
  have hcomparison : AngularComparisonStatement := by
    intro ℓ
    by_cases hℓ : ℓ = 0
    · subst ℓ
      have hGI0 (m : ℕ) : GammaInverseFiniteOrder (1/2-(m:ℝ)) 2 := by
        simpa only [Int.cast_zero, abs_zero, zero_div, add_zero] using hGI 0 m
      have hGQ0 (m : ℕ) : GammaQuotientStripBound (1/2-(m:ℝ)) := by
        simpa only [Int.cast_zero, abs_zero, zero_div, AngularGammaQuotientStripBound,
          GammaQuotientStripBound, angularGammaFEQuotient, gammaFEQuotient,
          Complex.ofReal_zero, add_zero] using hGQ 0 m
      exact radialPrimeComparison_of_voronoi hpnt hSWRadial hpubRadial hHuxley hperiod
        hMV hC hGI0 hGQ0 hVor (hGamma 0)
    · exact fixedAngularPrimeComparison_of_published ℓ hℓ hpnt hSW hpub hHuxley hperiod
        hMV hC (hGI ℓ) (hGQ ℓ) hVor (hGamma 0) (hGamma ℓ) (hGammaTail ℓ)
  exact ⟨hcomparison, angularCancellation_of_comparison hcomparison
    (angularPrimeModel_isLittleO hModel)⟩

theorem angularMainResults_of_polynomial
    (hpnt : PrimaryPrimePNT) (hSWRadial : KummerPrimeSiegelWalfisz)
    (hSW : AngularKummerPrimeExplicitEstimate)
    (hModel : FixedAngularPrimeExplicitEstimate)
    (hpubRadial : PrimitiveResidueHeckeInput) (hpub : PrimitiveAngularHeckeInput)
    (hHuxley : HuxleyAdditiveLargeSieve) (hperiod : CubicSupplementaryPeriodicity)
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hGI : ∀ (ℓ : ℤ) (m : ℕ),
      GammaInverseFiniteOrder (1/2-(m:ℝ)+|(ℓ:ℝ)|/2) (2+|(ℓ:ℝ)|/2))
    (hGQ : ∀ (ℓ : ℤ) (m : ℕ),
      AngularGammaQuotientStripBound (|(ℓ:ℝ)|/2) (1/2-(m:ℝ)))
    {v : Eisenstein → MetaplecticDualArgument → ℂ} (hVor : MetaplecticVoronoiInput v)
    (hGamma : ∀ (ℓ : ℤ) (σ : ℝ), 0 < σ → σ < 1/10000 →
      AngularGammaQuotientStripBound (metaplecticAngularShift ℓ) (-σ-1/6))
    (hGammaTail : ∀ (ℓ : ℤ) (m : ℕ),
      AngularGammaQuotientStripBound (metaplecticAngularShift ℓ-1/6) (-((m:ℝ)-1/2)) ∧
      AngularGammaQuotientStripBound (metaplecticAngularShift ℓ+1/6) (-((m:ℝ)-1/2)))
    {F : Eisenstein → ℂ → ℂ}
    (_hF : MetaplecticContinuation F) (_hGrowth : MetaplecticPolynomialGrowth F) (_hHB : MetaplecticMeanSquare F) :
    AngularComparisonStatement ∧ AngularCancellationStatement :=
  angularMainResults_of_voronoi hpnt hSWRadial hSW hModel hpubRadial hpub hHuxley hperiod hMV hC hGI hGQ hVor hGamma hGammaTail

theorem angularComparison_of_voronoi
    (hpnt : PrimaryPrimePNT) (hSWRadial : KummerPrimeSiegelWalfisz)
    (hSW : AngularKummerPrimeExplicitEstimate)
    (hModel : FixedAngularPrimeExplicitEstimate)
    (hpubRadial : PrimitiveResidueHeckeInput) (hpub : PrimitiveAngularHeckeInput)
    (hHuxley : HuxleyAdditiveLargeSieve) (hperiod : CubicSupplementaryPeriodicity)
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hGI : ∀ (ℓ : ℤ) (m : ℕ),
      GammaInverseFiniteOrder (1/2-(m:ℝ)+|(ℓ:ℝ)|/2) (2+|(ℓ:ℝ)|/2))
    (hGQ : ∀ (ℓ : ℤ) (m : ℕ),
      AngularGammaQuotientStripBound (|(ℓ:ℝ)|/2) (1/2-(m:ℝ)))
    {v : Eisenstein → MetaplecticDualArgument → ℂ} (hVor : MetaplecticVoronoiInput v)
    (hGamma : ∀ (ℓ : ℤ) (σ : ℝ), 0 < σ → σ < 1/10000 →
      AngularGammaQuotientStripBound (metaplecticAngularShift ℓ) (-σ-1/6))
    (hGammaTail : ∀ (ℓ : ℤ) (m : ℕ),
      AngularGammaQuotientStripBound (metaplecticAngularShift ℓ-1/6) (-((m:ℝ)-1/2)) ∧
      AngularGammaQuotientStripBound (metaplecticAngularShift ℓ+1/6) (-((m:ℝ)-1/2))) : AngularComparisonStatement :=
  (angularMainResults_of_voronoi hpnt hSWRadial hSW hModel hpubRadial hpub hHuxley hperiod hMV hC hGI hGQ hVor hGamma hGammaTail).1

theorem angularComparison_of_polynomial
    (hpnt : PrimaryPrimePNT) (hSWRadial : KummerPrimeSiegelWalfisz)
    (hSW : AngularKummerPrimeExplicitEstimate)
    (hModel : FixedAngularPrimeExplicitEstimate)
    (hpubRadial : PrimitiveResidueHeckeInput) (hpub : PrimitiveAngularHeckeInput)
    (hHuxley : HuxleyAdditiveLargeSieve) (hperiod : CubicSupplementaryPeriodicity)
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hGI : ∀ (ℓ : ℤ) (m : ℕ),
      GammaInverseFiniteOrder (1/2-(m:ℝ)+|(ℓ:ℝ)|/2) (2+|(ℓ:ℝ)|/2))
    (hGQ : ∀ (ℓ : ℤ) (m : ℕ),
      AngularGammaQuotientStripBound (|(ℓ:ℝ)|/2) (1/2-(m:ℝ)))
    {v : Eisenstein → MetaplecticDualArgument → ℂ} (hVor : MetaplecticVoronoiInput v)
    (hGamma : ∀ (ℓ : ℤ) (σ : ℝ), 0 < σ → σ < 1/10000 →
      AngularGammaQuotientStripBound (metaplecticAngularShift ℓ) (-σ-1/6))
    (hGammaTail : ∀ (ℓ : ℤ) (m : ℕ),
      AngularGammaQuotientStripBound (metaplecticAngularShift ℓ-1/6) (-((m:ℝ)-1/2)) ∧
      AngularGammaQuotientStripBound (metaplecticAngularShift ℓ+1/6) (-((m:ℝ)-1/2)))
    {F : Eisenstein → ℂ → ℂ}
    (_hF : MetaplecticContinuation F) (_hGrowth : MetaplecticPolynomialGrowth F) (_hHB : MetaplecticMeanSquare F) : AngularComparisonStatement :=
  angularComparison_of_voronoi hpnt hSWRadial hSW hModel hpubRadial hpub hHuxley hperiod hMV hC hGI hGQ hVor hGamma hGammaTail

theorem angularCancellation_of_voronoi
    (hpnt : PrimaryPrimePNT) (hSWRadial : KummerPrimeSiegelWalfisz)
    (hSW : AngularKummerPrimeExplicitEstimate)
    (hModel : FixedAngularPrimeExplicitEstimate)
    (hpubRadial : PrimitiveResidueHeckeInput) (hpub : PrimitiveAngularHeckeInput)
    (hHuxley : HuxleyAdditiveLargeSieve) (hperiod : CubicSupplementaryPeriodicity)
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hGI : ∀ (ℓ : ℤ) (m : ℕ),
      GammaInverseFiniteOrder (1/2-(m:ℝ)+|(ℓ:ℝ)|/2) (2+|(ℓ:ℝ)|/2))
    (hGQ : ∀ (ℓ : ℤ) (m : ℕ),
      AngularGammaQuotientStripBound (|(ℓ:ℝ)|/2) (1/2-(m:ℝ)))
    {v : Eisenstein → MetaplecticDualArgument → ℂ} (hVor : MetaplecticVoronoiInput v)
    (hGamma : ∀ (ℓ : ℤ) (σ : ℝ), 0 < σ → σ < 1/10000 →
      AngularGammaQuotientStripBound (metaplecticAngularShift ℓ) (-σ-1/6))
    (hGammaTail : ∀ (ℓ : ℤ) (m : ℕ),
      AngularGammaQuotientStripBound (metaplecticAngularShift ℓ-1/6) (-((m:ℝ)-1/2)) ∧
      AngularGammaQuotientStripBound (metaplecticAngularShift ℓ+1/6) (-((m:ℝ)-1/2))) : AngularCancellationStatement :=
  (angularMainResults_of_voronoi hpnt hSWRadial hSW hModel hpubRadial hpub hHuxley hperiod hMV hC hGI hGQ hVor hGamma hGammaTail).2

theorem angularCancellation_of_polynomial
    (hpnt : PrimaryPrimePNT) (hSWRadial : KummerPrimeSiegelWalfisz)
    (hSW : AngularKummerPrimeExplicitEstimate)
    (hModel : FixedAngularPrimeExplicitEstimate)
    (hpubRadial : PrimitiveResidueHeckeInput) (hpub : PrimitiveAngularHeckeInput)
    (hHuxley : HuxleyAdditiveLargeSieve) (hperiod : CubicSupplementaryPeriodicity)
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hGI : ∀ (ℓ : ℤ) (m : ℕ),
      GammaInverseFiniteOrder (1/2-(m:ℝ)+|(ℓ:ℝ)|/2) (2+|(ℓ:ℝ)|/2))
    (hGQ : ∀ (ℓ : ℤ) (m : ℕ),
      AngularGammaQuotientStripBound (|(ℓ:ℝ)|/2) (1/2-(m:ℝ)))
    {v : Eisenstein → MetaplecticDualArgument → ℂ} (hVor : MetaplecticVoronoiInput v)
    (hGamma : ∀ (ℓ : ℤ) (σ : ℝ), 0 < σ → σ < 1/10000 →
      AngularGammaQuotientStripBound (metaplecticAngularShift ℓ) (-σ-1/6))
    (hGammaTail : ∀ (ℓ : ℤ) (m : ℕ),
      AngularGammaQuotientStripBound (metaplecticAngularShift ℓ-1/6) (-((m:ℝ)-1/2)) ∧
      AngularGammaQuotientStripBound (metaplecticAngularShift ℓ+1/6) (-((m:ℝ)-1/2)))
    {F : Eisenstein → ℂ → ℂ}
    (_hF : MetaplecticContinuation F) (_hGrowth : MetaplecticPolynomialGrowth F) (_hHB : MetaplecticMeanSquare F) : AngularCancellationStatement :=
  angularCancellation_of_voronoi hpnt hSWRadial hSW hModel hpubRadial hpub hHuxley hperiod hMV hC hGI hGQ hVor hGamma hGammaTail

theorem angularMainResults_of_published
    (hpnt : PrimaryPrimePNT) (hSWRadial : KummerPrimeSiegelWalfisz)
    (hSW : AngularKummerPrimeExplicitEstimate)
    (hModel : FixedAngularPrimeExplicitEstimate)
    (hpubRadial : PrimitiveResidueHeckeInput) (hpub : PrimitiveAngularHeckeInput)
    (hHuxley : HuxleyAdditiveLargeSieve) (hperiod : CubicSupplementaryPeriodicity)
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hGI : ∀ (ℓ : ℤ) (m : ℕ),
      GammaInverseFiniteOrder (1/2-(m:ℝ)+|(ℓ:ℝ)|/2) (2+|(ℓ:ℝ)|/2))
    (hGQ : ∀ (ℓ : ℤ) (m : ℕ),
      AngularGammaQuotientStripBound (|(ℓ:ℝ)|/2) (1/2-(m:ℝ)))
    {v : Eisenstein → MetaplecticDualArgument → ℂ} (hVor : MetaplecticVoronoiInput v)
    (hGamma : ∀ (ℓ : ℤ) (σ : ℝ), 0 < σ → σ < 1/10000 →
      AngularGammaQuotientStripBound (metaplecticAngularShift ℓ) (-σ-1/6))
    (hGammaTail : ∀ (ℓ : ℤ) (m : ℕ),
      AngularGammaQuotientStripBound (metaplecticAngularShift ℓ-1/6) (-((m:ℝ)-1/2)) ∧
      AngularGammaQuotientStripBound (metaplecticAngularShift ℓ+1/6) (-((m:ℝ)-1/2)))
    {F Ψ Zf : Eisenstein → ℂ → ℂ}
    (hF : MetaplecticContinuation F) (hZf : HeathBrownZBound Zf)
    (hfac : HeathBrownZFactorization Ψ Zf) (hdiv : HeathBrownFiniteDivisor F Ψ)
    (hpart : HeathBrownGaussPartialSums) (hHB : MetaplecticMeanSquare F) :
    AngularComparisonStatement ∧ AngularCancellationStatement :=
  angularMainResults_of_polynomial hpnt hSWRadial hSW hModel hpubRadial hpub
    hHuxley hperiod hMV hC hGI hGQ hVor hGamma hGammaTail hF
    (metaplectic_polynomial_growth_of_published hF hZf hfac hdiv hpart) hHB

theorem angularComparison_of_published
    (hpnt : PrimaryPrimePNT) (hSWRadial : KummerPrimeSiegelWalfisz)
    (hSW : AngularKummerPrimeExplicitEstimate)
    (hModel : FixedAngularPrimeExplicitEstimate)
    (hpubRadial : PrimitiveResidueHeckeInput) (hpub : PrimitiveAngularHeckeInput)
    (hHuxley : HuxleyAdditiveLargeSieve) (hperiod : CubicSupplementaryPeriodicity)
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hGI : ∀ (ℓ : ℤ) (m : ℕ),
      GammaInverseFiniteOrder (1/2-(m:ℝ)+|(ℓ:ℝ)|/2) (2+|(ℓ:ℝ)|/2))
    (hGQ : ∀ (ℓ : ℤ) (m : ℕ),
      AngularGammaQuotientStripBound (|(ℓ:ℝ)|/2) (1/2-(m:ℝ)))
    {v : Eisenstein → MetaplecticDualArgument → ℂ} (hVor : MetaplecticVoronoiInput v)
    (hGamma : ∀ (ℓ : ℤ) (σ : ℝ), 0 < σ → σ < 1/10000 →
      AngularGammaQuotientStripBound (metaplecticAngularShift ℓ) (-σ-1/6))
    (hGammaTail : ∀ (ℓ : ℤ) (m : ℕ),
      AngularGammaQuotientStripBound (metaplecticAngularShift ℓ-1/6) (-((m:ℝ)-1/2)) ∧
      AngularGammaQuotientStripBound (metaplecticAngularShift ℓ+1/6) (-((m:ℝ)-1/2)))
    {F Ψ Zf : Eisenstein → ℂ → ℂ}
    (hF : MetaplecticContinuation F) (hZf : HeathBrownZBound Zf)
    (hfac : HeathBrownZFactorization Ψ Zf) (hdiv : HeathBrownFiniteDivisor F Ψ)
    (hpart : HeathBrownGaussPartialSums) (hHB : MetaplecticMeanSquare F) : AngularComparisonStatement :=
  angularComparison_of_polynomial hpnt hSWRadial hSW hModel hpubRadial hpub
    hHuxley hperiod hMV hC hGI hGQ hVor hGamma hGammaTail hF
    (metaplectic_polynomial_growth_of_published hF hZf hfac hdiv hpart) hHB

theorem angularCancellation_of_published
    (hpnt : PrimaryPrimePNT) (hSWRadial : KummerPrimeSiegelWalfisz)
    (hSW : AngularKummerPrimeExplicitEstimate)
    (hModel : FixedAngularPrimeExplicitEstimate)
    (hpubRadial : PrimitiveResidueHeckeInput) (hpub : PrimitiveAngularHeckeInput)
    (hHuxley : HuxleyAdditiveLargeSieve) (hperiod : CubicSupplementaryPeriodicity)
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hGI : ∀ (ℓ : ℤ) (m : ℕ),
      GammaInverseFiniteOrder (1/2-(m:ℝ)+|(ℓ:ℝ)|/2) (2+|(ℓ:ℝ)|/2))
    (hGQ : ∀ (ℓ : ℤ) (m : ℕ),
      AngularGammaQuotientStripBound (|(ℓ:ℝ)|/2) (1/2-(m:ℝ)))
    {v : Eisenstein → MetaplecticDualArgument → ℂ} (hVor : MetaplecticVoronoiInput v)
    (hGamma : ∀ (ℓ : ℤ) (σ : ℝ), 0 < σ → σ < 1/10000 →
      AngularGammaQuotientStripBound (metaplecticAngularShift ℓ) (-σ-1/6))
    (hGammaTail : ∀ (ℓ : ℤ) (m : ℕ),
      AngularGammaQuotientStripBound (metaplecticAngularShift ℓ-1/6) (-((m:ℝ)-1/2)) ∧
      AngularGammaQuotientStripBound (metaplecticAngularShift ℓ+1/6) (-((m:ℝ)-1/2)))
    {F Ψ Zf : Eisenstein → ℂ → ℂ}
    (hF : MetaplecticContinuation F) (hZf : HeathBrownZBound Zf)
    (hfac : HeathBrownZFactorization Ψ Zf) (hdiv : HeathBrownFiniteDivisor F Ψ)
    (hpart : HeathBrownGaussPartialSums) (hHB : MetaplecticMeanSquare F) : AngularCancellationStatement :=
  angularCancellation_of_polynomial hpnt hSWRadial hSW hModel hpubRadial hpub
    hHuxley hperiod hMV hC hGI hGQ hVor hGamma hGammaTail hF
    (metaplectic_polynomial_growth_of_published hF hZf hfac hdiv hpart) hHB

end CubicFirstMoment

end

end OAI
