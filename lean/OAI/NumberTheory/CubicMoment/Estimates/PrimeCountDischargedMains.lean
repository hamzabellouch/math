import OAI.NumberTheory.CubicMoment.Estimates.MeanValueDischargedMains
import OAI.NumberTheory.CubicMoment.Estimates.PrimaryPrimePNTProof

namespace OAI

/-! Exact main statements with elementary inputs, mean value and prime counting proved. -/
noncomputable section
namespace CubicFirstMoment

theorem mainResults_of_remaining_analytic_inputs
    (hSWRadial : KummerPrimeSiegelWalfisz)
    (hSW : AngularKummerPrimeExplicitEstimate) (hModel : FixedAngularPrimeExplicitEstimate)
    (hpubRadial : PrimitiveResidueHeckeInput) (hpub : PrimitiveAngularHeckeInput)
    (hHuxley : HuxleyAdditiveLargeSieve)
    {v : Eisenstein → MetaplecticDualArgument → ℂ} (hVor : MetaplecticVoronoiInput v)
    {F Ψ Zf : Eisenstein → ℂ → ℂ}
    (hF : MetaplecticContinuation F) (hZf : HeathBrownZBound Zf)
    (hfac : HeathBrownZFactorization Ψ Zf) (hdiv : HeathBrownFiniteDivisor F Ψ)
    (hpart : HeathBrownGaussPartialSums) (hHB : MetaplecticMeanSquare F) :
    FirstMomentStatement ∧ AngularComparisonStatement ∧ AngularCancellationStatement :=
  mainResults_of_character_and_metaplectic_inputs primaryPrimePNT_proved
    hSWRadial hSW hModel hpubRadial hpub hHuxley hVor hF hZf hfac hdiv hpart hHB

end CubicFirstMoment

end

end OAI
