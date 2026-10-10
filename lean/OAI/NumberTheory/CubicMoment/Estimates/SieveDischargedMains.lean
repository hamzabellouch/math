import OAI.NumberTheory.CubicMoment.Estimates.PrimeCountDischargedMains
import OAI.NumberTheory.CubicMoment.Estimates.HuxleyProof

namespace OAI

/-! Exact main statements with the additive large sieve also proved. -/
noncomputable section
namespace CubicFirstMoment

theorem mainResults_of_hecke_and_metaplectic_inputs
    (hSWRadial : KummerPrimeSiegelWalfisz)
    (hSW : AngularKummerPrimeExplicitEstimate) (hModel : FixedAngularPrimeExplicitEstimate)
    (hpubRadial : PrimitiveResidueHeckeInput) (hpub : PrimitiveAngularHeckeInput)
    {v : Eisenstein → MetaplecticDualArgument → ℂ} (hVor : MetaplecticVoronoiInput v)
    {F Ψ Zf : Eisenstein → ℂ → ℂ}
    (hF : MetaplecticContinuation F) (hZf : HeathBrownZBound Zf)
    (hfac : HeathBrownZFactorization Ψ Zf) (hdiv : HeathBrownFiniteDivisor F Ψ)
    (hpart : HeathBrownGaussPartialSums) (hHB : MetaplecticMeanSquare F) :
    FirstMomentStatement ∧ AngularComparisonStatement ∧ AngularCancellationStatement :=
  mainResults_of_remaining_analytic_inputs
    hSWRadial hSW hModel hpubRadial hpub huxleyAdditiveLargeSieve_proved hVor hF hZf hfac hdiv hpart hHB

end CubicFirstMoment

end

end OAI
