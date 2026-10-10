import OAI.NumberTheory.CubicMoment.Estimates.SieveDischargedMains
import OAI.NumberTheory.CubicMoment.Estimates.KummerPrimeFromPrimitive

namespace OAI

/-! The exact three main statements with the radial Kummer prime input
proved from the remaining primitive Hecke completion input. -/
noncomputable section
namespace CubicFirstMoment

theorem mainResults_of_angular_hecke_and_metaplectic_inputs
    (hSW : AngularKummerPrimeExplicitEstimate) (hModel : FixedAngularPrimeExplicitEstimate)
    (hpubRadial : PrimitiveResidueHeckeInput) (hpub : PrimitiveAngularHeckeInput)
    {v : Eisenstein → MetaplecticDualArgument → ℂ} (hVor : MetaplecticVoronoiInput v)
    {F Ψ Zf : Eisenstein → ℂ → ℂ}
    (hF : MetaplecticContinuation F) (hZf : HeathBrownZBound Zf)
    (hfac : HeathBrownZFactorization Ψ Zf) (hdiv : HeathBrownFiniteDivisor F Ψ)
    (hpart : HeathBrownGaussPartialSums) (hHB : MetaplecticMeanSquare F) :
    FirstMomentStatement ∧ AngularComparisonStatement ∧ AngularCancellationStatement :=
  mainResults_of_hecke_and_metaplectic_inputs
    (kummerPrimeSiegelWalfisz_of_primitive hpubRadial) hSW hModel
    hpubRadial hpub hVor hF hZf hfac hdiv hpart hHB

end CubicFirstMoment

end

end OAI
