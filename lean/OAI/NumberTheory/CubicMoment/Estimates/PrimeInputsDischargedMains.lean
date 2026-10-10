import OAI.NumberTheory.CubicMoment.Estimates.KummerDischargedMains
import OAI.NumberTheory.CubicMoment.Angular.AngularPrimeInputsProof

namespace OAI

/-! All three raw prime estimates are derived from the remaining Hecke
completion inputs before applying the exact main theorems. -/
noncomputable section
namespace CubicFirstMoment

theorem mainResults_of_primitive_hecke_and_metaplectic_inputs
    (hpubRadial : PrimitiveResidueHeckeInput) (hpub : PrimitiveAngularHeckeInput)
    {v : Eisenstein → MetaplecticDualArgument → ℂ} (hVor : MetaplecticVoronoiInput v)
    {F Ψ Zf : Eisenstein → ℂ → ℂ}
    (hF : MetaplecticContinuation F) (hZf : HeathBrownZBound Zf)
    (hfac : HeathBrownZFactorization Ψ Zf) (hdiv : HeathBrownFiniteDivisor F Ψ)
    (hpart : HeathBrownGaussPartialSums) (hHB : MetaplecticMeanSquare F) :
    FirstMomentStatement ∧ AngularComparisonStatement ∧ AngularCancellationStatement :=
  mainResults_of_angular_hecke_and_metaplectic_inputs
    (angularKummerPrimeExplicitEstimate_of_primitive hpub)
    (fixedAngularPrimeExplicitEstimate_of_primitive hpub)
    hpubRadial hpub hVor hF hZf hfac hdiv hpart hHB

end CubicFirstMoment

end

end OAI
