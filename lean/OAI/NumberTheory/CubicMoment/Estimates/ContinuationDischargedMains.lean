import OAI.NumberTheory.CubicMoment.Estimates.PrimeInputsDischargedMains
import OAI.NumberTheory.CubicMoment.Transform.MetaplecticContinuationProof

namespace OAI

/-! The exact main statements after deriving continuation and all raw
prime bounds. Continuation is built from the same Voronoi input; it is
not an additional hypothesis. -/
noncomputable section
namespace CubicFirstMoment

theorem mainResults_of_hecke_voronoi_and_heathBrown
    (hpubRadial : PrimitiveResidueHeckeInput) (hpub : PrimitiveAngularHeckeInput)
    {a : Eisenstein → MetaplecticDualArgument → ℂ} (hVor : MetaplecticVoronoiInput a)
    {Ψ Zf : Eisenstein → ℂ → ℂ} (hZf : HeathBrownZBound Zf)
    (hfac : HeathBrownZFactorization Ψ Zf)
    (hdiv : HeathBrownFiniteDivisor metaplecticCanonicalGauss Ψ)
    (hpart : HeathBrownGaussPartialSums) (hHB : MetaplecticMeanSquare metaplecticCanonicalGauss) :
    FirstMomentStatement ∧ AngularComparisonStatement ∧ AngularCancellationStatement :=
  mainResults_of_primitive_hecke_and_metaplectic_inputs hpubRadial hpub hVor
    (metaplecticContinuation_of_voronoi hVor) hZf hfac hdiv hpart hHB

end CubicFirstMoment

end

end OAI
