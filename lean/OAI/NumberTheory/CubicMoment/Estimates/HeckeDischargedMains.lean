import OAI.NumberTheory.CubicMoment.Estimates.VoronoiDischargedMains
import OAI.NumberTheory.CubicMoment.Estimates.PrimitiveHeckeProof

namespace OAI

/-! All three exact main results with the primitive Hecke inputs discharged.
Only the explicit published cubic Voronoi input remains. -/
noncomputable section
namespace CubicFirstMoment

theorem mainResults_of_voronoi
    {a : Eisenstein → MetaplecticDualArgument → ℂ} (hVor : MetaplecticVoronoiInput a) :
    FirstMomentStatement ∧ AngularComparisonStatement ∧ AngularCancellationStatement :=
  mainResults_of_hecke_and_voronoi primitiveResidueHeckeInput_proved
    primitiveAngularHeckeInput_proved hVor

end CubicFirstMoment

end

end OAI
