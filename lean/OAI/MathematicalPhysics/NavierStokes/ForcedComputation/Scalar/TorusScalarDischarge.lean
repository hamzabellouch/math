import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.PlaneScalarMildDataFields
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.PlaneScalarMildJointSmooth
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.PlaneScalarMildActualEquation
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.PlaneScalarMildPeriodicity

namespace OAI

/-! Scalar existence on the torus via periodic Gaussian mild solutions. -/

noncomputable section
namespace ForcedComputation.VelocityDetector
open ShearFlows Set PlaneScalarMild
open scoped Topology ContDiff

theorem torusScalarExistence : TorusScalarExistence := by
  intro T ν hT hν a h w₀ ha hh hw hpa hph hpw
  have hpb := driftCoefficients_periodic ha hpa
  obtain ⟨D,hinit,hs,hb⟩ := exists_periodic_data hT.le hw hpw hh hph
    (driftCoefficients_smooth ha) hpb
  have htime := D.periodic_solutionJetValue_smooth_time hT hν hh hph
    (driftCoefficients_smooth ha) hpb hs hb
  refine ⟨D.solutionValue hT.le hν, D.solutionValue_smooth hT hν htime, ?_, ?_, ?_⟩
  · intro t _
    exact D.solution_periodic_of_representatives hT.le hν hpw hph hpb hinit hs hb
      (projIcc 0 T hT.le t)
  · funext x
    change D.solution hT.le hν (projIcc 0 T hT.le 0) x = w₀ x
    rw [projIcc_of_mem hT.le (show (0 : ℝ) ∈ Icc 0 T from ⟨le_rfl,hT.le⟩)]
    exact (D.solution_initial hT.le hν x).trans (hinit 0 x)
  · intro t ht x
    exact D.solutionValue_equation hT.le hν ha hs hb ht x

end ForcedComputation.VelocityDetector

end

end OAI
