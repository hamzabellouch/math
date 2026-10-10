import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.PlaneScalarMildDataFields
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.PlaneScalarMildJointSmooth
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.PlaneScalarMildActualEquation
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.PlaneScalarInput

namespace OAI

/-! Whole-plane scalar existence via the Gaussian mild construction. -/

noncomputable section
namespace ForcedComputation.VelocityDetector
open ShearFlows Set PlaneScalarMild
open scoped Topology ContDiff

theorem planeScalarExistence : PlaneScalarExistence := by
  intro T ν hT hν a h ha hh hcompact
  obtain ⟨K,hK,hKh⟩ := hcompact T hT.le
  have hsource : ∀ t ∈ Icc (0 : ℝ) T, ∀ x ∉ K, Function.uncurry h (t,x) = 0 :=
    fun t ht x hx => (hKh t ht x hx).2
  have hcoeff : ∀ i t, t ∈ Icc (0 : ℝ) T → ∀ x ∉ K,
      driftCoefficients a i (t,x) = 0 := by
    intro i t ht x hx
    exact driftCoefficients_supported hK.isClosed (fun y hy => (hKh t ht y hy).1) i x hx
  obtain ⟨D,hinit,hs,hb⟩ := exists_supported_zero_data hK hh hsource
    (driftCoefficients_smooth ha) hcoeff
  have htime := D.supported_solutionJetValue_smooth_time hT hν hK hh hsource
    (driftCoefficients_smooth ha) hcoeff hs hb
  refine ⟨D.solutionValue hT.le hν, ?_, ?_⟩
  · refine ⟨D.solutionValue_smooth hT hν htime, ?_, ?_, ?_⟩
    · funext x
      change D.solution hT.le hν (projIcc 0 T hT.le 0) x = 0
      rw [projIcc_of_mem hT.le (show (0 : ℝ) ∈ Icc 0 T from ⟨le_rfl,hT.le⟩)]
      exact (D.solution_initial hT.le hν x).trans (hinit 0 x)
    · intro t ht x
      exact D.solutionValue_equation hT.le hν ha hs hb ht x
    · obtain ⟨B,_,hB⟩ := D.solutionValue_spatial_bounds hT.le hν 1
      refine ⟨B, fun t ht x => ?_⟩
      constructor
      · simpa only [norm_iteratedFDeriv_zero, Real.norm_eq_abs] using hB t ht 0 (by omega) x
      · simpa only [norm_iteratedFDeriv_one] using hB t ht 1 (by omega) x
  · obtain ⟨B,_,hB⟩ := D.solutionValue_spatial_bounds hT.le hν 3
    exact ⟨B,hB⟩

end ForcedComputation.VelocityDetector

end

end OAI
