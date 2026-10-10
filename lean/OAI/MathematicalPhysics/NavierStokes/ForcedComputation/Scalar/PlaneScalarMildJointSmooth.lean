import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.BoundedSpatialJetJointSmooth
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.PlaneScalarMildTimeSmooth

namespace OAI

/-! Joint smoothness of the actual scalar mild solution on the closed time slab. -/

noncomputable section
namespace ForcedComputation.PlaneScalarMild.CompatibleData
open ShearFlows Set
open scoped Topology ContDiff

private def smoothCurves {T ν : ℝ} (hT : 0 < T) (hν : 0 < ν) (D : CompatibleData T)
    (hs : ∀ k, ContDiffOn ℝ ∞ (D.solutionJetValue hT.le hν k) (Icc (0 : ℝ) T)) :
    BoundedSpatialJets.SmoothPlaneCurves T where
  curve := D.solutionJetValue hT.le hν
  smooth := hs
  compatible := by
    intro k n hkn t _
    have he := congrArg (fun q : WeaklySingular.Path (Jet k) T =>
      q (projIcc 0 T hT.le t)) (D.solutionJet_truncate hT.le hν k n hkn)
    exact he

/-- Norm-smooth time jets give joint smoothness, including the initial boundary. -/
theorem solutionValue_smooth {T ν : ℝ} (hT : 0 < T) (hν : 0 < ν) (D : CompatibleData T)
    (hs : ∀ k, ContDiffOn ℝ ∞ (D.solutionJetValue hT.le hν k) (Icc (0 : ℝ) T)) :
    ContDiffOn ℝ ∞ (Function.uncurry (D.solutionValue hT.le hν))
      (Icc (0 : ℝ) T ×ˢ (univ : Set Plane)) := by
  have he : (smoothCurves hT hν D hs).value = Function.uncurry (D.solutionValue hT.le hν) := by
    funext p
    exact congrFun (D.solutionJetValue_function hT.le hν 0 p.1) p.2
  rw [← he]
  exact (smoothCurves hT hν D hs).value_contDiffOn hT

/-- Uniform bounds on any finite list of spatial derivative orders. -/
theorem solutionValue_spatial_bounds {T ν : ℝ} (hT : 0 ≤ T) (hν : 0 < ν)
    (D : CompatibleData T) (n : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t ∈ Icc (0 : ℝ) T, ∀ k ≤ n, ∀ x,
      ‖iteratedFDeriv ℝ k (D.solutionValue hT hν t) x‖ ≤ B := by
  choose C hC hc using D.solution_spatial_bound hT hν
  refine ⟨∑ k ∈ Finset.range (n+1), C k, Finset.sum_nonneg (fun k _ => hC k), ?_⟩
  intro t _ k hk x
  exact (hc k (projIcc 0 T hT t) x).trans
    (Finset.single_le_sum (fun i _ => hC i) (Finset.mem_range.mpr (by omega)))

end ForcedComputation.PlaneScalarMild.CompatibleData

end

end OAI
