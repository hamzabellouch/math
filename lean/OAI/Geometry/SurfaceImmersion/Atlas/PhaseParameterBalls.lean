import OAI.Geometry.SurfaceImmersion.Primitive.UniformCircularPhaseCharts
import OAI.Geometry.Immersion.ClosedSurface.PhaseStock

namespace OAI

/-! Compact independent parameter balls about the three nonzero covectors. -/
noncomputable section
open Set Metric
open scoped Topology
namespace ClosedSurfaceR4.PhaseGeometry
open SmallModes

theorem phase_parameter_balls (P : PhaseBasis) :
    ∃ eps : ℝ, 0 < eps ∧ eps ≤ 1 ∧
      ∀ j : Fin 3, IsCompact (closedBall (P.ξ j) eps) ∧
        ∀ ell ∈ closedBall (P.ξ j) eps, ell ≠ 0 ∧ ‖ell‖ ≤ ‖P.ξ‖+1 := by
  let eps := min 1 (min (‖P.ξ 0‖/2) (min (‖P.ξ 1‖/2) (‖P.ξ 2‖/2)))
  have h0 : 0 < ‖P.ξ 0‖ := norm_pos_iff.mpr (P.nonzero 0)
  have h1 : 0 < ‖P.ξ 1‖ := norm_pos_iff.mpr (P.nonzero 1)
  have h2 : 0 < ‖P.ξ 2‖ := norm_pos_iff.mpr (P.nonzero 2)
  have heps : 0 < eps := lt_min zero_lt_one (lt_min (by positivity) (lt_min (by positivity) (by positivity)))
  have heps1 : eps ≤ 1 := min_le_left _ _
  have hs (j : Fin 3) : eps < ‖P.ξ j‖ := by
    have ha := (min_le_right 1 (min (‖P.ξ 0‖/2) (min (‖P.ξ 1‖/2) (‖P.ξ 2‖/2))))
    have hb := min_le_left (‖P.ξ 0‖/2) (min (‖P.ξ 1‖/2) (‖P.ξ 2‖/2))
    have hc := min_le_right (‖P.ξ 0‖/2) (min (‖P.ξ 1‖/2) (‖P.ξ 2‖/2))
    have hd := min_le_left (‖P.ξ 1‖/2) (‖P.ξ 2‖/2)
    have he := min_le_right (‖P.ξ 1‖/2) (‖P.ξ 2‖/2)
    fin_cases j
    · change eps < ‖P.ξ 0‖
      dsimp only [eps]
      linarith
    · change eps < ‖P.ξ 1‖
      dsimp only [eps]
      linarith
    · change eps < ‖P.ξ 2‖
      dsimp only [eps]
      linarith
  refine ⟨eps,heps,heps1,fun j => ⟨isCompact_closedBall _ _,?_⟩⟩
  intro ell hell
  have hb : ‖ell-P.ξ j‖ ≤ eps := by simpa only [mem_closedBall,dist_eq_norm] using hell
  refine ⟨?_,?_⟩
  · intro hz
    rw [hz,zero_sub,norm_neg] at hb
    exact (not_le_of_gt (hs j)) hb
  · calc
      ‖ell‖ ≤ ‖ell-P.ξ j‖+‖P.ξ j‖ := by simpa only [sub_add_cancel] using norm_add_le (ell-P.ξ j) (P.ξ j)
      _ ≤ eps+‖P.ξ‖ := add_le_add hb (norm_le_pi_norm P.ξ j)
      _ ≤ ‖P.ξ‖+1 := by linarith

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
