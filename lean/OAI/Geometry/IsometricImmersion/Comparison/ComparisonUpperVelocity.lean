import OAI.Geometry.IsometricImmersion.Taylor.TaylorUpperCauchyBounds
import OAI.Geometry.IsometricImmersion.Comparison.ActualComparisonEquation

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace SmoothLocal.HighEquation
open SmoothLocal.Geometry SmoothLocal.Taylor

theorem comparison_upper_velocity_jet_bound {P z : Coord → ℝ} {U : Set Coord} {I : Set ℝ}
    (hU : IsOpen U) (hI : IsOpen I) (hP : ContDiffOn ℝ ∞ P U) (hz : ContDiffOn ℝ ∞ z U)
    (b : ℝ) (hupper : ∀ x ∈ I, (![x,b] : Coord) ∈ U) {x : ℝ} (hx : x ∈ I)
    (N : ℕ) {BZ BP : ℝ}
    (hZB : ‖iteratedFDeriv ℝ N (heightCauchyVelocity z b) x‖ ≤ BZ)
    (hPB : ‖iteratedFDeriv ℝ N (heightCauchyVelocity P b) x‖ ≤ BP) :
    ‖iteratedFDeriv ℝ N (heightCauchyVelocity (comparisonDifference P z) b) x‖ ≤ BZ+BP := by
  have hzv := heightCauchyVelocity_contDiffOn hz hU b hupper
  have hPv := heightCauchyVelocity_contDiffOn hP hU b hupper
  have heq : heightCauchyVelocity (comparisonDifference P z) b =ᶠ[𝓝 x]
      (heightCauchyVelocity z b-heightCauchyVelocity P b) := by
    filter_upwards [hI.mem_nhds hx] with y hy
    exact CoordinateBound.iterated_sub hz hP hU [1] (hupper y hy)
  rw [(heq.iteratedFDeriv ℝ N).self_of_nhds,iteratedFDeriv_sub_apply
    ((hzv.contDiffAt (hI.mem_nhds hx)).of_le (WithTop.coe_le_coe.mpr le_top))
    ((hPv.contDiffAt (hI.mem_nhds hx)).of_le (WithTop.coe_le_coe.mpr le_top))]
  exact (norm_sub_le _ _).trans (add_le_add hZB hPB)

end SmoothLocal.HighEquation

end

end OAI
