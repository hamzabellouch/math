import OAI.Analysis.LipschitzHilbert.Trees.SourceBoundaryRadial
import OAI.Analysis.LipschitzHilbert.Trees.SourceBoundaryScales

namespace OAI

/-! The source neighborhood fits inside the radius 4 G^(-1/4) d(i).
The one-boundary radial comparison uses exactly this radius. -/

noncomputable section
namespace LipschitzHilbert.AngularGrid
variable {τ X : Type*}

theorem sourceBoundaryGap_ge_child (g : AngularGrid) (L : ℝ)
    (hbranch : (g.branching:ℝ) = SourceParameters.step L) (i : ℕ) :
    g.width (i+1) ≤ g.sourceBoundaryGap L i := by
  rw [g.sourceBoundaryGap_eq_sourceGap L hbranch]
  change g.width (i+1) ≤ SourceParameters.step L^(3/4:ℝ)*g.width (i+1)
  exact le_mul_of_one_le_left (g.width_pos (i+1)).le
    (Real.one_le_rpow (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2)) (by norm_num))

theorem source_boundary_radius (g : AngularGrid) (L : ℝ)
    (hbranch : (g.branching:ℝ) = SourceParameters.step L) (i : ℕ) :
    g.sourceBoundaryGap L i+2*g.width (i+1) <
      (4*SourceParameters.step L^(-(1/4:ℝ)))*g.width i := by
  have hc := g.sourceBoundaryGap_ge_child L hbranch i
  have hg := g.sourceBoundaryGap_pos L i
  have heq : (4*SourceParameters.step L^(-(1/4:ℝ)))*g.width i =
      4*g.sourceBoundaryGap L i := by unfold sourceBoundaryGap; ring
  rw [heq]
  nlinarith

theorem source_boundary_log_loss_le_radial (g : AngularGrid) (L : ℝ)
    (hbranch : (g.branching:ℝ) = SourceParameters.step L)
    (tops : Finset τ) (slope precision : τ → ℝ) (cutoff : ℝ) (weight : τ → X → ℝ)
    (hp : ∀ t ∈ tops, 0 ≤ precision t) (hw : ∀ t x, 0 < weight t x)
    {K : ℕ} (hK : 0 < K) (i : ℕ) (b : ℝ) (hb : 0 < b)
    (hbε : b ≤ 4*SourceParameters.step L^(-(1/4:ℝ))) (top : τ)
    (htop : top ∈ tops) (he : g.eligible cutoff (precision top) i)
    (hbd : b*g.width i ≤ g.boundaryDistance i (slope top)) (x : X) :
    Real.log (g.sourceBoundaryMass tops slope precision cutoff weight K (g.sourceBoundaryGap L)
      i (g.index (i+1) (slope top)) x /
        g.mass tops slope precision cutoff weight i (g.index i (slope top)) x) ≤
    Real.log (g.nearbyEligibleMass tops slope precision cutoff weight i
      ((4*SourceParameters.step L^(-(1/4:ℝ)))*g.width i) (slope top) x /
        g.nearbyEligibleMass tops slope precision cutoff weight i (b*g.width i) (slope top) x) := by
  rw [g.sourceBoundaryMass_path tops slope precision cutoff weight hK]
  exact g.boundary_log_loss_le_radial tops slope precision cutoff weight hp hw
    (i+1-K) i (g.sourceBoundaryGap L i) (b*g.width i)
    ((4*SourceParameters.step L^(-(1/4:ℝ)))*g.width i)
    (mul_pos hb (g.width_pos i)) (mul_le_mul_of_nonneg_right hbε (g.width_pos i).le)
    top hbd (g.source_boundary_radius L hbranch i) htop he x

end LipschitzHilbert.AngularGrid

end

end OAI
