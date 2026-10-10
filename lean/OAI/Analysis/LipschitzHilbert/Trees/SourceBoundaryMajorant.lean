import OAI.Analysis.LipschitzHilbert.Trees.SourceBoundaryRadius
import OAI.Analysis.LipschitzHilbert.Trees.SourceRadialLoss

namespace OAI

/-! The source boundary log loss is bounded by the radial near-boundary
majorant at its actual normalized distance. Far from boundaries it vanishes. -/

noncomputable section
open Set
namespace LipschitzHilbert.AngularGrid
variable {τ X : Type*}

theorem source_boundary_log_loss_le_majorant (g : AngularGrid) (L : ℝ)
    (hbranch : (g.branching:ℝ) = SourceParameters.step L)
    (tops : Finset τ) (slope precision : τ → ℝ) (cutoff : ℝ) (weight : τ → X → ℝ)
    (hp : ∀ t ∈ tops, 0 ≤ precision t) (hw : ∀ t x, 0 < weight t x)
    {K : ℕ} (hK : 0 < K) (i : ℕ) (top : τ) (htop : top ∈ tops)
    (he : g.eligible cutoff (precision top) i) (x : X) :
    let epsilon := 4*SourceParameters.step L^(-(1/4:ℝ))
    let b := g.boundaryDistance i (slope top)/g.width i
    0 < b →
    Real.log (g.sourceBoundaryMass tops slope precision cutoff weight K (g.sourceBoundaryGap L)
      i (g.index (i+1) (slope top)) x /
        g.mass tops slope precision cutoff weight i (g.index i (slope top)) x) ≤
      g.radialBoundaryLoss tops slope precision cutoff weight epsilon i top x b := by
  intro epsilon b hb
  by_cases hnear : b < epsilon
  · rw [radialBoundaryLoss,indicator_of_mem (show b ∈ Ioo 0 epsilon from ⟨hb,hnear⟩)]
    apply g.source_boundary_log_loss_le_radial L hbranch tops slope precision cutoff weight hp hw
      hK i b hb hnear.le top htop he _ x
    dsimp only [b]
    rw [div_mul_cancel₀ _ (g.width_pos i).ne']
  · rw [radialBoundaryLoss,indicator_of_notMem (show b ∉ Ioo 0 epsilon from fun h => hnear h.2)]
    have hfar : epsilon*g.width i ≤ g.boundaryDistance i (slope top) :=
      (le_div_iff₀ (g.width_pos i)).mp (le_of_not_gt hnear)
    have heq := g.boundary_mass_eq_parent_of_far tops slope precision cutoff weight hp
      (i+1-K) i (g.sourceBoundaryGap L i) (epsilon*g.width i) (slope top)
      (g.source_boundary_radius L hbranch i) hfar x
    rw [g.sourceBoundaryMass_path tops slope precision cutoff weight hK,heq,
      div_self (g.path_mass_pos tops slope precision cutoff weight hw i top htop he x).ne',Real.log_one]

end LipschitzHilbert.AngularGrid

end

end OAI
