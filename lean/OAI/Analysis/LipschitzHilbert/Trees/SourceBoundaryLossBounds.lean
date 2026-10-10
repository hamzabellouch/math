import OAI.Analysis.LipschitzHilbert.Phase.AngularSourceAmplitude

namespace OAI

/-! A single actual source boundary loss lies between zero and the
fixed total/self logarithm; this supplies integrability in the translation. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.AngularGrid
variable {τ X : Type*}

theorem source_boundary_log_loss_bounds (g : AngularGrid) (tops : Finset τ)
    (slope precision : τ → ℝ) (cutoff : ℝ) (weight : τ → X → ℝ)
    (hp : ∀ t ∈ tops, 0 ≤ precision t) (hw : ∀ t x, 0 < weight t x)
    {K : ℕ} (hK : 0 < K) (gap : ℕ → ℝ) (i : ℕ) (top : τ)
    (htop : top ∈ tops) (he : g.eligible cutoff (precision top) i) (x : X) :
    let loss := Real.log (g.sourceBoundaryMass tops slope precision cutoff weight K gap i
      (g.index (i+1) (slope top)) x / g.mass tops slope precision cutoff weight i (g.index i (slope top)) x)
    0 ≤ loss ∧ loss ≤ Real.log ((∑ t ∈ tops, weight t x)/weight top x) := by
  intro loss
  have hself : weight top x ≤ g.mass tops slope precision cutoff weight i (g.index i (slope top)) x :=
    Finset.single_le_sum (fun t _ => (hw t x).le)
      ((g.mem_cellTops _ _ _ _ _ _ _).mpr ⟨htop,rfl,he⟩)
  have hn := (hw top x).trans_le hself
  have hnb := g.sourceBoundaryMass_parent_le tops slope precision cutoff weight hp
    (fun t x => (hw t x).le) hK gap i (slope top) x
  have hb := (g.sourceBoundaryMass_bounds tops slope precision cutoff weight hp
    (fun t x => (hw t x).le) hK gap i (slope top) x).2
  have hbt := hb.trans (g.mass_le_total tops slope precision cutoff weight
    (fun t x => (hw t x).le) (i+1-K) (g.index (i+1-K) (slope top)) x)
  have ht0 := (hn.trans_le hnb).trans_le hbt
  exact ⟨Real.log_nonneg ((one_le_div hn).mpr hnb),
    Real.log_le_log (div_pos (hn.trans_le hnb) hn) (div_le_div₀ ht0.le hbt (hw top x) hself)⟩

end LipschitzHilbert.AngularGrid

end

end OAI
