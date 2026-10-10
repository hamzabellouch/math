import OAI.Analysis.LipschitzHilbert.Trees.SourceBlockChildren
import OAI.Analysis.LipschitzHilbert.Phase.AngularSnapshot
import OAI.Analysis.LipschitzHilbert.Trees.SourceShiftedDrop
import OAI.Analysis.LipschitzHilbert.Phase.SourcePredictionValues

namespace OAI

/-! The source predictor's off-child fractions are bounded by the actual
forward path drop. The final ineligible path has drop one even if other
children still continue. -/

noncomputable section
open scoped BigOperators
namespace LipschitzHilbert
open PhaseCombinatorics
attribute [local instance] Classical.propDecidable

namespace AngularGrid
variable {ι X : Type*}

theorem sourceBlock_child_fractions (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (weight : ι → X → ℝ)
    (hp : ∀ t ∈ tops, 0 ≤ precision t) (hw : ∀ t x, 0 ≤ weight t x)
    (lower upper : ℕ) (hlu : lower ≤ upper) (parent : ℤ) (x : X)
    (hn : 0 < g.mass tops slope precision cutoff weight lower parent x) :
    (∑ i : g.sourceBlockCells tops slope precision cutoff lower upper parent,
      g.mass tops slope precision cutoff weight upper i.val x /
        g.mass tops slope precision cutoff weight lower parent x) ≤ 1 := by
  let cells := g.sourceBlockCells tops slope precision cutoff lower upper parent
  have hsub (cell : ℤ) (hc : cell ∈ cells) :
      g.cellTops tops slope precision cutoff upper cell ⊆
        g.cellTops tops slope precision cutoff lower parent := by
    let top := g.sourceBlockTop tops slope precision cutoff lower upper parent ⟨cell,hc⟩
    have htop := g.sourceBlockTop_spec tops slope precision cutoff lower upper parent ⟨cell,hc⟩
    have hs := g.cellTops_subset_ancestor tops slope precision cutoff hp hlu (slope top)
    simpa only [top,htop.2.1,htop.2.2.2] using hs
  have hs := g.sum_cell_mass_le_ancestor tops slope precision cutoff weight hw
    lower upper parent cells hsub x
  rw [Finset.sum_subtype cells (p := fun j => j ∈ cells) (by simp)] at hs
  rw [← Finset.sum_div,div_le_one hn]
  exact hs

theorem sourceBlock_off_fractions (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (weight : ι → X → ℝ)
    (hp : ∀ t ∈ tops, 0 ≤ precision t) (hw : ∀ t x, 0 ≤ weight t x)
    (lower upper : ℕ) (hlu : lower ≤ upper) (parent : ℤ) (x : X)
    (hn : 0 < g.mass tops slope precision cutoff weight lower parent x)
    (i₀ : g.sourceBlockCells tops slope precision cutoff lower upper parent) :
    (∑ i : RemainderIndex i₀,
      g.mass tops slope precision cutoff weight upper i.val.val x /
        g.mass tops slope precision cutoff weight lower parent x) ≤
      1-g.mass tops slope precision cutoff weight upper i₀.val x /
        g.mass tops slope precision cutoff weight lower parent x := by
  have hs := g.sourceBlock_child_fractions tops slope precision cutoff weight hp hw
    lower upper hlu parent x hn
  rw [Fintype.sum_eq_add_sum_subtype_ne _ i₀] at hs
  linarith

/-- A continuing path selects its actual child cell; its lost fraction
pays for every other continuing child and every terminated top. -/
theorem sourceBlock_continuing_drop {K : ℕ} (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (weight : ι → X → ℝ)
    (hp : ∀ t ∈ tops, 0 ≤ precision t) (hw : ∀ t x, 0 < weight t x)
    (hK : 0 < K) (σ : Fin K) (j : ℕ) (top : ι) (htop : top ∈ tops)
    (he : g.eligible cutoff (precision top) (ShiftedBlocks.endpoint σ (j+1))) (x : X)
    (i₀ : g.sourceBlockCells tops slope precision cutoff (ShiftedBlocks.endpoint σ j)
      (ShiftedBlocks.endpoint σ (j+1)) (g.index (ShiftedBlocks.endpoint σ j) (slope top)))
    (hi : i₀.val = g.index (ShiftedBlocks.endpoint σ (j+1)) (slope top)) :
    let n := g.mass tops slope precision cutoff weight (ShiftedBlocks.endpoint σ j)
      (g.index (ShiftedBlocks.endpoint σ j) (slope top)) x
    let c := fun i => g.mass tops slope precision cutoff weight (ShiftedBlocks.endpoint σ (j+1)) i x
    let u := pathDrop (g.shiftedPathMass tops slope precision cutoff weight σ top x) j
    1-c i₀.val/n = u ∧ (∑ i : RemainderIndex i₀, c i.val.val/n) ≤ u := by
  dsimp only
  have hlu := (ShiftedBlocks.endpoint_strictMono hK σ).monotone (Nat.le_succ j)
  have he0 := g.eligible_of_le (hp top htop) hlu he
  have hn := g.path_mass_pos tops slope precision cutoff weight hw _ top htop he0 x
  have hdrop : pathDrop (g.shiftedPathMass tops slope precision cutoff weight σ top x) j =
      1-g.mass tops slope precision cutoff weight (ShiftedBlocks.endpoint σ (j+1)) i₀.val x /
        g.mass tops slope precision cutoff weight (ShiftedBlocks.endpoint σ j)
          (g.index (ShiftedBlocks.endpoint σ j) (slope top)) x := by
    simp only [pathDrop,shiftedPathMass,ite_eq_left he0,ite_eq_left he,hi,sub_div,div_self hn.ne']
  refine ⟨hdrop.symm,?_⟩
  rw [hdrop]
  exact g.sourceBlock_off_fractions tops slope precision cutoff weight hp
    (fun t z => (hw t z).le) _ _ hlu _ x hn i₀

/-- At the terminal block any remaining child can serve as the graph's
exception: both its complement and its defect are bounded by drop one. -/
theorem sourceBlock_terminal_drop {K : ℕ} (g : AngularGrid) (tops : Finset ι)
    (slope precision : ι → ℝ) (cutoff : ℝ) (weight : ι → X → ℝ)
    (hp : ∀ t ∈ tops, 0 ≤ precision t) (hw : ∀ t x, 0 < weight t x)
    (hK : 0 < K) (σ : Fin K) (j : ℕ) (top : ι) (htop : top ∈ tops)
    (he : g.eligible cutoff (precision top) (ShiftedBlocks.endpoint σ j))
    (hnext : ¬g.eligible cutoff (precision top) (ShiftedBlocks.endpoint σ (j+1))) (x : X)
    (i₀ : g.sourceBlockCells tops slope precision cutoff (ShiftedBlocks.endpoint σ j)
      (ShiftedBlocks.endpoint σ (j+1)) (g.index (ShiftedBlocks.endpoint σ j) (slope top))) :
    let n := g.mass tops slope precision cutoff weight (ShiftedBlocks.endpoint σ j)
      (g.index (ShiftedBlocks.endpoint σ j) (slope top)) x
    let c := fun i => g.mass tops slope precision cutoff weight (ShiftedBlocks.endpoint σ (j+1)) i x
    let u := pathDrop (g.shiftedPathMass tops slope precision cutoff weight σ top x) j
    1-c i₀.val/n ≤ u ∧ (∑ i : RemainderIndex i₀, c i.val.val/n) ≤ u := by
  dsimp only
  rw [g.shiftedPathDrop_terminal tops slope precision cutoff weight hw σ top htop x j he hnext]
  have hn := g.path_mass_pos tops slope precision cutoff weight hw _ top htop he x
  have hc := g.mass_nonnegative tops slope precision cutoff weight (fun t z => (hw t z).le)
    (ShiftedBlocks.endpoint σ (j+1)) i₀.val x
  have hd : 1-g.mass tops slope precision cutoff weight (ShiftedBlocks.endpoint σ (j+1)) i₀.val x /
      g.mass tops slope precision cutoff weight (ShiftedBlocks.endpoint σ j)
        (g.index (ShiftedBlocks.endpoint σ j) (slope top)) x ≤ 1 := by
    exact sub_le_self _ (div_nonneg hc hn.le)
  refine ⟨hd,?_⟩
  exact (g.sourceBlock_off_fractions tops slope precision cutoff weight hp
    (fun t z => (hw t z).le) _ _
    ((ShiftedBlocks.endpoint_strictMono hK σ).monotone (Nat.le_succ j)) _ x hn i₀).trans hd

end AngularGrid

theorem sourcePredictionValue_pos {ι κ : Type} [Fintype ι] [Fintype κ]
    (p μ n : ℝ) (hn : 0 < n) (c : ι → ℝ) (hc : ∀ i, 0 ≤ c i)
    (A : ι → EuclideanSpace ℂ κ) (lam : ι → ℂ) :
    0 < sourcePredictionValue p μ n c A lam := by
  unfold sourcePredictionValue
  apply energyRatio_pos
  have hs : 0 ≤ ∑ i, (c i/n)*‖(c i)^(μ-1) • A i‖^p :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (div_nonneg (hc i) hn.le)
      (Real.rpow_nonneg (norm_nonneg _) _))
  linarith

end LipschitzHilbert

end

end OAI
