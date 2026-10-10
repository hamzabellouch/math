import OAI.Analysis.LipschitzHilbert.Phase.AngularExceptionCount
import OAI.Analysis.LipschitzHilbert.Phase.AngularGraphMass
import OAI.Analysis.LipschitzHilbert.Phase.AngularGraphPrediction

namespace OAI

/-! Fourier prediction with actual snapshot masses and one path exception. -/

noncomputable section

open Set MeasureTheory
open scoped BigOperators

namespace LipschitzHilbert.AngularGrid

attribute [local instance] Classical.propDecidable

theorem sum_cell_mass_le_ancestor {ι X : Type*}
    (g : AngularGrid) (tops : Finset ι) (slope precision : ι → ℝ)
    (cutoff : ℝ) (weight : ι → X → ℝ) (hw : ∀ i x, 0 ≤ weight i x)
    (base level : ℕ) (parent : ℤ) (cells : Finset ℤ)
    (hsub : ∀ c ∈ cells, g.cellTops tops slope precision cutoff level c ⊆
      g.cellTops tops slope precision cutoff base parent) (x : X) :
    (∑ c ∈ cells, g.mass tops slope precision cutoff weight level c x) ≤
      g.mass tops slope precision cutoff weight base parent x := by
  classical
  have hdisjoint : (cells : Set ℤ).PairwiseDisjoint
      (g.cellTops tops slope precision cutoff level) := by
    intro a _ b _ hab
    exact g.cellTops_disjoint tops slope precision cutoff level hab
  change (∑ c ∈ cells, ∑ i ∈ g.cellTops tops slope precision cutoff level c,
    weight i x) ≤ _
  rw [← Finset.sum_biUnion hdisjoint]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.biUnion_subset.mpr hsub)
    (fun i _ _ => hw i x)

/-- The exact snapshot prediction of §9. The cardinality hypothesis concerns
significant tops, not graph cells; one unshrunk path child is allowed without
a significant representative. Both graph masses and normalized child weights
are the finite sums of the actual positive top weights. -/
theorem snapshot_prediction_average {ι κ : Type*} [DecidableEq ι] [Fintype κ]
    (g : AngularGrid) (tops : Finset ι) (T : ι → SlopeBox) (d : ι → ℝ)
    (cutoff : ℝ) (weight : ι → (ℝ × ℝ) → ℝ)
    (hd : ∀ i ∈ tops, 0 ≤ d i) (hw : ∀ i x, 0 < weight i x)
    (z : ℝ × ℝ) (base level : ℕ) (hle : base ≤ level)
    (parent : ℤ) (cells : Finset ℤ) (representative : cells → ℝ)
    (hcell : ∀ c, g.index (level + 1) (representative c) = c.val)
    (hancestor : ∀ c, g.index base (representative c) = parent)
    (hnonempty : ∀ c : cells,
      (g.cellTops tops (fun i => (T i).slope) d cutoff (level + 1) c.val).Nonempty)
    (exception : ℤ) {gap B K D p etaMin : ℝ}
    (hgap : 0 < gap) (hetaMin : 0 < etaMin) (hD : 2 ≤ D) (hp : 4 ≤ p)
    (hprecision : cutoff / (g.branching : ℝ) ^ (level + 1) ≤ gap / B ^ 2)
    (hspan : g.width base ≤ B * gap)
    (hsignificant : ∀ c ∈ cells, c ≠ exception →
      ∃ i ∈ g.cellTops tops (fun i => (T i).slope) d cutoff (level + 1) c,
        (T i).radius z ≤ K)
    (hcount : ∀ I : Finset ι, I ⊆ tops →
      (∀ i ∈ I, (T i).radius z ≤ K) →
      (∀ i ∈ I, d i ≤ gap / B ^ 2) →
      (∀ i ∈ I, ∀ j ∈ I, |(T i).slope - (T j).slope| ≤ B * gap) →
      (∀ i ∈ I, ∀ j ∈ I, i ≠ j → gap ≤ |(T i).slope - (T j).slope|) →
      (I.card : ℝ) ≤ D / 100)
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (s : ℝ) (eta : κ → ℝ) (heta : ∀ k, etaMin ≤ |eta k|)
    (hν : PhaseCombinatorics.FourierGap ν (gap * etaMin))
    (X : cells → EuclideanSpace ℂ κ) (lambda : cells → ℂ)
    (hn : 0 < g.mass tops (fun i => (T i).slope) d cutoff weight base parent z)
    (hlambda : ∀ c, ‖lambda c‖ ≤
      (g.mass tops (fun i => (T i).slope) d cutoff weight (level + 1) c.val z /
        g.boundaryMass tops (fun i => (T i).slope) d cutoff weight base level gap
          (representative c) z) ^ PhaseCombinatorics.phaseMu D p) :
    let n := g.mass tops (fun i => (T i).slope) d cutoff weight base parent z
    let l := fun c : cells =>
      g.mass tops (fun i => (T i).slope) d cutoff weight (level + 1) c.val z / n
    (∫ t, (1 + ‖PhaseCombinatorics.diagonalFourierSum
      (fun c k => (s - g.center (level + 1) c.val) * eta k)
      (fun c => (((l c ^ (1 - PhaseCombinatorics.phaseMu D p) : ℝ) : ℂ) *
        lambda c) • X c) t‖ ^ p) / (1 + ∑ c, l c * ‖X c‖ ^ p) ∂ν) ≤ 1 := by
  classical
  let w := fun c : cells =>
    g.mass tops (fun i => (T i).slope) d cutoff weight (level + 1) c.val z
  let m := fun c : cells =>
    g.boundaryMass tops (fun i => (T i).slope) d cutoff weight base level gap
      (representative c) z
  let n := g.mass tops (fun i => (T i).slope) d cutoff weight base parent z
  have hsub (c : ℤ) (hc : c ∈ cells) :
      g.cellTops tops (fun i => (T i).slope) d cutoff (level + 1) c ⊆
        g.cellTops tops (fun i => (T i).slope) d cutoff base parent := by
    have h := g.cellTops_subset_ancestor tops (fun i => (T i).slope) d cutoff hd
      (hle.trans (Nat.le_succ _)) (representative ⟨c, hc⟩)
    simpa only [hcell, hancestor] using h
  have hwpos (c : cells) : 0 < w c := by
    obtain ⟨i, hi⟩ := hnonempty c
    exact g.mass_pos_of_member tops (fun i => (T i).slope) d cutoff weight hw
      (level + 1) c.val z hi
  have htotal : ∑ c : cells, w c / n ≤ 1 := by
    rw [← Finset.sum_div, div_le_one hn]
    have h := g.sum_cell_mass_le_ancestor tops (fun i => (T i).slope) d cutoff weight
      (fun i x => (hw i x).le) base (level + 1) parent cells hsub z
    change (∑ c : cells, g.mass tops (fun i => (T i).slope) d cutoff weight
      (level + 1) c.val z) ≤ n
    rw [Finset.sum_subtype cells (p := fun c => c ∈ cells) (by simp)] at h
    exact h
  apply g.angular_graph_prediction_average (level + 1) cells w m hwpos
    (fun c => g.closed_neighborhood_mass_le_boundary tops (fun i => (T i).slope)
      d cutoff weight hd (fun i x => (hw i x).le) hle hgap.le cells representative
      parent hcell hancestor c z) ν s eta (fun c => w c / n) X lambda
    hgap hetaMin heta hν (by linarith) hp
  · intro S hS hpair
    have h := g.independent_cells_card_le_one_exception tops T d z cutoff base
      (level + 1) parent S exception hprecision hspan
      (fun c hc => hsub c (hS hc))
      (fun c hc => hsignificant c (hS hc)) hpair hcount
    linarith
  · exact fun c => (div_pos (hwpos c) hn).le
  · exact htotal
  · exact hlambda

end LipschitzHilbert.AngularGrid

end

end OAI
