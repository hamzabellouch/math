import OAI.Analysis.LipschitzHilbert.Phase.AngularSnapshot
import OAI.Analysis.LipschitzHilbert.Phase.SourceActivePrediction

namespace OAI

/-! The simultaneous top count supplies exactly the graph bound used after
zero snapshot children are removed. The unshrunk path is the sole exception. -/

noncomputable section
open Set
open scoped BigOperators
namespace LipschitzHilbert.AngularGrid
attribute [local instance] Classical.propDecidable

/-- Only supported snapshot children need significant top representatives. -/
theorem supported_snapshot_independence {ι κ : Type} [DecidableEq ι] [Fintype κ]
    (g : AngularGrid) (tops : Finset ι) (T : ι → SlopeBox) (d : ι → ℝ)
    (z : ℝ × ℝ) (cutoff : ℝ) (base level : ℕ) (parent : ℤ)
    (cells : Finset ℤ) (representative : cells → ℝ)
    (hcell : ∀ c, g.index (level+1) (representative c) = c.val)
    (hancestor : ∀ c, g.index base (representative c) = parent)
    (hd : ∀ i ∈ tops, 0 ≤ d i) (hle : base ≤ level)
    (X : cells → EuclideanSpace ℂ κ) (path : cells)
    {gap B K D : ℝ} (hD : 2 ≤ D)
    (hprecision : cutoff/(g.branching:ℝ)^(level+1) ≤ gap/B^2)
    (hspan : g.width base ≤ B*gap)
    (hsignificant : ∀ c, X c ≠ 0 → (c:ℤ) ≠ path.val →
      ∃ i ∈ g.cellTops tops (fun i => (T i).slope) d cutoff (level+1) c.val,
        (T i).radius z ≤ K)
    (hcount : ∀ I : Finset ι, I ⊆ tops →
      (∀ i ∈ I, (T i).radius z ≤ K) →
      (∀ i ∈ I, d i ≤ gap/B^2) →
      (∀ i ∈ I, ∀ j ∈ I, |(T i).slope-(T j).slope| ≤ B*gap) →
      (∀ i ∈ I, ∀ j ∈ I, i ≠ j → gap ≤ |(T i).slope-(T j).slope|) →
      (I.card:ℝ) ≤ D/100) :
    ∀ S : Finset cells, (∀ c ∈ S, X c ≠ 0 ∨ c = path) →
      (S : Set cells).Pairwise (fun c e => ¬g.neighbors (level+1) gap c.val e.val) →
      (S.card:ℝ) ≤ D := by
  classical
  intro S hsupport hindependent
  have h := g.independent_cells_card_le_one_exception tops T d z cutoff base
    (level+1) parent (S.image Subtype.val) path.val hprecision hspan
    (by
      intro c hc
      obtain ⟨c',_,rfl⟩ := Finset.mem_image.mp hc
      have ha := g.cellTops_subset_ancestor tops (fun i => (T i).slope) d cutoff hd
        (hle.trans (Nat.le_succ _)) (representative c')
      simpa only [hcell,hancestor] using ha)
    (by
      intro c hc hne
      obtain ⟨c',hc',rfl⟩ := Finset.mem_image.mp hc
      rcases hsupport c' hc' with hx | he
      · exact hsignificant c' hx hne
      · exact (hne (congrArg Subtype.val he)).elim)
    (by
      intro c hc e he hne
      obtain ⟨c',hc',rfl⟩ := Finset.mem_image.mp hc
      obtain ⟨e',he',rfl⟩ := Finset.mem_image.mp he
      exact hindependent hc' he' (fun h => hne (congrArg Subtype.val h))) hcount
  rw [Finset.card_image_of_injective _ Subtype.val_injective] at h
  linarith

/-- The shrink threshold makes every supported non-path cell eligible for
this count; no significant representative is imposed on a zero amplitude. -/
theorem supported_shrink_significant {ι κ : Type} [DecidableEq ι] [Fintype κ]
    (g : AngularGrid) (tops : Finset ι) (T : ι → SlopeBox) (d : ι → ℝ)
    (z : ℝ × ℝ) (cutoff : ℝ) (level : ℕ) (cells : Finset ℤ)
    (A : cells → EuclideanSpace ℂ κ) (c : cells → ℝ) (path : cells)
    {K ε : ℝ} (hε : 0 ≤ ε) (hc : ∀ i, 0 ≤ c i)
    (hsmall : ∀ j, (∀ i ∈ g.cellTops tops (fun i => (T i).slope) d cutoff level j.val,
      K < (T i).radius z) → ‖A j‖ ≤ 2*ε*c j) :
    ∀ j, (if j = path then A j else radialShrink (2*ε*c j) (A j)) ≠ 0 →
      j.val ≠ path.val →
      ∃ i ∈ g.cellTops tops (fun i => (T i).slope) d cutoff level j.val,
        (T i).radius z ≤ K := by
  classical
  intro j hactive hpath
  have hne : j ≠ path := fun h => hpath (congrArg Subtype.val h)
  rw [ite_eq_right hne] at hactive
  by_contra hnone
  have hsmall' := hsmall j (by
    intro i hi
    exact lt_of_not_ge (fun h => hnone ⟨i,hi,h⟩))
  exact hactive ((radialShrink_eq_zero_iff
    (mul_nonneg (mul_nonneg (by norm_num) hε) (hc j)) (A j)).mpr hsmall')

end LipschitzHilbert.AngularGrid

end

end OAI
