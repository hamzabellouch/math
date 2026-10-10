import OAI.Analysis.LipschitzHilbert.Phase.AngularBoundary
import OAI.Analysis.LipschitzHilbert.Trees.SourceSimultaneousCount

namespace OAI

/-! The simultaneous top count supplies the graph's independence bound. -/

noncomputable section

open Set

namespace LipschitzHilbert.AngularGrid

/-- Select one significant top in each nonempty angular cell. Disjoint
cells make this selection injective, and nonneighbors make its slopes
separated. Thus the previously proved simultaneous list bound applies
to every independent cell collection. -/
theorem independent_cells_card_le {ι : Type*} [DecidableEq ι]
    (g : AngularGrid) (tops : Finset ι) (T : ι → SlopeBox) (d : ι → ℝ)
    (z : ℝ × ℝ) (cutoff : ℝ) (base level : ℕ) (parent : ℤ)
    (cells : Finset ℤ) {rho B K D : ℝ}
    (hprecision : cutoff / (g.branching : ℝ) ^ level ≤ rho / B ^ 2)
    (hspan : g.width base ≤ B * rho)
    (hancestor : ∀ c ∈ cells,
      g.cellTops tops (fun i => (T i).slope) d cutoff level c ⊆
        g.cellTops tops (fun i => (T i).slope) d cutoff base parent)
    (hsignificant : ∀ c ∈ cells, ∃ i ∈ g.cellTops tops (fun i => (T i).slope) d cutoff level c,
      (T i).radius z ≤ K)
    (hindependent : (cells : Set ℤ).Pairwise (fun c e => ¬g.neighbors level rho c e))
    (hcount : ∀ I : Finset ι, I ⊆ tops →
      (∀ i ∈ I, (T i).radius z ≤ K) →
      (∀ i ∈ I, d i ≤ rho / B ^ 2) →
      (∀ i ∈ I, ∀ j ∈ I, |(T i).slope - (T j).slope| ≤ B * rho) →
      (∀ i ∈ I, ∀ j ∈ I, i ≠ j → rho ≤ |(T i).slope - (T j).slope|) →
      (I.card : ℝ) ≤ D) : (cells.card : ℝ) ≤ D := by
  classical
  choose rep hrep hsig using fun c : cells => hsignificant c.val c.property
  have hindex (c : cells) : g.index level (T (rep c)).slope = c.val :=
    ((g.mem_cellTops _ _ _ _ _ _ _).mp (hrep c)).2.1
  have hbase (c : cells) : g.index base (T (rep c)).slope = parent :=
    ((g.mem_cellTops _ _ _ _ _ _ _).mp (hancestor c.val c.property (hrep c))).2.1
  have hinj : Function.Injective rep := by
    intro c e h
    apply Subtype.ext
    rw [← hindex c, ← hindex e, h]
  let I : Finset ι := Finset.univ.image rep
  have hmem {i : ι} (hi : i ∈ I) : ∃ c : cells, rep c = i := by
    obtain ⟨c, _, hc⟩ := Finset.mem_image.mp hi
    exact ⟨c, hc⟩
  have hcard : I.card = cells.card := by
    change (Finset.univ.image rep).card = cells.card
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_coe]
  rw [← hcard]
  apply hcount I
  · intro i hi
    obtain ⟨c, rfl⟩ := hmem hi
    exact ((g.mem_cellTops _ _ _ _ _ _ _).mp (hrep c)).1
  · intro i hi
    obtain ⟨c, rfl⟩ := hmem hi
    exact hsig c
  · intro i hi
    obtain ⟨c, rfl⟩ := hmem hi
    exact ((g.eligible_iff_precision_le cutoff (d (rep c)) level).mp
      ((g.mem_cellTops _ _ _ _ _ _ _).mp (hrep c)).2.2).trans hprecision
  · intro i hi j hj
    obtain ⟨c, rfl⟩ := hmem hi
    obtain ⟨e, rfl⟩ := hmem hj
    exact (g.same_cell_diameter base ((hbase c).trans (hbase e).symm)).trans hspan
  · intro i hi j hj hij
    obtain ⟨c, rfl⟩ := hmem hi
    obtain ⟨e, rfl⟩ := hmem hj
    have hne : c.val ≠ e.val := fun h => hij (congrArg rep (Subtype.ext h))
    have hfar := hindependent c.property e.property hne
    apply g.slopes_separated_of_not_neighbors level rho
    simpa only [hindex c, hindex e] using hfar

end LipschitzHilbert.AngularGrid

end

end OAI
