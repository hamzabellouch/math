import OAI.Combinatorics.Ramsey.CycleClique.Construction.Reduction
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace OAI

/-! Combining independent sets in disjoint anticomplete regions. -/

namespace CycleClique.Construction
variable {V ι : Type*}

theorem HasIndependent.mono {G : SimpleGraph V} {m n : ℕ}
    (h : HasIndependent G m) (hnm : n ≤ m) : HasIndependent G n := by
  obtain ⟨f, hf, hadj⟩ := h
  exact ⟨f ∘ Fin.castLE hnm, hf.comp (Fin.castLE_injective hnm),
    fun i j => hadj (Fin.castLE hnm i) (Fin.castLE hnm j)⟩

/-- A labelled independent set in an induced region supplies an actual
ambient finset of exactly the certified weight. -/
theorem exists_independent_subset {G : SimpleGraph V} {Y : Finset V} {n : ℕ}
    (h : HasIndependent (G.induce (Y : Set V)) n) :
    ∃ I : Finset V, I ⊆ Y ∧ G.IsIndepSet (I : Set V) ∧ I.card = n := by
  classical
  obtain ⟨f, hf, hadj⟩ := h
  let g : Fin n → V := fun i => (f i).val
  have hg : Function.Injective g := Subtype.val_injective.comp hf
  refine ⟨Finset.univ.image g, ?_, ?_, ?_⟩
  · intro v hv
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hv
    exact (f i).property
  · intro v hv w hw _
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hw
    exact hadj i j
  · simp [Finset.card_image_of_injective _ hg]

theorem HasIndependent.le_indepNum [Fintype V] {G : SimpleGraph V} {n : ℕ}
    (h : HasIndependent G n) : n ≤ G.indepNum := by
  classical
  obtain ⟨f, hf, hadj⟩ := h
  let I := Finset.univ.image f
  have hI : G.IsIndepSet (I : Set V) := by
    intro x hx y hy _
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hy
    exact hadj i j
  have hc : I.card = n := by simp [I, Finset.card_image_of_injective _ hf]
  simpa [hc] using hI.card_le_indepNum

theorem hasIndependent_iff_le_indepNum [Fintype V] {G : SimpleGraph V} {n : ℕ} :
    HasIndependent G n ↔ n ≤ G.indepNum := by
  classical
  refine ⟨HasIndependent.le_indepNum, fun hn => ?_⟩
  obtain ⟨I, hI⟩ := G.exists_isNIndepSet_indepNum
  have hni : n ≤ I.card := by simpa only [hI.card_eq] using hn
  obtain ⟨J, hJI, hJ⟩ := Finset.exists_subset_card_eq hni
  let e : Fin n ≃ J := (Finset.equivFinOfCardEq hJ).symm
  refine ⟨fun i => (e i).val, Subtype.val_injective.comp e.injective, ?_⟩
  intro i j hadj
  exact hI.isIndepSet (hJI (e i).property) (hJI (e j).property)
    (G.ne_of_adj hadj) hadj

theorem hasIndependent_induce_mono {G : SimpleGraph V} {Y Z : Finset V} {n : ℕ}
    (hYZ : Y ⊆ Z) (h : HasIndependent (G.induce (Y : Set V)) n) :
    HasIndependent (G.induce (Z : Set V)) n := by
  let f : Y → Z := fun v => ⟨v.val, hYZ v.property⟩
  have hf : Function.Injective f := by
    intro a b he
    exact Subtype.ext (congrArg (fun z : Z => z.val) he)
  exact h.map f hf (fun h => h)

theorem hasIndependent_one_of_nonempty {G : SimpleGraph V} {Y : Finset V}
    (hY : Y.Nonempty) : HasIndependent (G.induce (Y : Set V)) 1 := by
  obtain ⟨v, hv⟩ := hY
  exact ⟨fun _ => ⟨v, hv⟩, fun _ _ _ => Subsingleton.elim _ _, fun _ _ h => G.irrefl h⟩

/-- The exact counting step behind both the terminal and finite packing
tests. The regions may have different certified weights. -/
theorem independent_packing [DecidableEq V] {G : SimpleGraph V} {k : ℕ}
    (hbound : IndependenceBound G k) (F : Finset ι) (I : ι → Finset V)
    (hind : ∀ i ∈ F, G.IsIndepSet (I i : Set V))
    (hdis : (F : Set ι).PairwiseDisjoint I)
    (hanti : ∀ i ∈ F, ∀ j ∈ F, i ≠ j → ∀ x ∈ I i, ∀ y ∈ I j, ¬ G.Adj x y) :
    ∑ i ∈ F, (I i).card ≤ k := by
  classical
  have hUnion : G.IsIndepSet ((F.biUnion I : Finset V) : Set V) := by
    intro x hx y hy hxy
    obtain ⟨i, hi, hx⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨j, hj, hy⟩ := Finset.mem_biUnion.mp hy
    by_cases hij : i = j
    · subst j
      exact hind i hi hx hy hxy
    · exact hanti i hi j hj hij x hx y hy
  have hc := hbound (F.biUnion I) hUnion
  simpa only [Finset.card_biUnion hdis] using hc

end CycleClique.Construction

end OAI
