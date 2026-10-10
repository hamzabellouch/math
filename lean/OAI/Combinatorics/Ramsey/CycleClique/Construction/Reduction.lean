import OAI.Combinatorics.Ramsey.CycleClique.Construction.Definitions

namespace OAI

/-!
# Minimal-counterexample deletion and expansion

The argument is Section 2 of *Cycle--clique Ramsey numbers*. The hypothesis
on smaller independence parameters is an induction hypothesis, not a new
published input and not a substitute for the upper-bound theorem.
-/

namespace CycleClique.Construction
variable {V : Type*} [Fintype V]

/-- Every independent set has at most `a` vertices. -/
def IndependenceBound (G : SimpleGraph V) (a : ℕ) : Prop :=
  ∀ I : Finset V, G.IsIndepSet (I : Set V) → I.card ≤ a

/-- The union of an independent set and all of its neighbours. -/
noncomputable def closedNeighborhood (G : SimpleGraph V) (I : Finset V) : Finset V := by
  classical
  exact Finset.univ.filter fun v => v ∈ I ∨ ∃ i ∈ I, G.Adj i v

@[simp] theorem mem_closedNeighborhood {G : SimpleGraph V} {I : Finset V} {v : V} :
    v ∈ closedNeighborhood G I ↔ v ∈ I ∨ ∃ i ∈ I, G.Adj i v := by
  classical
  simp [closedNeighborhood]

theorem subset_closedNeighborhood (G : SimpleGraph V) (I : Finset V) :
    I ⊆ closedNeighborhood G I := by
  intro v hv
  exact mem_closedNeighborhood.mpr (Or.inl hv)

omit [Fintype V] in
theorem independenceBound_iff_not_hasIndependent {G : SimpleGraph V} {a : ℕ} :
    IndependenceBound G a ↔ ¬ HasIndependent G (a + 1) := by
  classical
  constructor
  · intro h ⟨f, hf, he⟩
    let I := Finset.univ.image f
    have hI : G.IsIndepSet (I : Set V) := by
      intro x hx y hy _
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hy
      exact he i j
    have hcard : I.card = a + 1 := by
      simp [I, Finset.card_image_of_injective _ hf]
    have := h I hI
    omega
  · intro h I hI
    by_contra hn
    obtain ⟨J, hJI, hJ⟩ := Finset.exists_subset_card_eq (show a + 1 ≤ I.card by omega)
    let e : Fin (a + 1) ≃ J := (Finset.equivFinOfCardEq hJ).symm
    apply h
    refine ⟨fun i => (e i).val, Subtype.val_injective.comp e.injective, ?_⟩
    intro i j hij
    have hne : (e i).val ≠ (e j).val := G.ne_of_adj hij
    exact hI (hJI (e i).property) (hJI (e j).property) hne hij

/-- The part of an independent set outside its closed neighbourhood is
anticomplete to it, so independent sets in the remainder can be adjoined. -/
theorem independent_union_outside [DecidableEq V] {G : SimpleGraph V} {I J : Finset V}
    (hI : G.IsIndepSet (I : Set V)) (hJ : G.IsIndepSet (J : Set V))
    (hout : ∀ v ∈ J, v ∉ closedNeighborhood G I) :
    G.IsIndepSet ((I ∪ J : Finset V) : Set V) := by
  classical
  intro x hx y hy hxy
  rcases Finset.mem_union.mp hx with hx | hx <;>
    rcases Finset.mem_union.mp hy with hy | hy
  · exact hI hx hy hxy
  · intro hadj
    exact hout y hy (mem_closedNeighborhood.mpr (Or.inr ⟨x, hx, hadj⟩))
  · intro hadj
    exact hout x hx (mem_closedNeighborhood.mpr (Or.inr ⟨y, hy, hadj.symm⟩))
  · exact hJ hx hy hxy

theorem independent_outside_bound {G : SimpleGraph V} {a : ℕ}
    (hG : IndependenceBound G a) {I : Finset V}
    (hI : G.IsIndepSet (I : Set V)) :
    IndependenceBound (G.induce {v | v ∉ closedNeighborhood G I}) (a - I.card) := by
  classical
  intro J hJ
  let J' : Finset V := J.map ⟨Subtype.val, Subtype.val_injective⟩
  have hJ' : G.IsIndepSet (J' : Set V) := by
    intro x hx y hy hxy
    obtain ⟨x', hx', rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨y', hy', rfl⟩ := Finset.mem_map.mp hy
    exact hJ hx' hy' (fun he => hxy (congrArg Subtype.val he))
  have hout : ∀ v ∈ J', v ∉ closedNeighborhood G I := by
    intro v hv
    obtain ⟨v', _, rfl⟩ := Finset.mem_map.mp hv
    exact v'.property
  have hdis : Disjoint I J' := by
    apply Finset.disjoint_left.mpr
    intro v hvI hvJ
    exact hout v hvJ (subset_closedNeighborhood G I hvI)
  have hbound := hG (I ∪ J') (independent_union_outside hI hJ' hout)
  rw [Finset.card_union_of_disjoint hdis, Finset.card_map] at hbound
  omega

/-- Independent-set expansion from the smaller-parameter extremal bounds.
This is manuscript Lemma `red:expansion`, with its minimality premise explicit. -/
theorem minimal_counterexample_expansion {G : SimpleGraph V} {k a : ℕ}
    (hcard : Fintype.card V = k * a + 1)
    (hcycle : ¬ HasCycle G (k + 1)) (hbound : IndependenceBound G a)
    (hsmall : ∀ (b : ℕ), b < a →
      ∀ (Y : Finset V),
        ¬ HasCycle (G.induce (Y : Set V)) (k + 1) →
        IndependenceBound (G.induce (Y : Set V)) b → Y.card ≤ k * b)
    (I : Finset V) (hI : G.IsIndepSet (I : Set V)) (hne : I.Nonempty) :
    k * I.card + 1 ≤ (closedNeighborhood G I).card := by
  classical
  let Y := Finset.univ \ closedNeighborhood G I
  have hY : (Y : Set V) = {v | v ∉ closedNeighborhood G I} := by
    ext v
    simp [Y]
  have hb : a - I.card < a := by
    have := hbound I hI
    have := Finset.card_pos.mpr hne
    omega
  have hcyY : ¬ HasCycle (G.induce (Y : Set V)) (k + 1) := by
    intro h
    exact hcycle (h.map Subtype.val Subtype.val_injective (fun h => h))
  have hindY : IndependenceBound (G.induce (Y : Set V)) (a - I.card) := by
    rw [hY]
    exact independent_outside_bound hbound hI
  have hs := hsmall (a - I.card) hb Y hcyY hindY
  have hsum : Y.card + (closedNeighborhood G I).card = k * a + 1 := by
    have h := Finset.card_sdiff_add_card_eq_card
      (Finset.subset_univ (closedNeighborhood G I))
    simpa [Y, hcard] using h
  have hi := hbound I hI
  have hmul : k * a = k * (a - I.card) + k * I.card := by
    rw [← Nat.mul_add, Nat.sub_add_cancel hi]
  omega

end CycleClique.Construction

end OAI
