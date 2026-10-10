import OAI.Combinatorics.Ramsey.CycleClique.Construction.Reduction

namespace OAI

/-!
# Expansion inside a minimum-order dense layer subgraph

These are the independent-set deletion calculations in manuscript
Proposition `clq:layer-interface`. Both parity cases are stated: for an
even parameter the order inequality is weak and minimality is strict;
for an odd parameter the order inequality is strict and minimality weak.
-/

namespace CycleClique.Construction
theorem independenceBound_indepNum {V : Type*} [Fintype V] (G : SimpleGraph V) :
    IndependenceBound G G.indepNum := fun _ h => h.card_le_indepNum

theorem indepNum_le_of_independenceBound {V : Type*} [Fintype V]
    {G : SimpleGraph V} {a : ℕ} (h : IndependenceBound G a) : G.indepNum ≤ a := by
  obtain ⟨I, hI⟩ := G.exists_isNIndepSet_indepNum
  have := h I hI.isIndepSet
  simpa [hI.card_eq] using this

private theorem outside_indepNum_bound {V : Type*} [Fintype V]
    {G : SimpleGraph V} {I : Finset V} (hI : G.IsIndepSet (I : Set V)) :
    (G.induce {v | v ∉ closedNeighborhood G I}).indepNum ≤ G.indepNum - I.card := by
  classical
  exact indepNum_le_of_independenceBound
    (independent_outside_bound (independenceBound_indepNum G) hI)

/-- Even-parameter local minimality gives strict neighbourhood expansion
unless the neighbourhood is the entire graph. -/
theorem minimal_dense_expansion_even {V : Type*} [Fintype V]
    {G : SimpleGraph V} {s : ℕ}
    (hdense : s * G.indepNum ≤ Fintype.card V)
    (hminimal : ∀ Y : Finset V, Y.Nonempty → Y.card < Fintype.card V →
      Y.card < s * (G.induce (Y : Set V)).indepNum)
    (I : Finset V) (hI : G.IsIndepSet (I : Set V)) (hne : I.Nonempty) :
    s * I.card ≤ (closedNeighborhood G I).card ∧
      ((closedNeighborhood G I).card < Fintype.card V →
        s * I.card < (closedNeighborhood G I).card) := by
  classical
  let Y : Finset V := Finset.univ \ closedNeighborhood G I
  have hY : (Y : Set V) = {v | v ∉ closedNeighborhood G I} := by ext v; simp [Y]
  have hsum : Y.card + (closedNeighborhood G I).card = Fintype.card V := by
    simpa [Y] using Finset.card_sdiff_add_card_eq_card
      (Finset.subset_univ (closedNeighborhood G I))
  have hIcard := hI.card_le_indepNum
  have houtside : (G.induce (Y : Set V)).indepNum ≤ G.indepNum - I.card := by
    rw [hY]
    exact outside_indepNum_bound hI
  have hmul : s * G.indepNum = s * (G.indepNum - I.card) + s * I.card := by
    rw [← Nat.mul_add, Nat.sub_add_cancel hIcard]
  have hclosedPos : 0 < (closedNeighborhood G I).card := by
    apply Finset.card_pos.mpr
    obtain ⟨v, hv⟩ := hne
    exact ⟨v, subset_closedNeighborhood G I hv⟩
  by_cases hYempty : Y = ∅
  · have hYzero : Y.card = 0 := by simp [hYempty]
    have hmulI : s * I.card ≤ s * G.indepNum := Nat.mul_le_mul_left _ hIcard
    constructor <;> omega
  · have hYne := Finset.nonempty_iff_ne_empty.mpr hYempty
    have hmin := hminimal Y hYne (by omega)
    have hmulR := Nat.mul_le_mul_left s houtside
    constructor <;> omega

/-- Odd-parameter local minimality gives strict neighbourhood expansion
for every nonempty independent set. -/
theorem minimal_dense_expansion_odd {V : Type*} [Fintype V]
    {G : SimpleGraph V} {s : ℕ}
    (hdense : s * G.indepNum < Fintype.card V)
    (hminimal : ∀ Y : Finset V, Y.Nonempty → Y.card < Fintype.card V →
      Y.card ≤ s * (G.induce (Y : Set V)).indepNum)
    (I : Finset V) (hI : G.IsIndepSet (I : Set V)) (hne : I.Nonempty) :
    s * I.card < (closedNeighborhood G I).card := by
  classical
  let Y : Finset V := Finset.univ \ closedNeighborhood G I
  have hY : (Y : Set V) = {v | v ∉ closedNeighborhood G I} := by ext v; simp [Y]
  have hsum : Y.card + (closedNeighborhood G I).card = Fintype.card V := by
    simpa [Y] using Finset.card_sdiff_add_card_eq_card
      (Finset.subset_univ (closedNeighborhood G I))
  have hIcard := hI.card_le_indepNum
  have houtside : (G.induce (Y : Set V)).indepNum ≤ G.indepNum - I.card := by
    rw [hY]
    exact outside_indepNum_bound hI
  have hmul : s * G.indepNum = s * (G.indepNum - I.card) + s * I.card := by
    rw [← Nat.mul_add, Nat.sub_add_cancel hIcard]
  have hclosedPos : 0 < (closedNeighborhood G I).card := by
    apply Finset.card_pos.mpr
    obtain ⟨v, hv⟩ := hne
    exact ⟨v, subset_closedNeighborhood G I hv⟩
  by_cases hYempty : Y = ∅
  · have hYzero : Y.card = 0 := by simp [hYempty]
    have hmulI : s * I.card ≤ s * G.indepNum := Nat.mul_le_mul_left _ hIcard
    omega
  · have hYne := Finset.nonempty_iff_ne_empty.mpr hYempty
    have hmin := hminimal Y hYne (by omega)
    have hmulR := Nat.mul_le_mul_left s houtside
    omega

end CycleClique.Construction

end OAI
