import Mathlib
import OAI.Combinatorics.Ramsey.CycleClique.DenseCycles
import OAI.Combinatorics.Ramsey.CycleClique.Independence
import OAI.Combinatorics.Ramsey.CycleClique.IndependenceTwo

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem cycleGraph_adj_succ {n : ℕ} [NeZero n] (hn : 2 ≤ n) {a b : Fin n} :
    (SimpleGraph.cycleGraph n).Adj a b ↔ a = b + 1 ∨ b = a + 1 := by
  obtain ⟨n, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  rw [SimpleGraph.cycleGraph_adj, sub_eq_iff_eq_add, sub_eq_iff_eq_add]
  simp only [add_comm]

theorem contains_cycle_of_labels {V : Type*} {G : SimpleGraph V}
    {n : ℕ} [NeZero n] (hn : 2 ≤ n) (f : Fin n → V) (hf : Function.Injective f)
    (hstep : ∀ i, G.Adj (f i) (f (i + 1))) : SimpleGraph.cycleGraph n ⊑ G := by
  refine ⟨⟨⟨f, ?_⟩, hf⟩⟩
  intro a b hab
  rcases (cycleGraph_adj_succ hn).mp hab with rfl | rfl
  · exact (hstep b).symm
  · exact hstep a

theorem fin_add_one_val {n : ℕ} [NeZero n] (hn : 2 ≤ n) (i : Fin n) :
    (i + 1).val = if i.val + 1 = n then 0 else i.val + 1 := by
  simp only [Fin.val_add, Fin.val_one', Nat.mod_eq_of_lt (by omega : 1 < n)]
  split_ifs with h
  · simp [h]
  · rw [Nat.mod_eq_of_lt (by omega)]

 
def bypassIndex {n : ℕ} (hn : 3 ≤ n) (i : Fin (n - 1)) : Fin n :=
  ⟨if i.val = 0 then 0 else i.val + 1, by split_ifs <;> omega⟩

theorem bypassIndex_injective {n : ℕ} (hn : 3 ≤ n) :
    Function.Injective (bypassIndex hn) := by
  intro i j hij
  have hh := congrArg Fin.val hij
  simp only [bypassIndex] at hh
  apply Fin.ext
  split_ifs at hh <;> omega

theorem bypassIndex_step {n : ℕ} [NeZero n] [NeZero (n - 1)] (hn : 3 ≤ n)
    (i : Fin (n - 1)) :
    (bypassIndex hn i = 0 ∧ bypassIndex hn (i + 1) = 2) ∨
      bypassIndex hn (i + 1) = bypassIndex hn i + 1 := by
  have hval := fin_add_one_val (by omega : 2 ≤ n - 1) i
  by_cases hi : i.val = 0
  · left
    constructor <;> apply Fin.ext
    · simp [bypassIndex, hi]
    · have hi1 : (i + 1).val = 1 := by rw [hval]; split_ifs <;> omega
      simp [bypassIndex, hi1, Nat.mod_eq_of_lt (by omega : 2 < n)]
  · right
    apply Fin.ext
    rw [fin_add_one_val (by omega) (bypassIndex hn i)]
    simp only [bypassIndex]
    rw [hval]
    split_ifs <;> omega

 
def fourStepIndex {n : ℕ} (hn : 7 ≤ n) (i : Fin (n - 1)) : Fin n :=
  ⟨if i.val < n - 6 then i.val + 1 else
    if i.val < n - 4 then i.val + 4 else i.val - 1,
    by split_ifs <;> omega⟩

theorem fourStepIndex_injective {n : ℕ} (hn : 7 ≤ n) :
    Function.Injective (fourStepIndex hn) := by
  intro i j hij
  have hh := congrArg Fin.val hij
  simp only [fourStepIndex] at hh
  apply Fin.ext
  split_ifs at hh <;> omega

theorem fourStepIndex_step {n : ℕ} [NeZero n] [NeZero (n - 1)] (hn : 7 ≤ n)
    (i : Fin (n - 1)) :
    fourStepIndex hn (i + 1) = fourStepIndex hn i + 1 ∨
      fourStepIndex hn (i + 1) = fourStepIndex hn i + 4 ∨
      fourStepIndex hn i = fourStepIndex hn (i + 1) + 4 := by
  have hval := fin_add_one_val (by omega : 2 ≤ n - 1) i
  have h1 : 1 % n = 1 := Nat.mod_eq_of_lt (by omega)
  have h4 : 4 % n = 4 := Nat.mod_eq_of_lt (by omega)
  have h1' : (1 : Fin n).val = 1 := by rw [Fin.val_one', h1]
  have h4' : (4 : Fin n).val = 4 := h4
  simp only [Fin.ext_iff, Fin.val_add, h1', h4', fourStepIndex, hval]
  split_ifs <;> simp_all only [ite_false, ite_true]
  all_goals first
    | (left; rw [Nat.mod_eq_of_lt (by omega)] <;> omega)
    | (right; left; rw [Nat.mod_eq_of_lt (by omega)])
    | (right; right; rw [Nat.mod_eq_of_lt (by omega)]; omega)
    | (right; left; rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]; omega)

 
theorem fin_ne_add_step {n : ℕ} [NeZero n] (i : Fin n) (d : ℕ)
    (hd : 0 < d) (hdn : d < n) : i ≠ i + Fin.ofNat n d := by
  intro he
  have hh : (0 : Fin n) = Fin.ofNat n d := add_left_cancel (show i + 0 = i + Fin.ofNat n d by
    simpa only [add_zero] using he)
  have hv := congrArg Fin.val hh
  simp only [Fin.val_zero, Fin.val_ofNat, Nat.mod_eq_of_lt hdn] at hv
  omega

 

theorem shorten_cycle {V : Type*} [Fintype V] {G : SimpleGraph V}
    (hα : G.indepNum ≤ 2) {n : ℕ} (hn : 7 ≤ n)
    (hc : SimpleGraph.cycleGraph n ⊑ G) : SimpleGraph.cycleGraph (n - 1) ⊑ G := by
  classical
  let : NeZero n := ⟨by omega⟩
  let : NeZero (n - 1) := ⟨by omega⟩
  obtain ⟨f⟩ := hc
  have h22 : (2 : Fin n) + 2 = 4 := by
    apply Fin.ext
    change (2 % n + 2 % n) % n = 4 % n
    simp only [Nat.mod_eq_of_lt (by omega : 2 < n)]
  have hstep : ∀ i : Fin n, G.Adj (f i) (f (i + 1)) := by
    intro i
    exact f.toHom.map_adj ((cycleGraph_adj_succ (by omega)).mpr (Or.inr rfl))
  by_cases hchord : ∃ i : Fin n, G.Adj (f i) (f (i + 2))
  · obtain ⟨i, hi⟩ := hchord
    let g : Fin (n - 1) → V := fun j => f (i + bypassIndex (by omega : 3 ≤ n) j)
    apply contains_cycle_of_labels (by omega) g
    · intro a b hab
      exact bypassIndex_injective (by omega) (add_left_cancel (f.injective hab))
    · intro j
      rcases bypassIndex_step (by omega : 3 ≤ n) j with ⟨hj, hj'⟩ | hj
      · simpa only [g, hj, hj', add_zero] using hi
      · simpa only [g, hj, ← add_assoc] using hstep (i + bypassIndex (by omega) j)
  · push Not at hchord
    have hfour : ∀ i : Fin n, G.Adj (f i) (f (i + 4)) := by
      intro i
      have h02 : i ≠ i + 2 := fin_ne_add_step i 2 (by omega) (by omega)
      have h04 : i ≠ i + 4 := fin_ne_add_step i 4 (by omega) (by omega)
      have h24 : i + 2 ≠ i + 4 := by
        have hn24 := fin_ne_add_step (i + 2) 2 (by omega) (by omega)
        change i + 2 ≠ i + 2 + 2 at hn24
        simpa only [add_assoc, h22] using hn24
      apply alpha_two_adj hα (z := f (i + 2))
      · exact fun hh => h04 (f.injective hh)
      · exact fun hh => h02 (f.injective hh)
      · exact fun hh => h24 (f.injective hh).symm
      · exact hchord i
      · intro hh
        apply hchord (i + 2)
        simpa only [add_assoc, h22] using hh.symm
    apply contains_cycle_of_labels (by omega) (fun j => f (fourStepIndex hn j))
    · exact f.injective.comp (fourStepIndex_injective hn)
    · intro j
      rcases fourStepIndex_step hn j with hj | hj | hj
      · rw [hj]; exact hstep _
      · rw [hj]; exact hfour _
      · rw [hj]; exact (hfour _).symm

 
theorem cycle_of_alpha_two_long_cycle {V : Type*} [Fintype V] {G : SimpleGraph V}
    (hα : G.indepNum ≤ 2) {k : ℕ} (hk : 6 ≤ k) :
    ∀ n, k ≤ n → SimpleGraph.cycleGraph n ⊑ G → SimpleGraph.cycleGraph k ⊑ G := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hkn hc
    by_cases he : k = n
    · rw [he]; exact hc
    · exact ih (n - 1) (by omega) (by omega) (shorten_cycle hα (by omega) hc)

 
theorem size_test {V : Type*} [Fintype V] {G : SimpleGraph V}
    {k t : ℕ} (hk : 5 ≤ k) (_ht : 1 ≤ t)
    (hcycle : ¬ SimpleGraph.cycleGraph (k + 1) ⊑ G) (hclique : G.cliqueNum ≤ t)
    (Y : Set V) (hY : max k (2 * t) < Y.ncard) : 3 ≤ independence G Y := by
  classical
  by_contra hn
  have hα : (G.induce Y).indepNum ≤ 2 := by change independence G Y ≤ 2; omega
  have hcY : (G.induce Y).cliqueNum ≤ t := by
    by_contra hh
    have hc := (complete_isContained_iff_le_cliqueNum (G.induce Y) (t + 1)).mpr (by omega)
    have hc' := (complete_isContained_iff_le_cliqueNum G (t + 1)).mp
      (hc.trans (SimpleGraph.Embedding.induce Y).isContained)
    omega
  have hcard : max k (2 * t) < Fintype.card Y := by
    rwa [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
  have hconn := connected_of_alpha_two_large hα hcY (by omega)
  have hdel := deletion_connected_of_alpha_two_large hα hcY (by omega)
  obtain ⟨x, c, hc, hlen⟩ := hamiltonian_of_alpha_two hconn (by omega) hα hdel
  have hlong : SimpleGraph.cycleGraph (Fintype.card Y) ⊑ G.induce Y :=
    (SimpleGraph.cycleGraph_isContained_iff (by omega)).mpr ⟨x, c, hc, hlen⟩
  have hshort := cycle_of_alpha_two_long_cycle hα (by omega : 6 ≤ k + 1)
    (Fintype.card Y) (by omega) hlong
  exact hcycle (hshort.trans (SimpleGraph.Embedding.induce Y).isContained)

 

abbrev exteriorEdges {V : Type*} (G : SimpleGraph V) (X : Set V) : SimpleGraph V where
  Adj u v := G.Adj u v ∧ (u ∉ X ∨ v ∉ X)
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1.ne rfl⟩

end CycleClique

end OAI
