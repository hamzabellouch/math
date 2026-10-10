import Mathlib
import OAI.Combinatorics.Ramsey.CycleClique.Basic
import OAI.Combinatorics.Ramsey.CycleClique.Independence
import OAI.Combinatorics.Ramsey.CycleClique.LowerBound

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem ramsey_upper_zero (k : ℕ) : RamseyProperty (k + 1) 1 1 := by
  intro G
  right
  refine ⟨⟨⟨id, ?_⟩, Function.injective_id⟩⟩
  intro a b hab
  exact False.elim (hab (Subsingleton.elim a b))

theorem ramsey_upper_one (k : ℕ) : RamseyProperty (k + 1) 2 (k + 1) := by
  classical
  intro G
  by_cases hblue : (⊤ : SimpleGraph (Fin 2)) ⊑ Gᶜ
  · exact Or.inr hblue
  left
  have hi := (no_compl_clique_iff G 1).mp hblue
  have htop : ∀ a b, a ≠ b → G.Adj a b := by
    intro a b hab
    by_contra hn
    have hI : G.IsIndepSet {a, b} := by
      intro x hx y hy hxy hxyadj
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
      · exact hxy rfl
      · exact hn hxyadj
      · exact hn hxyadj.symm
      · exact hxy rfl
    have hc := indep_ncard_le hI
    rw [Set.ncard_pair hab] at hc
    omega
  exact ⟨⟨⟨id, fun {a b} hab => htop a b hab.ne⟩, Function.injective_id⟩⟩

 

theorem order_bound_from_ramsey {V : Type*} [Fintype V] {G : SimpleGraph V}
    {k b : ℕ} (hR : RamseyProperty (k + 1) (b + 1) (k * b + 1))
    (hcycle : ¬ SimpleGraph.cycleGraph (k + 1) ⊑ G) (hα : G.indepNum ≤ b) :
    Fintype.card V ≤ k * b := by
  by_contra hn
  rcases hR.on_fintype (by omega) G with hc | hb
  · exact hcycle hc
  · exact (no_compl_clique_iff G b).mpr hα hb

 
theorem expansion_of_minimality {k a : ℕ} (G : SimpleGraph (Fin (k * a + 1)))
    (hcycle : ¬ SimpleGraph.cycleGraph (k + 1) ⊑ G) (hα : G.indepNum ≤ a)
    (hprevious : ∀ b < a, RamseyProperty (k + 1) (b + 1) (k * b + 1))
    {I : Set (Fin (k * a + 1))} (hI : G.IsIndepSet I) (hne : I.Nonempty) :
    k * I.ncard + 1 ≤ (closedNeighborhood G I).ncard := by
  classical
  have hr : 0 < I.ncard := (Set.ncard_pos).mpr hne
  have hrle : I.ncard ≤ a := (indep_ncard_le hI).trans hα
  let S := (closedNeighborhood G I)ᶜ
  have hprev := hprevious (a - I.ncard) (by omega)
  have hbound := independence_outside_closed hI (Set.subset_univ I)
  rw [independence_univ] at hbound
  have hαS : (G.induce S).indepNum ≤ a - I.ncard := by
    have heq : Set.univ \ closedNeighborhood G I = S := (Set.compl_eq_univ_sdiff _).symm
    rw [heq] at hbound
    change independence G S ≤ a - I.ncard
    omega
  have hcS : ¬ SimpleGraph.cycleGraph (k + 1) ⊑ G.induce S := by
    intro hc
    exact hcycle (hc.trans (SimpleGraph.Embedding.induce S).isContained)
  have hc := order_bound_from_ramsey hprev hcS hαS
  rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq] at hc
  have hsum := Set.ncard_add_ncard_compl (closedNeighborhood G I)
  rw [Nat.card_eq_fintype_card, Fintype.card_fin] at hsum
  have hmul : k * (a - I.ncard) + k * I.ncard = k * a := by
    rw [← Nat.mul_add, Nat.sub_add_cancel hrle]
  change S.ncard ≤ k * (a - I.ncard) at hc
  change (closedNeighborhood G I).ncard + S.ncard = k * a + 1 at hsum
  omega

 

theorem minimal_expanding_counterexample {k a₀ : ℕ} (ha₀ : 2 ≤ a₀) (ha₀k : a₀ ≤ k)
    (hfailure : ¬ RamseyProperty (k + 1) (a₀ + 1) (k * a₀ + 1)) :
    ∃ a, 2 ≤ a ∧ a ≤ k ∧ ∃ G : SimpleGraph (Fin (k * a + 1)),
      (¬ SimpleGraph.cycleGraph (k + 1) ⊑ G) ∧ G.indepNum ≤ a ∧
      ∀ I, G.IsIndepSet I → I.Nonempty → k * I.ncard + 1 ≤ (closedNeighborhood G I).ncard := by
  classical
  let A : Set ℕ := {a | 2 ≤ a ∧ a ≤ k ∧
    ¬ RamseyProperty (k + 1) (a + 1) (k * a + 1)}
  have hA : A.Nonempty := ⟨a₀, ha₀, ha₀k, hfailure⟩
  let a := sInf A
  have hamin : a ∈ A := Nat.sInf_mem hA
  obtain ⟨ha, hak, hfail⟩ := hamin
  have hprev : ∀ b < a, RamseyProperty (k + 1) (b + 1) (k * b + 1) := by
    intro b hba
    rcases b with _ | b
    · simpa using ramsey_upper_zero k
    rcases b with _ | b
    · simpa using ramsey_upper_one k
    by_contra hn
    have hbA : b + 2 ∈ A := ⟨by omega, by omega, hn⟩
    have := Nat.sInf_le hbA
    change a ≤ b + 2 at this
    omega
  unfold RamseyProperty at hfail
  obtain ⟨G, hn⟩ := not_forall.mp hfail
  obtain ⟨hcycle, hblue⟩ := not_or.mp hn
  have hα := (no_compl_clique_iff G a).mp hblue
  exact ⟨a, ha, hak, G, hcycle, hα,
    fun I hI hne => expansion_of_minimality G hcycle hα hprev hI hne⟩

end CycleClique

end OAI
