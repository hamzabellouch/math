import Mathlib
import OAI.Combinatorics.Ramsey.CycleClique.Basic
import OAI.Combinatorics.Ramsey.CycleClique.ColouredPaths
import OAI.Combinatorics.Ramsey.CycleClique.Exceptional
import OAI.Combinatorics.Ramsey.CycleClique.Independence
import OAI.Combinatorics.Ramsey.CycleClique.InducedGraphs

namespace OAI

namespace CycleClique
open scoped SimpleGraph

def MinimalDensity {V : Type*} (G : SimpleGraph V) (s ε : ℕ) : Prop :=
  (s * G.indepNum + ε ≤ Nat.card V) ∧
  ∀ T : Set V, T.Nonempty → T.ncard < Nat.card V →
    T.ncard < s * independence G T + ε

 
theorem minimal_density_connected {V : Type*} [Fintype V] [Nonempty V]
    {G : SimpleGraph V} {s ε : ℕ} (hε : ε ≤ 1) (hdense : MinimalDensity G s ε) :
    G.Connected := by
  classical
  simp only [MinimalDensity, Nat.card_eq_fintype_card] at hdense
  obtain ⟨r⟩ := ‹Nonempty V›
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨r, fun w => ?_⟩
  by_contra hw
  let A : Set V := {v | G.Reachable r v}
  have hrA : r ∈ A := SimpleGraph.Reachable.refl r
  have hwA : w ∈ Aᶜ := hw
  have hsum := Set.ncard_add_ncard_compl A
  rw [Nat.card_eq_fintype_card] at hsum
  have hApos : 0 < A.ncard := (Set.ncard_pos).mpr ⟨r, hrA⟩
  have hBpos : 0 < Aᶜ.ncard := (Set.ncard_pos).mpr ⟨w, hwA⟩
  have hA := hdense.2 A ⟨r, hrA⟩ (by omega)
  have hB := hdense.2 Aᶜ ⟨w, hwA⟩ (by omega)
  have hα := independence_add_le (G := G) (Set.subset_univ A) (Set.subset_univ Aᶜ)
    disjoint_compl_right (by
      intro a ha b hb hab
      exact hb (ha.trans hab.reachable))
  rw [independence_univ] at hα
  have hmul := Nat.mul_le_mul_left s hα
  have hd := hdense.1
  nlinarith

 

theorem minimal_density_expansion {V : Type*} [Fintype V] {G : SimpleGraph V}
    {s ε : ℕ} (hdense : MinimalDensity G s ε)
    {I : Set V} (hI : G.IsIndepSet I) (hne : I.Nonempty) :
    s * I.ncard ≤ (closedNeighborhood G I).ncard ∧
    ((0 < ε ∨ (closedNeighborhood G I)ᶜ.Nonempty) →
      s * I.ncard < (closedNeighborhood G I).ncard) := by
  classical
  simp only [MinimalDensity, Nat.card_eq_fintype_card] at hdense
  let N := closedNeighborhood G I
  have hNpos : 0 < N.ncard := (Set.ncard_pos).mpr (hne.mono (fun _ h => Or.inl h))
  have hsum := Set.ncard_add_ncard_compl N
  rw [Nat.card_eq_fintype_card] at hsum
  have hα := independence_outside_closed hI (Set.subset_univ I)
  rw [independence_univ, ← Set.compl_eq_univ_sdiff] at hα
  have hm := Nat.mul_le_mul_left s hα
  have hd := hdense.1
  by_cases hR : Nᶜ.Nonempty
  · have hr := hdense.2 Nᶜ hR (by omega)
    have hstrict : s * I.ncard < N.ncard := by nlinarith
    exact ⟨hstrict.le, fun _ => hstrict⟩
  · have hRcard : Nᶜ.ncard = 0 := (Set.ncard_eq_zero).mpr (Set.not_nonempty_iff_eq_empty.mp hR)
    refine ⟨?_, ?_⟩
    · nlinarith
    · rintro (he | hn)
      · nlinarith
      · exact False.elim (hR hn)

 
theorem exists_minimal_density {V : Type*} [Fintype V] (G : SimpleGraph V)
    (s ε : ℕ) {D : Set V} (hne : D.Nonempty)
    (hd : s * independence G D + ε ≤ D.ncard) :
    ∃ S ⊆ D, S.Nonempty ∧ MinimalDensity (G.induce S) s ε := by
  classical
  let A : Set ℕ := {n | ∃ S ⊆ D, S.Nonempty ∧
    s * independence G S + ε ≤ S.ncard ∧ S.ncard = n}
  have hA : A.Nonempty := ⟨D.ncard, D, Set.Subset.rfl, hne, hd, rfl⟩
  obtain ⟨S, hSD, hS, hdS, hcS⟩ := Nat.sInf_mem hA
  refine ⟨S, hSD, hS, ?_, ?_⟩
  · simpa [independence, ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq] using hdS
  · intro T hT hlt
    by_contra hn
    have him : Subtype.val '' T ⊆ D := by
      rintro x ⟨y, hy, rfl⟩
      exact hSD y.property
    have hcard : (Subtype.val '' T).ncard = T.ncard :=
      Set.ncard_image_of_injective _ Subtype.val_injective
    have hm : (Subtype.val '' T).ncard ∈ A := by
      refine ⟨Subtype.val '' T, him, hT.image _, ?_, rfl⟩
      rw [← independence_induce_image, hcard]
      omega
    have hmin := Nat.sInf_le hm
    rw [hcard, ← hcS] at hmin
    have hSc : S.ncard = Nat.card S := (Nat.card_coe_set_eq S).symm
    omega

 
theorem minimal_density_indep_ge_two {V : Type*} [Fintype V] [Nonempty V]
    {G : SimpleGraph V} {s ε : ℕ} (hd : MinimalDensity G s ε)
    (hfree : ¬ (⊤ : SimpleGraph (Fin s)) ⊑ G) : 2 ≤ G.indepNum := by
  classical
  have hpos : 0 < G.indepNum := by
    simpa [independence_univ] using
      (independence_pos (G := G) (S := Set.univ) Set.univ_nonempty)
  by_contra hn
  have ha : G.indepNum = 1 := by omega
  have hcl : G.IsClique Set.univ := clique_of_independence_le_one (by
    rw [independence_univ, ha])
  have hlt := clique_ncard_lt hfree hcl
  rw [Set.ncard_univ, Nat.card_eq_fintype_card] at hlt
  have hc := hd.1
  rw [ha, Nat.mul_one, Nat.card_eq_fintype_card] at hc
  omega

 

theorem minimal_density_properties {V : Type*} [Fintype V] [Nonempty V]
    {G : SimpleGraph V} {s ε : ℕ} [DecidableRel G.Adj] (hs : 4 ≤ s) (hε : ε ≤ 1)
    (hd : MinimalDensity G s ε) (hfree : ¬ (⊤ : SimpleGraph (Fin s)) ⊑ G) :
    G.Connected ∧ ¬ G.IsBipartite ∧ 2 * s + ε ≤ Fintype.card V ∧
    (∀ v, s ≤ G.degree v) ∧
    (∀ I, G.IsIndepSet I → I.Nonempty →
      s * I.ncard ≤ (closedNeighborhood G I).ncard ∧
      ((0 < ε ∨ (closedNeighborhood G I)ᶜ.Nonempty) →
        s * I.ncard < (closedNeighborhood G I).ncard)) := by
  classical
  have hcV : Nat.card V = Fintype.card V := Nat.card_eq_fintype_card
  have hα := minimal_density_indep_ge_two hd hfree
  have horder : 2 * s + ε ≤ Fintype.card V := by
    have := hd.1
    nlinarith
  refine ⟨minimal_density_connected hε hd, ?_, horder, ?_,
    fun I hI hne => minimal_density_expansion hd hI hne⟩
  · intro hbip
    have hupper := bipartite_card_le_twice_indep hbip
    have hlower := hd.1
    nlinarith
  · intro v
    have hexp := minimal_density_expansion hd
      (show G.IsIndepSet {v} from Set.pairwise_singleton _ _) (Set.singleton_nonempty v)
    simp only [Set.ncard_singleton, Nat.mul_one, closedNeighborhood_singleton_card] at hexp
    by_cases hR : (closedNeighborhood G {v})ᶜ.Nonempty
    · have := hexp.2 (Or.inr hR)
      omega
    · have hN : closedNeighborhood G {v} = Set.univ := by
        apply Set.eq_univ_of_forall
        intro w
        by_contra hw
        exact hR ⟨w, hw⟩
      have hc := closedNeighborhood_singleton_card G v
      rw [hN, Set.ncard_univ, Nat.card_eq_fintype_card] at hc
      omega

end CycleClique

end OAI
