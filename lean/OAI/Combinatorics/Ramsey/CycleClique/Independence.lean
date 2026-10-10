import Mathlib
import OAI.Combinatorics.Ramsey.CycleClique.Basic
import OAI.Combinatorics.Ramsey.CycleClique.ColouredPaths

namespace OAI

namespace CycleClique
open scoped SimpleGraph

noncomputable def independence {V : Type*} (G : SimpleGraph V) (S : Set V) : ℕ :=
  (G.induce S).indepNum

theorem indep_ncard_le {V : Type*} [Fintype V] {G : SimpleGraph V}
    {I : Set V} (hI : G.IsIndepSet I) : I.ncard ≤ G.indepNum := by
  classical
  have hc := (show G.IsIndepSet (I.toFinset : Set V) by simpa using hI).card_le_indepNum
  rwa [← Set.ncard_eq_toFinset_card'] at hc

theorem exists_indep_of_independence {V : Type*} [Fintype V] (G : SimpleGraph V)
    (S : Set V) : ∃ I ⊆ S, G.IsIndepSet I ∧ I.ncard = independence G S := by
  classical
  obtain ⟨J, hJ⟩ := (G.induce S).exists_isNIndepSet_indepNum
  refine ⟨Subtype.val '' (J : Set S), ?_, ?_, ?_⟩
  · rintro v ⟨w, _, rfl⟩
    exact w.property
  · rintro a ⟨x, hx, rfl⟩ b ⟨y, hy, rfl⟩ hxy hab
    exact hJ.isIndepSet hx hy (fun heq => hxy (congrArg Subtype.val heq)) hab
  · rw [Set.ncard_image_of_injective _ Subtype.val_injective, Set.ncard_coe_finset]
    exact hJ.card_eq

theorem indep_ncard_le_independence {V : Type*} [Fintype V] {G : SimpleGraph V}
    {I S : Set V} (hI : G.IsIndepSet I) (hIS : I ⊆ S) : I.ncard ≤ independence G S := by
  classical
  let J : Set S := Subtype.val ⁻¹' I
  have hJ : (G.induce S).IsIndepSet J := by
    intro a ha b hb hab hadj
    exact hI ha hb (fun h => hab (Subtype.ext h)) hadj
  have heq : Subtype.val '' J = I := by
    ext v
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact hw
    · intro hv
      exact ⟨⟨v, hIS hv⟩, hv, rfl⟩
  have hc := indep_ncard_le hJ
  rw [← Set.ncard_image_of_injective J Subtype.val_injective, heq] at hc
  exact hc

theorem independence_mono {V : Type*} [Fintype V] {G : SimpleGraph V}
    {S T : Set V} (hST : S ⊆ T) : independence G S ≤ independence G T := by
  obtain ⟨I, hIS, hI, hcard⟩ := exists_indep_of_independence G S
  rw [← hcard]
  exact indep_ncard_le_independence hI (hIS.trans hST)

theorem independence_le_card {V : Type*} [Fintype V] (G : SimpleGraph V) (S : Set V) :
    independence G S ≤ S.ncard := by
  obtain ⟨I, hIS, _, hcard⟩ := exists_indep_of_independence G S
  rw [← hcard]
  exact Set.ncard_le_ncard hIS

theorem independence_pos {V : Type*} [Fintype V] {G : SimpleGraph V} {S : Set V}
    (hS : S.Nonempty) : 0 < independence G S := by
  obtain ⟨x, hx⟩ := hS
  have hI : G.IsIndepSet {x} := Set.pairwise_singleton _ _
  have hc := indep_ncard_le_independence hI (Set.singleton_subset_iff.mpr hx)
  simp only [Set.ncard_singleton] at hc
  omega

theorem independence_univ {V : Type*} [Fintype V] (G : SimpleGraph V) :
    independence G Set.univ = G.indepNum := by
  classical
  apply le_antisymm
  · obtain ⟨I, _, hI, hcard⟩ := exists_indep_of_independence G Set.univ
    rw [← hcard]
    exact indep_ncard_le hI
  · obtain ⟨I, hI⟩ := G.exists_isNIndepSet_indepNum
    have hc := indep_ncard_le_independence hI.isIndepSet (Set.subset_univ _)
    simpa only [Set.ncard_coe_finset, hI.card_eq] using hc

 

theorem independence_outside_closed {V : Type*} [Fintype V] {G : SimpleGraph V}
    {I S : Set V} (hI : G.IsIndepSet I) (hIS : I ⊆ S) :
    independence G (S \ closedNeighborhood G I) + I.ncard ≤ independence G S := by
  classical
  obtain ⟨J, hJsub, hJ, hJcard⟩ := exists_indep_of_independence G
    (S \ closedNeighborhood G I)
  have hdisj : Disjoint J I := Set.disjoint_left.mpr (by
    intro v hv hi
    exact (hJsub hv).2 (Or.inl hi))
  have hJI : G.IsIndepSet (J ∪ I) := by
    intro a ha b hb hab hadj
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · exact hJ ha hb hab hadj
    · exact (hJsub ha).2 (Or.inr ⟨b, hb, hadj.symm⟩)
    · exact (hJsub hb).2 (Or.inr ⟨a, ha, hadj⟩)
    · exact hI ha hb hab hadj
  have hc := indep_ncard_le_independence hJI (Set.union_subset (fun _ h => (hJsub h).1) hIS)
  rwa [Set.ncard_union_eq hdisj, hJcard] at hc

 
theorem no_compl_clique_iff {V : Type*} [Fintype V] (G : SimpleGraph V) (a : ℕ) :
    (¬ (⊤ : SimpleGraph (Fin (a + 1))) ⊑ Gᶜ) ↔ G.indepNum ≤ a := by
  classical
  constructor
  · intro h
    obtain ⟨I, hI⟩ := G.exists_isNIndepSet_indepNum
    have hc := clique_ncard_lt h ((SimpleGraph.isClique_compl G).mpr hI.isIndepSet)
    simp only [Set.ncard_coe_finset, hI.card_eq] at hc
    omega
  · intro h hc
    apply hc.not_cliqueFree
    intro I hI
    have hi := (SimpleGraph.isNClique_compl G).mp hI
    have hb := hi.isIndepSet.card_le_indepNum
    rw [hi.card_eq] at hb
    omega

end CycleClique

end OAI
