import Mathlib
import OAI.Combinatorics.Ramsey.CycleClique.Basic
import OAI.Combinatorics.Ramsey.CycleClique.ColouredPaths
import OAI.Combinatorics.Ramsey.CycleClique.Exceptional
import OAI.Combinatorics.Ramsey.CycleClique.Independence

namespace OAI

namespace CycleClique
open scoped SimpleGraph

theorem indep_induce_iff_image {V : Type*} {G : SimpleGraph V} {S : Set V} {I : Set S} :
    (G.induce S).IsIndepSet I ↔ G.IsIndepSet (Subtype.val '' I) := by
  constructor
  · intro h a ha b hb hab hadj
    obtain ⟨x, hx, rfl⟩ := ha
    obtain ⟨y, hy, rfl⟩ := hb
    exact h hx hy (fun heq => hab (congrArg Subtype.val heq)) hadj
  · intro h a ha b hb hab hadj
    exact h ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩ (fun heq => hab (Subtype.ext heq)) hadj

theorem independence_induce_image {V : Type*} [Fintype V] (G : SimpleGraph V)
    (S : Set V) (T : Set S) :
    independence (G.induce S) T = independence G (Subtype.val '' T) := by
  classical
  apply le_antisymm
  · obtain ⟨I, hIT, hI, hc⟩ := exists_indep_of_independence (G.induce S) T
    have hb := indep_ncard_le_independence (indep_induce_iff_image.mp hI) (Set.image_mono hIT)
    rwa [Set.ncard_image_of_injective _ Subtype.val_injective, hc] at hb
  · obtain ⟨I, hIT, hI, hc⟩ := exists_indep_of_independence G (Subtype.val '' T)
    let J : Set S := Subtype.val ⁻¹' I
    have heq : Subtype.val '' J = I := by
      ext v
      constructor
      · rintro ⟨w, hw, rfl⟩
        exact hw
      · intro hv
        obtain ⟨w, _, rfl⟩ := hIT hv
        exact ⟨w, hv, rfl⟩
    have hJ : (G.induce S).IsIndepSet J := indep_induce_iff_image.mpr (heq ▸ hI)
    have hJT : J ⊆ T := by
      intro x hx
      obtain ⟨y, hy, hxy⟩ := hIT hx
      exact Subtype.val_injective hxy ▸ hy
    have hb := indep_ncard_le_independence hJ hJT
    rw [← Set.ncard_image_of_injective J Subtype.val_injective, heq, hc] at hb
    exact hb

 
theorem independence_add_le {V : Type*} [Fintype V] {G : SimpleGraph V}
    {A B S : Set V} (hA : A ⊆ S) (hB : B ⊆ S) (hdis : Disjoint A B)
    (hcross : ∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b) :
    independence G A + independence G B ≤ independence G S := by
  classical
  obtain ⟨I, hIA, hI, hcI⟩ := exists_indep_of_independence G A
  obtain ⟨J, hJB, hJ, hcJ⟩ := exists_indep_of_independence G B
  have hdIJ : Disjoint I J := hdis.mono hIA hJB
  have hIJ : G.IsIndepSet (I ∪ J) := by
    intro a ha b hb hab hadj
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · exact hI ha hb hab hadj
    · exact hcross a (hIA ha) b (hJB hb) hadj
    · exact hcross b (hIA hb) a (hJB ha) hadj.symm
    · exact hJ ha hb hab hadj
  have hc := indep_ncard_le_independence hIJ (Set.union_subset (hIA.trans hA) (hJB.trans hB))
  rwa [Set.ncard_union_eq hdIJ, hcI, hcJ] at hc

 
theorem clique_of_independence_le_one {V : Type*} [Fintype V] {G : SimpleGraph V}
    {S : Set V} (hα : independence G S ≤ 1) : G.IsClique S := by
  intro a ha b hb hab
  by_contra hn
  have hI : G.IsIndepSet {a, b} := by
    intro x hx y hy hxy hxyadj
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact hxy rfl
    · exact hn hxyadj
    · exact hn hxyadj.symm
    · exact hxy rfl
  have hc := indep_ncard_le_independence hI (Set.insert_subset ha (Set.singleton_subset_iff.mpr hb))
  rw [Set.ncard_pair hab] at hc
  omega

 
theorem bipartite_card_le_twice_indep {V : Type*} [Fintype V] {G : SimpleGraph V}
    (hbip : G.IsBipartite) : Fintype.card V ≤ 2 * G.indepNum := by
  classical
  obtain ⟨χ⟩ := hbip
  have hzero := indep_ncard_le (χ.isIndepSet_colorClass (0 : Fin 2))
  have hone := indep_ncard_le (χ.isIndepSet_colorClass (1 : Fin 2))
  have hunion : χ.colorClass 0 ∪ χ.colorClass 1 = Set.univ := by
    ext v
    simp only [Set.mem_union, SimpleGraph.Coloring.colorClass, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    have := (χ v).isLt
    omega
  have hdis : Disjoint (χ.colorClass 0) (χ.colorClass 1) := by
    apply Set.disjoint_left.mpr
    intro v hv₀ hv₁
    have hzero : χ v = 0 := hv₀
    have hone : χ v = 1 := hv₁
    exact (by decide : (0 : Fin 2) ≠ 1) (hzero.symm.trans hone)
  have hc := Set.ncard_union_eq hdis
  rw [hunion, Set.ncard_univ, Nat.card_eq_fintype_card] at hc
  omega

 
theorem closedNeighborhood_singleton_card {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    (closedNeighborhood G {v}).ncard = G.degree v + 1 := by
  have heq : closedNeighborhood G {v} = insert v (G.neighborSet v) := by
    ext w
    simp [closedNeighborhood, SimpleGraph.mem_neighborSet]
  rw [heq, Set.ncard_insert_of_notMem G.notMem_neighborSet_self, ncard_neighborSet]

end CycleClique

end OAI
