import Mathlib
import OAI.Probability.CriticalPercolation.Clusters.ComponentSelf
import OAI.Probability.CriticalPercolation.Exploration.IncidenceDegree

namespace OAI

section
section
noncomputable section
open Set
open scoped Classical

namespace CriticalPercolation
namespace BondGraph
open ClusterDeletion

variable {V E : Type*} [Fintype V] [Fintype E] (G : BondGraph V E)

def exitEndpoint (U : Set V) (e : E) : V :=
  if (G.ends e).out.1 ∈ U then (G.ends e).out.2 else (G.ends e).out.1

def exitVertices (U : Set V) : Finset V :=
  (G.incidentEdges U).toFinset.image (G.exitEndpoint U)

omit [Fintype V] in
lemma exterior_neighbor_mem_exitVertices (U : Set V) {u v : V}
    (hu : u∈U) (hv : v∉U) (hadj : G.fullGraph.Adj u v) :
    v∈G.exitVertices U := by
  obtain ⟨e,_,he⟩ := hadj.1
  have hemi : e∈G.incidentEdges U := ⟨u,hu,he ▸ Sym2.mem_mk_left _ _⟩
  apply Finset.mem_image.mpr
  refine ⟨e,Set.mem_toFinset.mpr hemi,?_⟩
  have hh : s((G.ends e).out.1,(G.ends e).out.2)=s(u,v) :=
    (G.ends e).out_eq.trans he
  rcases (Sym2.mk_eq_mk_iff (p := (G.ends e).out) (q := (u,v))).mp hh with hh|hh
  · have h1 := congrArg Prod.fst hh
    have h2 := congrArg Prod.snd hh
    simp [exitEndpoint,h1,h2,hu]
  · have h1 := congrArg Prod.fst hh
    have h2 := congrArg Prod.snd hh
    simp only [Prod.fst_swap,Prod.snd_swap] at h1 h2
    simp [exitEndpoint,h1,hv]

lemma exitVertices_card_le (U : Set V) (D : ℕ)
    (hD : ∀ v, (G.incidentEdges {v}).toFinset.card≤D) :
    (G.exitVertices U).card≤U.toFinset.card*D :=
  Finset.card_image_le.trans (G.incident_card_le U D hD)

def smallDamage (H : SimpleGraph V) (U : Set V) (s : ℕ) : Finset V :=
  U.toFinset ∪ ((G.exitVertices U).filter
    (fun w => (component (delete H U) w).toFinset.card<s)).biUnion
      (fun w => (component (delete H U) w).toFinset)

lemma smallDamage_card_le (H : SimpleGraph V) (U : Set V) (s D : ℕ)
    (hD : ∀ v, (G.incidentEdges {v}).toFinset.card≤D) :
    (G.smallDamage H U s).card ≤ U.toFinset.card + U.toFinset.card*D*(s-1) := by
  let T := (G.exitVertices U).filter
    (fun w => (component (delete H U) w).toFinset.card<s)
  change (U.toFinset ∪ T.biUnion (fun w => (component (delete H U) w).toFinset)).card ≤ _
  calc
    _ ≤ U.toFinset.card + (T.biUnion (fun w => (component (delete H U) w).toFinset)).card :=
      Finset.card_union_le _ _
    _ ≤ U.toFinset.card + ∑ w∈T, (component (delete H U) w).toFinset.card :=
      Nat.add_le_add_left Finset.card_biUnion_le _
    _ ≤ U.toFinset.card + ∑ _w∈T, (s-1) := by
      apply Nat.add_le_add_left
      apply Finset.sum_le_sum
      intro w hw
      have hh := (Finset.mem_filter.mp hw).2
      omega
    _ = U.toFinset.card + T.card*(s-1) := by simp
    _ ≤ U.toFinset.card + (G.exitVertices U).card*(s-1) :=
      Nat.add_le_add_left (Nat.mul_le_mul_right _ (Finset.card_filter_le _ _)) _
    _ ≤ _ := Nat.add_le_add_left
      (Nat.mul_le_mul_right _ (G.exitVertices_card_le U D hD)) _

lemma tail_deletion_or_damage (H : SimpleGraph V) (hH : H≤G.fullGraph)
    (U : Set V) (s : ℕ) (v : V)
    (hs : s≤(component H v).toFinset.card) :
    (v∉U ∧ s≤(component (delete H U) v).toFinset.card) ∨ v∈G.smallDamage H U s := by
  by_cases hv : v∈G.smallDamage H U s
  · exact Or.inr hv
  apply Or.inl
  have hvU : v∉U := fun hh => hv (Finset.mem_union_left _ (Set.mem_toFinset.mpr hh))
  refine ⟨hvU,?_⟩
  by_contra! hsmall
  have hclosed : ∀ ⦃a b⦄, a∈component (delete H U) v → H.Adj a b →
      b∈component (delete H U) v := by
    intro a b ha hab
    have haU : a∉U := by
      by_contra haU
      have he := component_delete_self H U a haU
      have hav : v∈component (delete H U) a := ha.symm
      rw [he] at hav
      exact hvU ((Set.mem_singleton_iff.mp hav) ▸ haU)
    have hbU : b∉U := by
      intro hb
      have hae := G.exterior_neighbor_mem_exitVertices U hb haU (hH hab.symm)
      have he := component_eq_of_mem ha
      apply hv
      apply Finset.mem_union_right
      apply Finset.mem_biUnion.mpr
      refine ⟨a,Finset.mem_filter.mpr ⟨hae,?_⟩,Set.mem_toFinset.mpr ha.symm⟩
      rwa [he]
    exact ha.trans (SimpleGraph.Adj.reachable ⟨hab,haU,hbU⟩)
  have hsub : component H v ⊆ component (delete H U) v := by
    intro w hw
    exact reachable_mem_of_closed hclosed (component_self _ _) hw
  have hc := Finset.card_le_card (Set.toFinset_mono hsub)
  omega

def tailCount (H : SimpleGraph V) (B : Finset V) (s : ℕ) : ℝ :=
  ∑ v∈B, if s≤(component H v).toFinset.card then 1 else 0

def exteriorTailCount (H : SimpleGraph V) (U : Set V) (B : Finset V) (s : ℕ) : ℝ :=
  ∑ v∈B, if v∉U ∧ s≤(component (delete H U) v).toFinset.card then 1 else 0

lemma tailCount_le_exterior_add_damage (H : SimpleGraph V) (hH : H≤G.fullGraph)
    (U : Set V) (B : Finset V) (s D : ℕ)
    (hD : ∀ v, (G.incidentEdges {v}).toFinset.card≤D) :
    tailCount H B s ≤ exteriorTailCount H U B s +
      (U.toFinset.card + U.toFinset.card*D*(s-1) : ℕ) := by
  calc
    _ ≤ ∑ v∈B, ((if v∉U ∧ s≤(component (delete H U) v).toFinset.card then 1 else 0) +
        if v∈G.smallDamage H U s then 1 else 0) := by
      apply Finset.sum_le_sum
      intro v _
      by_cases hs : s≤(component H v).toFinset.card
      · rcases G.tail_deletion_or_damage H hH U s v hs with hv|hv
        · rw [ite_eq_left hs,ite_eq_left hv]
          split_ifs <;> norm_num
        · rw [ite_eq_left hs,ite_eq_left hv]
          split_ifs <;> norm_num
      · simp only [hs,ite_false]
        split_ifs <;> norm_num
    _ = exteriorTailCount H U B s + ((B.filter (fun v => v∈G.smallDamage H U s)).card:ℝ) := by
      rw [Finset.sum_add_distrib]
      congr 1
      simp only [Finset.sum_boole]
    _ ≤ exteriorTailCount H U B s + ((G.smallDamage H U s).card:ℝ) := by
      apply add_le_add le_rfl
      exact Nat.cast_le.mpr (Finset.card_le_card (fun v hv => (Finset.mem_filter.mp hv).2))
    _ ≤ _ := add_le_add le_rfl (Nat.cast_le.mpr (G.smallDamage_card_le H U s D hD))

end BondGraph
end CriticalPercolation
end
end
end

end OAI
