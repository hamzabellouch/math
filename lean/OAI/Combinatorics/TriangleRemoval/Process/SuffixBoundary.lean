import Mathlib
import OAI.Combinatorics.TriangleRemoval.Embeddings.BirthGraph
import OAI.Combinatorics.TriangleRemoval.Process.BornEdges

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open Filter
open scoped BigOperators Topology
open scoped BigOperators

namespace SharpTerminalLeave.BirthGraph
variable {N : ℕ} (B : BirthGraph N)

def suffixBoundary (Z : Finset (Fin N)) (a b : Fin N) : Finset (Fin N) :=
  ((Z.biUnion B.older) ∪ {a,b}) \ Z

def suffixVertices (Z : Finset (Fin N)) (a b : Fin N) : Finset (Fin N) :=
  Z ∪ B.suffixBoundary Z a b

def suffixEdges (Z : Finset (Fin N)) (a b : Fin N) : Finset (Finset (Fin N)) :=
  insert {a,b} (B.backEdges Z)

lemma suffixBoundary_disjoint (Z : Finset (Fin N)) (a b : Fin N) :
    Disjoint (B.suffixBoundary Z a b) Z := Finset.sdiff_disjoint

lemma mem_suffixBoundary (Z : Finset (Fin N)) (a b x : Fin N) :
    x ∈ B.suffixBoundary Z a b ↔
      ((∃ v ∈ Z, x ∈ B.older v) ∨ x = a ∨ x = b) ∧ x ∉ Z := by
  simp only [suffixBoundary,Finset.mem_sdiff,Finset.mem_union,Finset.mem_biUnion,
    Finset.mem_insert,Finset.mem_singleton]

lemma suffixBoundary_card {Z : Finset (Fin N)} {a b : Fin N} (hmark : a ∈ Z ∨ b ∈ Z) :
    (B.suffixBoundary Z a b).card ≤ 2 * Z.card + 1 := by
  have hbase : (Z.biUnion B.older).card ≤ 2 * Z.card := by
    calc
      _ ≤ ∑ v ∈ Z, (B.older v).card := Finset.card_biUnion_le
      _ ≤ ∑ _v ∈ Z, 2 := Finset.sum_le_sum (fun v _ => B.older_card v)
      _ = _ := by simp [mul_comm]
  have hbound (x y : Fin N) (hx : x ∈ Z) :
      (((Z.biUnion B.older) ∪ {x,y}) \ Z).card ≤ 2 * Z.card + 1 := by
    have hs : ((Z.biUnion B.older) ∪ {x,y}) \ Z ⊆ insert y (Z.biUnion B.older) := by
      intro z hz
      obtain ⟨hz,hzn⟩ := Finset.mem_sdiff.mp hz
      rcases Finset.mem_union.mp hz with hz | hz
      · exact Finset.mem_insert_of_mem hz
      · rcases Finset.mem_insert.mp hz with rfl | hz
        · exact False.elim (hzn hx)
        · exact Finset.mem_insert.mpr (Or.inl (Finset.mem_singleton.mp hz))
    exact (Finset.card_le_card hs).trans ((Finset.card_insert_le _ _).trans (Nat.add_le_add_right hbase 1))
  rcases hmark with ha | hb
  · exact hbound a b ha
  · simpa only [suffixBoundary,Finset.pair_comm a b] using hbound b a hb

lemma suffixVertices_card {Z : Finset (Fin N)} {a b : Fin N} (hmark : a ∈ Z ∨ b ∈ Z) :
    (B.suffixVertices Z a b).card ≤ 3 * Z.card + 1 := by
  unfold suffixVertices
  have hh := (Finset.card_union_le Z (B.suffixBoundary Z a b)).trans
    (Nat.add_le_add_left (B.suffixBoundary_card hmark) Z.card)
  omega

lemma suffixEdges_simple {Z : Finset (Fin N)} {a b : Fin N} (hab : a ≠ b) :
    ∀ e ∈ B.suffixEdges Z a b, e.card = 2 := by
  intro e he
  rcases Finset.mem_insert.mp he with rfl | he
  · exact Finset.card_pair hab
  · obtain ⟨v,_,u,hu,rfl⟩ := B.backEdges_mem_pair he
    exact Finset.card_pair (ne_of_lt (B.older_lt v u hu))

lemma suffixEdges_subset_vertices {Z : Finset (Fin N)} {a b : Fin N} :
    ∀ e ∈ B.suffixEdges Z a b, e ⊆ B.suffixVertices Z a b := by
  intro e he x hx
  apply Finset.mem_union.mpr
  by_cases hxZ : x ∈ Z
  · exact Or.inl hxZ
  · apply Or.inr
    apply (B.mem_suffixBoundary Z a b x).mpr
    refine ⟨?_,hxZ⟩
    rcases Finset.mem_insert.mp he with rfl | he
    · exact Or.inr (by simpa only [Finset.mem_insert,Finset.mem_singleton] using hx)
    · obtain ⟨v,hv,u,hu,rfl⟩ := B.backEdges_mem_pair he
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact Or.inl ⟨v,hv,hu⟩
      · exact False.elim (hxZ (Finset.mem_singleton.mp hx ▸ hv))

lemma suffixEdges_touch {Z : Finset (Fin N)} {a b : Fin N} (hmark : a ∈ Z ∨ b ∈ Z) :
    ∀ e ∈ B.suffixEdges Z a b, ∃ v ∈ e, v ∈ Z := by
  intro e he
  rcases Finset.mem_insert.mp he with rfl | he
  · rcases hmark with ha | hb
    · exact ⟨a,by simp,ha⟩
    · exact ⟨b,by simp,hb⟩
  · obtain ⟨v,hv,u,_,rfl⟩ := B.backEdges_mem_pair he
    exact ⟨v,by simp,hv⟩

lemma suffixBoundary_independent {Z : Finset (Fin N)} {a b : Fin N}
    (hmark : a ∈ Z ∨ b ∈ Z) :
    ∀ e ∈ B.suffixEdges Z a b, ¬ e ⊆ B.suffixBoundary Z a b := by
  intro e he hs
  obtain ⟨v,hve,hvZ⟩ := B.suffixEdges_touch hmark e he
  exact Finset.disjoint_left.mp (B.suffixBoundary_disjoint Z a b) (hs hve) hvZ

end SharpTerminalLeave.BirthGraph

end

end OAI
