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

def Within (Z : Finset (Fin N)) (x y : Fin N) : Prop :=
  Relation.ReflTransGen (fun x y => x ∈ Z ∧ y ∈ Z ∧ x ∈ B.older y) x y

def Covered (Z : Finset (Fin N)) (a b : Fin N) : Prop :=
  ∀ z ∈ Z, (a ∈ Z ∧ B.Within Z z a) ∨ (b ∈ Z ∧ B.Within Z z b)

theorem within_closed {Z U : Finset (Fin N)} {x y : Fin N}
    (h : B.Within Z x y)
    (hclosed : ∀ v ∈ U, ∀ u ∈ B.older v, u ∈ Z → u ∈ U) (hy : y ∈ U) : x ∈ U := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact hy
  | @head x c hxc _ ih => exact hclosed c ih x hxc.2.2 hxc.1

theorem covered_closed {Z U : Finset (Fin N)} {a b : Fin N}
    (hc : B.Covered Z a b) (ha : a ∈ Z → a ∈ U) (hb : b ∈ Z → b ∈ U)
    (hclosed : ∀ v ∈ U, ∀ u ∈ B.older v, u ∈ Z → u ∈ U) : Z ⊆ U := by
  intro z hz
  rcases hc z hz with ⟨haZ, hza⟩ | ⟨hbZ, hzb⟩
  · exact B.within_closed hza hclosed (ha haZ)
  · exact B.within_closed hzb hclosed (hb hbZ)

theorem retained_backEdges_subset {Z I U : Finset (Fin N)} (hI : Disjoint I Z) :
    ((B.backEdges Z).filter (fun e => e ⊆ I ∪ U)) ⊆ B.backEdges U := by
  intro e he
  obtain ⟨heZ, heIU⟩ := Finset.mem_filter.mp he
  obtain ⟨v, hvZ, u, hu, rfl⟩ := B.backEdges_mem_pair heZ
  have hvIU : v ∈ I ∪ U := heIU (by simp)
  have hvU : v ∈ U := (Finset.mem_union.mp hvIU).resolve_left
    (fun hvI => Finset.disjoint_left.mp hI hvI hvZ)
  exact Finset.mem_biUnion.mpr ⟨v, hvU, Finset.mem_image.mpr ⟨u, hu, rfl⟩⟩

theorem proper_suffix_sparse {Z I U : Finset (Fin N)} {a b : Fin N}
    (hI : Disjoint I Z) (hU : U ⊆ Z) (hproper : U ≠ Z)
    (hborn : ∀ v ∈ Z, (B.older v).card = 2) (hc : B.Covered Z a b) :
    ((insert ({a, b} : Finset (Fin N)) (B.backEdges Z)).filter
      (fun e => e ⊆ I ∪ U)).card ≤ 2 * U.card := by
  classical
  let S := (B.backEdges Z).filter (fun e => e ⊆ I ∪ U)
  let T := (insert ({a, b} : Finset (Fin N)) (B.backEdges Z)).filter
    (fun e => e ⊆ I ∪ U)
  have hS : S ⊆ B.backEdges U := B.retained_backEdges_subset hI
  have hUcard : (B.backEdges U).card = 2 * U.card :=
    B.backEdges_card_eq U (fun v hv => hborn v (hU hv))
  have hST : T ⊆ insert {a, b} S := by
    intro e he
    obtain ⟨he, heIU⟩ := Finset.mem_filter.mp he
    rcases Finset.mem_insert.mp he with rfl | he
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨he, heIU⟩)
  by_contra hfail
  have hbig : 2 * U.card < T.card := Nat.lt_of_not_ge hfail
  have hmark : ({a, b} : Finset (Fin N)) ⊆ I ∪ U := by
    by_contra hn
    have hTS : T ⊆ S := by
      intro e he
      obtain ⟨he, heIU⟩ := Finset.mem_filter.mp he
      rcases Finset.mem_insert.mp he with rfl | he
      · exact False.elim (hn heIU)
      · exact Finset.mem_filter.mpr ⟨he, heIU⟩
    have hh := (Finset.card_le_card hTS).trans (Finset.card_le_card hS)
    rw [hUcard] at hh
    exact (Nat.not_le_of_gt hbig) hh
  have heq : S = B.backEdges U := by
    apply Finset.eq_of_subset_of_card_le hS
    have hh := (Finset.card_le_card hST).trans (Finset.card_insert_le _ _)
    rw [hUcard]
    omega
  have hclosed : ∀ v ∈ U, ∀ u ∈ B.older v, u ∈ Z → u ∈ U := by
    intro v hv u hu huZ
    have heU : ({u, v} : Finset (Fin N)) ∈ B.backEdges U :=
      Finset.mem_biUnion.mpr ⟨v, hv, Finset.mem_image.mpr ⟨u, hu, rfl⟩⟩
    rw [← heq] at heU
    have huIU : u ∈ I ∪ U := (Finset.mem_filter.mp heU).2 (by simp)
    exact (Finset.mem_union.mp huIU).resolve_left
      (fun huI => Finset.disjoint_left.mp hI huI huZ)
  have haU : a ∈ Z → a ∈ U := by
    intro haZ
    exact (Finset.mem_union.mp (hmark (by simp))).resolve_left
      (fun haI => Finset.disjoint_left.mp hI haI haZ)
  have hbU : b ∈ Z → b ∈ U := by
    intro hbZ
    exact (Finset.mem_union.mp (hmark (by simp))).resolve_left
      (fun hbI => Finset.disjoint_left.mp hI hbI hbZ)
  exact hproper (Finset.Subset.antisymm hU (B.covered_closed hc haU hbU hclosed))

theorem suffix_edges_card {Z : Finset (Fin N)} {a b : Fin N}
    (hborn : ∀ v ∈ Z, (B.older v).card = 2)
    (hne : ¬ B.graph.Adj a b) :
    (insert ({a, b} : Finset (Fin N)) (B.backEdges Z)).card = 2 * Z.card + 1 := by
  have hn : ({a, b} : Finset (Fin N)) ∉ B.backEdges Z := by
    intro he
    obtain ⟨v, hv, u, hu, huv⟩ := B.backEdges_mem_pair he
    have huvn : u ≠ v := ne_of_lt (B.older_lt v u hu)
    have hab : a ≠ b := by
      intro h
      have hc := congrArg Finset.card huv
      simp [h, huvn] at hc
    have ha : a = u ∨ a = v := by
      have hm : a ∈ ({u, v} : Finset (Fin N)) := by rw [← huv]; simp
      simpa only [Finset.mem_insert, Finset.mem_singleton] using hm
    have hb : b = u ∨ b = v := by
      have hm : b ∈ ({u, v} : Finset (Fin N)) := by rw [← huv]; simp
      simpa only [Finset.mem_insert, Finset.mem_singleton] using hm
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact hab rfl
    · exact hne (Or.inl hu)
    · exact hne (Or.inr hu)
    · exact hab rfl
  rw [Finset.card_insert_of_notMem hn, B.backEdges_card_eq Z hborn]

end SharpTerminalLeave.BirthGraph

end

end OAI
