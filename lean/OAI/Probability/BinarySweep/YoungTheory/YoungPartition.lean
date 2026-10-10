import Mathlib
import OAI.Probability.BinarySweep.YoungTheory.YoungFactor

namespace OAI

noncomputable section
open scoped BigOperators

namespace BinaryCoordinateSweeps.Young

lemma card_cellsOfRowLens (w : List ℕ) : (YoungDiagram.cellsOfRowLens w).card = w.sum := by
  induction w with
  | nil => simp [YoungDiagram.cellsOfRowLens]
  | cons a w ih =>
    rw [YoungDiagram.cellsOfRowLens, Finset.card_union_of_disjoint]
    · simpa using congrArg (a + ·) ih
    · rw [Finset.disjoint_left]
      intro x hx hy
      obtain ⟨y, hy, he⟩ := Finset.mem_map.mp hy
      have hx0 := (Finset.mem_product.mp hx).1
      simp only [Finset.mem_singleton] at hx0
      have hf := congrArg Prod.fst he
      change Nat.succ y.1 = x.1 at hf
      omega

def diagram {n : ℕ} (p : n.Partition) : YoungDiagram :=
  YoungDiagram.ofRowLens (p.parts.sort (· ≥ ·)) (Multiset.pairwise_sort _ _).sortedGE

lemma diagram_card {n : ℕ} (p : n.Partition) : (diagram p).card = n := by
  change (YoungDiagram.cellsOfRowLens (p.parts.sort (· ≥ ·))).card = n
  rw [card_cellsOfRowLens, ← Multiset.sum_coe, Multiset.sort_eq, p.parts_sum]

lemma diagram_rowLens {n : ℕ} (p : n.Partition) :
    (diagram p).rowLens = p.parts.sort (· ≥ ·) := by
  apply YoungDiagram.rowLens_ofRowLens_eq_self
  intro x hx
  apply p.parts_pos
  simpa only [Multiset.mem_sort] using hx

lemma diagram_injective {n : ℕ} : Function.Injective (diagram (n := n)) := by
  intro p q h
  apply Nat.Partition.ext
  have hh := congrArg (fun μ => (μ.rowLens : Multiset ℕ)) h
  simpa only [diagram_rowLens, Multiset.sort_eq] using hh

def cellsEquivFin {n : ℕ} (p : n.Partition) : Cell (diagram p) ≃ Fin n :=
  Fintype.equivFinOfCardEq (by simpa using diagram_card p)

def conjPartition {X : Type*} [Fintype X] [DecidableEq X] :
    ConjClasses (Equiv.Perm X) → (Fintype.card X).Partition :=
  Quotient.lift Equiv.Perm.partition (fun _ _ h => Equiv.Perm.partition_eq_of_isConj.mp h)

lemma conjPartition_injective {X : Type*} [Fintype X] [DecidableEq X] :
    Function.Injective (conjPartition (X := X)) := by
  intro c d
  obtain ⟨c, rfl⟩ := ConjClasses.mk_surjective c
  obtain ⟨d, rfl⟩ := ConjClasses.mk_surjective d
  intro h
  exact ConjClasses.mk_eq_mk_iff_isConj.mpr (Equiv.Perm.partition_eq_of_isConj.mpr h)

end BinaryCoordinateSweeps.Young

end

end OAI
