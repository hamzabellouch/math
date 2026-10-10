import OAI.NumberTheory.TwoPoint.Bounds.IntegerClosedCatalog
import OAI.NumberTheory.TwoPoint.Bounds.TraceCatalogMaps

namespace OAI

/-! Recover the column data of the actual joined matrix paths. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

lemma ofFn_rev_eq_reverse {α : Type*} {n : ℕ} (f : Fin n → α) :
    List.ofFn (fun i => f i.rev) = (List.ofFn f).reverse := by
  apply List.ext_getElem
  · simp only [List.length_ofFn, List.length_reverse]
  · intro i hi hj
    simp only [List.getElem_ofFn, List.getElem_reverse, List.length_ofFn]
    congr 1
    apply Fin.ext
    simp only [Fin.val_rev]
    omega

def closedColumnRows {J k : ℕ} {P : Fin J → Finset ℕ} (Q : Finset ℕ)
    (a b : Fin k → ((j : Fin J) → P j) × (Q × Bool)) :
    Fin (k + k) → ((j : Fin J) → P j) × (Q × Bool) :=
  Fin.append a (fun i => ((b i.rev).1, (b i.rev).2.1, !(b i.rev).2.2))

lemma closedColumnRows_word {J k : ℕ} {P : Fin J → Finset ℕ} (Q : Finset ℕ)
    (a b : Fin k → ((j : Fin J) → P j) × (Q × Bool)) :
    integerStepWord Q (fun d => ∏ j, (d j).val) (closedColumnRows Q a b) =
      integerClosedWordCode Q (fun d => ∏ j, (d j).val) (a, b) := by
  unfold integerStepWord closedColumnRows integerClosedWordCode
  rw [List.ofFn_fin_append, List.map_append]
  congr 1
  rw [reverseWord]
  simp only [integerStepWord, List.map_reverse, List.map_ofFn, Function.comp_def]
  rw [← ofFn_rev_eq_reverse]
  simp only [SignedStep.flip]

def closedColumnAssignment {J k : ℕ} {P : Fin J → Finset ℕ} (Q : Finset ℕ)
    (a b : Fin k → ((j : Fin J) → P j) × (Q × Bool)) :
    ColumnPrimeAssignment J (k + k) P :=
  fun j i => (closedColumnRows Q a b i).1 j

def closedColumnPadding {J k : ℕ} {P : Fin J → Finset ℕ} (Q : Finset ℕ)
    (a b : Fin k → ((j : Fin J) → P j) × (Q × Bool)) : Fin (k + k) → Q :=
  fun i => (closedColumnRows Q a b i).2.1

def closedColumnForward {J k : ℕ} {P : Fin J → Finset ℕ} (Q : Finset ℕ)
    (a b : Fin k → ((j : Fin J) → P j) × (Q × Bool)) : Fin (k + k) → Bool :=
  fun i => (closedColumnRows Q a b i).2.2

theorem closedColumn_encoding_word {J k : ℕ} {P : Fin J → Finset ℕ} (Q : Finset ℕ)
    (a b : Fin k → ((j : Fin J) → P j) × (Q × Bool)) :
    columnTupleWord (closedColumnAssignment Q a b) (closedColumnForward Q a b)
      (fun i => (closedColumnPadding Q a b i).val) =
      integerClosedWordCode Q (fun d => ∏ j, (d j).val) (a, b) := by
  rw [← closedColumnRows_word]
  simp only [columnTupleWord, columnTuple, closedColumnAssignment, closedColumnForward,
    closedColumnPadding, integerStepWord, List.map_ofFn, Function.comp_def]

end TwoPointCorrelations

end OAI
