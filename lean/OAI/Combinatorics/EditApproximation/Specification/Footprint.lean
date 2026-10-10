import OAI.Combinatorics.EditApproximation.Binary.BitMemoHeap
import OAI.Combinatorics.EditApproximation.Binary.BitQueryKeysSpace
import OAI.Combinatorics.EditApproximation.Binary.BinaryNormalizationSpace
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI.EditApproximation.BitQuery

/- The allocation trace of a query, without a proof relating allocations to work.
The trace retains every allocation and every adaptive continuation. -/


namespace Footprint

def cells {ι β : Type*} {program : BitQuery ι β} (oracle : ι → BinaryFraction) :
    Footprint program → ℕ
  | .done _ => 0
  | .read key _ next => 3 + cells oracle (next (oracle key))
  | .charge localCells next => localCells + cells oracle next





















theorem runCells_congr {ι κ : Type*}
    (ask : ι → BinaryMemo BinaryFraction → BitRecursiveMemoResult κ)
    (childCells otherCells : ι → BinaryMemo BinaryFraction → ℕ)
    (h : ∀ key memory, childCells key memory = otherCells key memory)
    {program : BitQuery ι BinaryFraction} (heap : Footprint program)
    (memory : BinaryMemo BinaryFraction) :
    heap.runCells ask childCells memory = heap.runCells ask otherCells memory := by
  induction heap generalizing memory with
  | done => rfl
  | read key next continuation ih => simp only [runCells, h, ih]
  | charge localCells next ih => simp only [runCells, ih]

end Footprint

namespace Heap

/-- Forget only the local allocation/work certificates, preserving the exact trace. -/
def footprint {ι β : Type*} {program : BitQuery ι β} : Heap program → Footprint program
  | .done value => .done value
  | .read key next continuation => .read key next (fun word => (continuation word).footprint)
  | .charge localCells _ next => .charge localCells next.footprint

@[simp] theorem footprint_done {ι β : Type*} (value : β) :
    (Heap.done (ι := ι) value).footprint = .done value := rfl

@[simp] theorem footprint_read {ι β : Type*} (key : ι) (next : BinaryFraction → BitQuery ι β)
    (continuation : ∀ word, Heap (next word)) :
    (Heap.read key next continuation).footprint =
      .read key next (fun word => (continuation word).footprint) := rfl

@[simp] theorem footprint_charge {ι β : Type*} {steps : ℕ} {program : BitQuery ι β}
    (allocation : ℕ) (bound : allocation ≤ 3 * steps) (heap : Heap program) :
    (Heap.charge allocation bound heap).footprint = .charge allocation heap.footprint := rfl

@[simp] theorem footprint_cells {ι β : Type*} {program : BitQuery ι β}
    (oracle : ι → BinaryFraction) (heap : Heap program) :
    heap.footprint.cells oracle = heap.cells oracle := by
  induction heap with
  | done => rfl
  | read key next continuation ih => simp only [footprint, Footprint.cells, cells, ih]
  | charge localCells bound next ih => simp only [footprint, Footprint.cells, cells, ih]

@[simp] theorem footprint_bind {ι α β : Type*} {program : BitQuery ι α} (heap : Heap program)
    (next : α → BitQuery ι β) (allocation : ∀ value, Heap (next value)) :
    (heap.bind next allocation).footprint =
      heap.footprint.bind next (fun value => (allocation value).footprint) := by
  induction heap with
  | done => rfl
  | read key continuation stored ih =>
    simp only [bind, footprint, Footprint.bind]
    congr 1
    funext word
    exact ih word
  | charge localCells bound tail ih =>
    exact congrArg (Footprint.charge localCells) ih

@[simp] theorem footprint_compute {ι β : Type*} (execution : β × ℕ) (allocation : ℕ)
    (bound : allocation ≤ 3 * execution.2) :
    (Heap.compute (ι := ι) execution allocation bound).footprint =
      Footprint.compute execution allocation := rfl

@[simp] theorem footprint_chargeOf {ι β : Type*} {steps : ℕ} {program : BitQuery ι β}
    (allocation : ℕ) (bound : allocation ≤ steps) (heap : Heap program) :
    (Heap.chargeOf allocation bound heap).footprint = Footprint.chargeOf allocation heap.footprint := rfl

@[simp] theorem footprint_computeOf {ι β : Type*} (execution : β × ℕ) (allocation : ℕ)
    (bound : allocation ≤ execution.2) :
    (Heap.computeOf (ι := ι) execution allocation bound).footprint =
      Footprint.computeOf execution allocation := rfl

@[simp] theorem footprint_collect {ι κ β : Type*} (reader : κ → BitQuery ι BinaryFraction)
    (allocation : ∀ key, Heap (reader key)) (inputs : List κ)
    (next : List BinaryFraction → BitQuery ι β) (continuation : ∀ words, Heap (next words)) :
    (Heap.collect reader allocation inputs next continuation).footprint =
      Footprint.collect reader (fun key => (allocation key).footprint) inputs next
        (fun words => (continuation words).footprint) := by
  induction inputs generalizing next with
  | nil => rfl
  | cons key rest ih =>
    change ((allocation key).bind _ _).footprint = _
    rw [footprint_bind]
    apply congrArg (Footprint.bind (allocation key).footprint _)
    funext word
    exact congrArg (Footprint.charge 1) (ih _ _)

@[simp] theorem footprint_mapKeysWithWork {ι κ β : Type*} (f : ι → κ × ℕ)
    (allocation : ι → ℕ) (ha : ∀ key, allocation key ≤ (f key).2)
    {program : BitQuery ι β} (heap : Heap program) :
    (heap.mapKeysWithWork f allocation ha).footprint = heap.footprint.mapKeysWithWork f allocation := by
  induction heap with
  | done => rfl
  | read key next continuation ih =>
    change Footprint.charge (allocation key)
      (Footprint.read (f key).1 _ (fun word => (mapKeysWithWork f allocation ha (continuation word)).footprint)) =
      Footprint.charge (allocation key)
      (Footprint.read (f key).1 _ (fun word => Footprint.mapKeysWithWork f allocation (continuation word).footprint))
    apply congrArg (Footprint.charge (allocation key))
    apply congrArg (Footprint.read (f key).1 _)
    funext word
    exact ih word
  | charge localCells bound next ih =>
    exact congrArg (Footprint.charge localCells) ih

private theorem map_decidable_cases {p : Prop} (d : Decidable p) {α β : Sort*}
    (f : α → β) (no : ¬p → α) (yes : p → α) :
    f (Decidable.casesOn d no yes) =
      Decidable.casesOn d (fun h => f (no h)) (fun h => f (yes h)) := by
  cases d <;> rfl

private theorem footprint_mpr_congr {ι β : Type*} {p q : BitQuery ι β}
    (eqn : p = q) (a : Heap q) (b : Footprint q) (hab : a.footprint = b) :
    ((congrArg Heap eqn).mpr a).footprint = (congrArg Footprint eqn).mpr b := by
  cases eqn
  exact hab

@[simp] theorem footprint_restrictWithWork {ι : Type*} (P : ι → Prop)
    (test : ι → Bool × ℕ) (htest : ∀ key, (test key).1 = true ↔ P key)
    (allocation : ι → ℕ) (ha : ∀ key, allocation key ≤ (test key).2)
    {program : BitQuery ι BinaryFraction} (heap : Heap program) :
    (heap.restrictWithWork P test htest allocation ha).footprint =
      heap.footprint.restrictWithWork P test htest allocation := by
  induction heap with
  | done => rfl
  | charge localCells bound next ih =>
    exact congrArg (Footprint.charge localCells) ih
  | read key next continuation ih =>
    simp only [footprint_read]
    unfold restrictWithWork Footprint.restrictWithWork
    apply congrArg (Footprint.charge (allocation key))
    rw [map_decidable_cases (f := footprint)]
    congr 1
    · funext h
      apply footprint_mpr_congr (dite_eq_right h)
      exact ih (BinaryFraction.nat 0)
    · funext h
      apply footprint_mpr_congr (dite_eq_left h)
      apply congrArg (Footprint.read _ _)
      funext word
      exact ih word

@[simp] theorem footprint_normalize {ι : Type*} {program : BitQuery ι BinaryFraction}
    (heap : Heap program) (base : List Bool) (hbase : 0 < bitWordValue base) (remaining : ℕ) :
    (heap.normalize base hbase remaining).footprint = heap.footprint.normalize base hbase remaining := by
  exact footprint_bind heap _ _

@[simp] theorem footprint_runCells {ι κ : Type*}
    (ask : ι → BinaryMemo BinaryFraction → BitRecursiveMemoResult κ)
    (childCells : ι → BinaryMemo BinaryFraction → ℕ)
    {program : BitQuery ι BinaryFraction} (heap : Heap program) (memory : BinaryMemo BinaryFraction) :
    heap.footprint.runCells ask childCells memory = heap.runCells ask childCells memory := by
  induction heap generalizing memory with
  | done => rfl
  | read key next continuation ih => simp only [footprint, Footprint.runCells, runCells, ih]
  | charge localCells bound next ih => simp only [footprint, Footprint.runCells, runCells, ih]

@[simp] theorem footprint_rankedBitMemoCells {κ : Type*} (rank : κ → ℕ)
    (program : (key : κ) → BitQuery {child : κ // rank child < rank key} BinaryFraction)
    (heap : ∀ key, Heap (program key))
    (bits : ℕ) (encode addressCells : κ → ℕ) (key : κ) (memory : BinaryMemo BinaryFraction) :
    Footprint.rankedBitMemoCells rank program (fun key => (heap key).footprint)
      bits encode addressCells key memory =
      EditApproximation.rankedBitMemoCells rank program heap bits encode addressCells key memory := by
  have hall : ∀ level key, rank key = level → ∀ memory,
      Footprint.rankedBitMemoCells rank program (fun key => (heap key).footprint)
        bits encode addressCells key memory =
        EditApproximation.rankedBitMemoCells rank program heap bits encode addressCells key memory := by
    intro level
    induction level using Nat.strong_induction_on with
    | h level ih =>
      intro key hlevel memory
      rw [Footprint.rankedBitMemoCells, EditApproximation.rankedBitMemoCells]
      cases hf : (memory.lookupCosted (binaryMemoKey bits (encode key))).1 with
      | some value => rfl
      | none =>
        dsimp only
        congr 1
        rw [← footprint_runCells]
        apply Footprint.runCells_congr
        intro child previous
        exact ih (rank child.val) (hlevel ▸ child.property) child.val rfl previous
  exact hall (rank key) key rfl memory

end Heap
end OAI.EditApproximation.BitQuery
