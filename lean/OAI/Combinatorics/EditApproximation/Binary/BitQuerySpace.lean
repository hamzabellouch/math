import OAI.Combinatorics.EditApproximation.Binary.BitQuery

namespace OAI

/-! Allocation annotations for the actual adaptive query. Charge annotations
carry the concrete routine's allocation bound; reads reserve three cells for
its suspended continuation and result pointer. Charge transitions are tail
transitions. Summing all allocations bounds simultaneously live cells even
if no temporary cell is reclaimed until the query returns. -/

namespace EditApproximation.BitQuery

inductive Heap {ι β : Type*} : BitQuery ι β → Type _ where
  | done (value : β) : Heap (.done value)
  | read (key : ι) (next : BinaryFraction → BitQuery ι β)
      (continuation : ∀ word, Heap (next word)) : Heap (.read key next)
  | charge {steps : ℕ} {next : BitQuery ι β} (cells : ℕ)
      (bound : cells ≤ 3 * steps) (continuation : Heap next) : Heap (.charge steps next)

namespace Heap

def cells {ι β : Type*} {program : BitQuery ι β} (oracle : ι → BinaryFraction) : Heap program → ℕ
  | .done _ => 0
  | .read key _ next => 3 + cells oracle (next (oracle key))
  | .charge localCells _ next => localCells + cells oracle next

theorem cells_le_work {ι β : Type*} {program : BitQuery ι β} (oracle : ι → BinaryFraction)
    (heap : Heap program) : heap.cells oracle ≤ 3 * program.work oracle (fun _ => 1) := by
  induction heap with
  | done result => exact le_rfl
  | read key next heap ih =>
    have h := ih (oracle key)
    simp only [cells, work]
    omega
  | charge localCells bound next ih =>
    simp only [cells, work]
    omega

def bind {ι α β : Type*} {program : BitQuery ι α} (heap : Heap program)
    (next : α → BitQuery ι β) (allocation : ∀ value, Heap (next value)) : Heap (program.bind next) :=
  match heap with
  | .done result => allocation result
  | .read key continuation stored => .read key _ (fun word => (stored word).bind next allocation)
  | .charge localCells bound tail => .charge localCells bound (tail.bind next allocation)

def compute {ι β : Type*} (execution : β × ℕ) (allocation : ℕ)
    (bound : allocation ≤ 3 * execution.2) : Heap (BitQuery.compute (ι := ι) execution) :=
  .charge allocation bound (.done execution.1)

def chargeOf {ι β : Type*} {steps : ℕ} {program : BitQuery ι β} (allocation : ℕ)
    (bound : allocation ≤ steps) (tail : Heap program) : Heap (.charge steps program) :=
  .charge allocation (by omega) tail

def computeOf {ι β : Type*} (execution : β × ℕ) (allocation : ℕ)
    (bound : allocation ≤ execution.2) : Heap (BitQuery.compute (ι := ι) execution) :=
  compute execution allocation (by omega)

def collect {ι κ β : Type*} (reader : κ → BitQuery ι BinaryFraction)
    (allocation : ∀ key, Heap (reader key)) :
    (inputs : List κ) → (next : List BinaryFraction → BitQuery ι β) →
      (∀ words, Heap (next words)) → Heap (BitQuery.collect reader inputs next)
  | [], _, continuation => continuation []
  | key :: rest, next, continuation =>
    (allocation key).bind _ fun word => .charge 1 (by decide)
      (collect reader allocation rest (fun words => next (word :: words))
        (fun words => continuation (word :: words)))

end Heap
end EditApproximation.BitQuery

end OAI
