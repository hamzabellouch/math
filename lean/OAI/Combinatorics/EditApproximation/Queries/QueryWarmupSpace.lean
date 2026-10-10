import OAI.Combinatorics.EditApproximation.Queries.QueryGatherSpace
import OAI.Combinatorics.EditApproximation.Queries.QueryContinuationSpace
import OAI.Combinatorics.EditApproximation.Queries.QueryWarmupProgram
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

namespace EditApproximation
namespace BinaryFraction



theorem queryOverrideParentReadAllocation_le_work {n : ℕ} (value : BinaryFraction) (q : TargetInterval n)
    (keys : List (TargetInterval n)) (words : List BinaryFraction) (r : TargetInterval n) :
    queryOverrideParentReadAllocation q keys words r ≤
      (queryOverrideParentReadWithWork value q keys words r).2 := by
  have he := queryIntervalEqualAllocation_le_work r q
  have hp := queryParentReadAllocation_le_work keys words r
  unfold queryOverrideParentReadAllocation queryOverrideParentReadWithWork
  dsimp only
  split_ifs <;> dsimp only <;> omega

end BinaryFraction
open BitQuery BinaryFraction

def queryWarmupProgramHeap {ι : Type*} {nx ny M : ℕ} (parent : TargetInterval nx)
    (N P F : ℕ) (a : BinaryFraction)
    (initialRead : TargetInterval ny → BitQuery ι BinaryFraction)
    (childRead : (Fin M × TargetInterval ny) → BitQuery ι BinaryFraction) (q : TargetInterval ny)
    (hi : ∀ r, Heap (initialRead r)) (hc : ∀ key, Heap (childRead key)) :
    Heap (queryWarmupProgram parent N P F a initialRead childRead q) :=
  (hi q).bind _ fun value =>
    (Heap.computeOf (queryRawCentersWithWork N P F a value q)
      (queryRawCentersAllocation N P F a value q) (queryRawCentersAllocation_le_work N P F a value q)).bind _ fun centers =>
      Heap.collect initialRead hi centers _ fun words =>
        let initial := queryOverrideParentReadWithWork value q centers words
        let allocation := queryOverrideParentReadAllocation q centers words
        let halloc := queryOverrideParentReadAllocation_le_work value q centers words
        (Heap.computeOf (queryWarmupInputsWithWork M parent N P F a initial q)
          (queryWarmupInputsAllocation M parent N P F a initial allocation q)
          (queryWarmupInputsAllocation_le_work M parent N P F a initial allocation q halloc)).bind _ fun inputs =>
            Heap.collect childRead hc inputs _ fun childWords =>
              Heap.computeOf (localWarmupReadKernelWithWork parent N P F a initial
                (fun input => queryChildReadWithWork inputs childWords input.1 input.2) q)
                (localWarmupReadAllocation parent N P F a initial allocation
                  (fun input => queryChildReadWithWork inputs childWords input.1 input.2)
                  (fun input => queryChildReadAllocation inputs childWords input.1 input.2) q)
                (localWarmupReadAllocation_le_work parent N P F a initial allocation
                  (fun input => queryChildReadWithWork inputs childWords input.1 input.2)
                  (fun input => queryChildReadAllocation inputs childWords input.1 input.2) q halloc
                  (fun input => queryChildReadAllocation_le_work inputs childWords input.1 input.2))

end EditApproximation

end OAI
