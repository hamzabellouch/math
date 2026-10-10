import OAI.Combinatorics.EditApproximation.Binary.BinaryInitialReadSpace
import OAI.Combinatorics.EditApproximation.Queries.QueryGatherSpace
import OAI.Combinatorics.EditApproximation.Queries.QueryInitialConeProgram
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

namespace EditApproximation.BinaryFraction



theorem queryInitialConeCentersAllocation_le_work {n : ℕ} (N P : ℕ) (A value : BinaryFraction)
    (q : TargetInterval n) :
    queryInitialConeCentersAllocation N P A value q ≤ (queryInitialConeCentersWithWork N P A value q).2 := by
  let radius := (naturalCeilingWithWork value).1
  let build := fun b =>
    let spacing := (seedGridSpacingWithWork b P).1
    let states := gridStateBoxWithWork n (bitWordValue spacing) (bitWordValue radius) q.lo q.hi
    (states.1, (seedGridSpacingWithWork b P).2 + states.2 + 1)
  have hr := naturalCeilingAllocation_le_work value
  have hd := dyadicScalesAllocation_le_work N
  have hf := filterAllocation_le_work (fun b => initialScaleGuardWithWork (bitWordValue radius) b A)
    (fun b => initialScaleGuardAllocation (bitWordValue radius) b A) (dyadicScalesWithWork N).1
    (fun b _ => initialScaleGuardAllocation_le_work (bitWordValue radius) b A)
  have hm := arithmeticFlatMapAllocation_le_work build
    (fun b => seedGridSpacingAllocation b P + gridStateBoxAllocation n
      (bitWordValue (seedGridSpacingWithWork b P).1) (bitWordValue radius) q.lo q.hi)
    (filterWithWork (fun b => initialScaleGuardWithWork (bitWordValue radius) b A) (dyadicScalesWithWork N).1).1 (by
      intro b _
      have hs := seedGridSpacingAllocation_le_work b P
      have hg := gridStateBoxAllocation_le_work n (bitWordValue (seedGridSpacingWithWork b P).1) (bitWordValue radius) q.lo q.hi
      dsimp only [build]
      omega)
  unfold queryInitialConeCentersAllocation queryInitialConeCentersWithWork
  dsimp only [build, radius] at hf hm ⊢
  omega



theorem queryInitialSeedReadAllocation_le_work {n : ℕ} (value : BinaryFraction) (q : TargetInterval n)
    (keys : List (TargetInterval n)) (words : List BinaryFraction) (r : TargetInterval n) :
    queryInitialSeedReadAllocation value q keys words r ≤ (queryInitialSeedReadWithWork value q keys words r).2 := by
  have he := queryIntervalEqualAllocation_le_work r q
  have hv := naturalCeilingAllocation_le_work value
  have hp := queryParentReadAllocation_le_work keys words r
  have hc := naturalCeilingAllocation_le_work (queryParentReadWithWork keys words r).1
  unfold queryInitialSeedReadAllocation queryInitialSeedReadWithWork
  dsimp only
  split_ifs <;> dsimp only <;> omega

end EditApproximation.BinaryFraction

namespace EditApproximation
open BitQuery BinaryFraction

def queryInitialConeProgramAtHeap {ι : Type*} {n : ℕ} (sourceLength N P F : ℕ) (A a : BinaryFraction)
    (reader : TargetInterval n → BitQuery ι BinaryFraction) (q : TargetInterval n)
    (hr : ∀ r, Heap (reader r)) : Heap (queryInitialConeProgramAt sourceLength N P F A a reader q) :=
  (hr q).bind _ fun value =>
    (Heap.computeOf (queryInitialConeCentersWithWork N P A value q)
      (queryInitialConeCentersAllocation N P A value q)
      (queryInitialConeCentersAllocation_le_work N P A value q)).bind _ fun keys =>
        Heap.collect reader hr keys _ fun words =>
          Heap.computeOf (cachedInitialProgramReadWithWork sourceLength N P F A a
            (queryInitialSeedReadWithWork value q keys words) q)
            (cachedInitialProgramReadAllocation (queryInitialSeedReadWithWork value q keys words)
              (queryInitialSeedReadAllocation value q keys words) sourceLength N P F A a q)
            (cachedInitialProgramReadAllocation_le_work (queryInitialSeedReadWithWork value q keys words)
              (queryInitialSeedReadAllocation value q keys words) sourceLength N P F A a q
              (queryInitialSeedReadAllocation_le_work value q keys words))

end EditApproximation

end OAI
