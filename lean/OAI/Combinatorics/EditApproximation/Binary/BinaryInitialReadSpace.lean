import OAI.Combinatorics.EditApproximation.Binary.BinaryInitialGuardSpace
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

namespace EditApproximation.BinaryFraction

section Reads
variable {n : ℕ} (read : TargetInterval n → List Bool × ℕ) (allocation : TargetInterval n → ℕ)



theorem initialGridReadAllocation_le_work (P : ℕ) (A : BinaryFraction) (radius : ℕ) (q : TargetInterval n) (b : ℕ)
    (ha : ∀ r, allocation r ≤ (read r).2) :
    initialGridReadAllocation read allocation P A radius q b ≤ (initialGridReadWithWork P A read radius q b).2 := by
  let spacing := (seedGridSpacingWithWork b P).1
  have hs := seedGridSpacingAllocation_le_work b P
  have hg := gridStateBoxAllocation_le_work n (bitWordValue spacing) radius q.lo q.hi
  have hf := filterAllocation_le_work
    (fun r => ((initialCenterGuardWithWork b (bitWordValue (read r).1) A).1,
      (initialCenterGuardWithWork b (bitWordValue (read r).1) A).2 + (read r).2))
    (fun r => initialCenterGuardAllocation b (bitWordValue (read r).1) A + allocation r)
    (gridStateBoxWithWork n (bitWordValue spacing) radius q.lo q.hi).1
    (fun r _ => Nat.add_le_add (initialCenterGuardAllocation_le_work b (bitWordValue (read r).1) A) (ha r))
  unfold initialGridReadAllocation initialGridReadWithWork
  dsimp only [spacing] at hg hf ⊢
  omega



theorem initialCentersReadAllocation_le_work (N P : ℕ) (A : BinaryFraction) (q : TargetInterval n)
    (ha : ∀ r, allocation r ≤ (read r).2) :
    initialCentersReadAllocation read allocation N P A q ≤ (initialCentersReadWithWork N P A read q).2 := by
  let Uq := bitWordValue (read q).1
  have hq := ha q
  have hd := dyadicScalesAllocation_le_work N
  have hf := filterAllocation_le_work (fun b => initialScaleGuardWithWork Uq b A)
    (fun b => initialScaleGuardAllocation Uq b A) (dyadicScalesWithWork N).1
    (fun b _ => initialScaleGuardAllocation_le_work Uq b A)
  have hm := arithmeticFlatMapAllocation_le_work (initialGridReadWithWork P A read Uq q)
    (initialGridReadAllocation read allocation P A Uq q)
    (filterWithWork (fun b => initialScaleGuardWithWork Uq b A) (dyadicScalesWithWork N).1).1
    (fun b _ => initialGridReadAllocation_le_work read allocation P A Uq q b ha)
  unfold initialCentersReadAllocation initialCentersReadWithWork
  dsimp only [Uq] at hf hm ⊢
  omega



theorem initialConeReadAllocation_le_work (sourceLength : ℕ) (a L : BinaryFraction) (query center : TargetInterval n)
    (ha : ∀ r, allocation r ≤ (read r).2) :
    initialConeReadAllocation read allocation sourceLength a L query center ≤
      (initialConeReadWithWork sourceLength read a L query center).2 := by
  have hr := ha center
  have hc := initialConeAllocation_le_work sourceLength (bitWordValue (read center).1) a L query center
  unfold initialConeReadAllocation initialConeReadWithWork
  dsimp only
  omega



theorem initialMinimumReadAllocation_le_work (sourceLength N F : ℕ) (a : BinaryFraction)
    (query : TargetInterval n) (centers : List (TargetInterval n)) (ha : ∀ r, allocation r ≤ (read r).2) :
    initialMinimumReadAllocation read allocation sourceLength N F a query centers ≤
      (initialMinimumReadWithWork sourceLength read N F a query centers).2 := by
  let L := (canonicalMulWithWork (nat 32) (nat F)).1
  let coefficient := (canonicalAddWithWork L one).1
  have hq := ha query
  have hz := naturalEqualAllocation_le_work (bitWordValue (read query).1) 0
  have hL := canonicalMulAllocation_le_work (nat 32) (nat F)
  have hc := canonicalAddAllocation_le_work L one
  have hf := canonicalMulAllocation_le_work coefficient (nat N)
  have hs := arithmeticMapAllocation_le_work (initialConeReadWithWork sourceLength read a L query)
    (initialConeReadAllocation read allocation sourceLength a L query) centers
    (fun center _ => initialConeReadAllocation_le_work read allocation sourceLength a L query center ha)
  have hm := minimumAllocation_le_work (canonicalMulWithWork coefficient (nat N)).1
    (arithmeticMapWithWork (initialConeReadWithWork sourceLength read a L query) centers).1
  unfold initialMinimumReadAllocation initialMinimumReadWithWork
  dsimp only
  split_ifs <;> dsimp only [L, coefficient] at hc hf hs hm ⊢ <;> omega



theorem initialProgramReadAllocation_le_work (sourceLength N P F : ℕ) (A a : BinaryFraction) (query : TargetInterval n)
    (ha : ∀ r, allocation r ≤ (read r).2) :
    initialProgramReadAllocation read allocation sourceLength N P F A a query ≤
      (initialProgramReadWithWork sourceLength N P F A a read query).2 := by
  have hc := initialCentersReadAllocation_le_work read allocation N P A query ha
  have hm := initialMinimumReadAllocation_le_work read allocation sourceLength N F a query
    (initialCentersReadWithWork N P A read query).1 ha
  unfold initialProgramReadAllocation initialProgramReadWithWork
  dsimp only
  omega



theorem cachedInitialProgramReadAllocation_le_work (sourceLength N P F : ℕ) (A a : BinaryFraction)
    (query : TargetInterval n) (ha : ∀ r, allocation r ≤ (read r).2) :
    cachedInitialProgramReadAllocation read allocation sourceLength N P F A a query ≤
      (cachedInitialProgramReadWithWork sourceLength N P F A a read query).2 :=
  finishCachedAllocation_le_work _ _ _ _ _ (initialProgramReadAllocation_le_work read allocation sourceLength N P F A a query ha)

end Reads
end EditApproximation.BinaryFraction

end OAI
