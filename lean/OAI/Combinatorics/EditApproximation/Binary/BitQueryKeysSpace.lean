import OAI.Combinatorics.EditApproximation.Binary.BitQuerySpace
import OAI.Combinatorics.EditApproximation.Binary.BitQueryKeys

namespace OAI

namespace EditApproximation.BitQuery.Heap

def mapKeysWithWork {ι κ β : Type*} (f : ι → κ × ℕ) (allocation : ι → ℕ)
    (ha : ∀ key, allocation key ≤ (f key).2)
    {program : BitQuery ι β} (heap : Heap program) : Heap (program.mapKeysWithWork f) :=
  match heap with
  | .done result => .done result
  | .read key next continuation =>
    chargeOf (allocation key) (ha key)
      (.read (f key).1 _ (fun word => (continuation word).mapKeysWithWork f allocation ha))
  | .charge localCells bound next => .charge localCells bound (next.mapKeysWithWork f allocation ha)

def restrictWithWork {ι : Type*} (P : ι → Prop)
    (test : ι → Bool × ℕ) (htest : ∀ key, (test key).1 = true ↔ P key)
    (allocation : ι → ℕ) (ha : ∀ key, allocation key ≤ (test key).2)
    {program : BitQuery ι BinaryFraction} (heap : Heap program) :
    Heap (program.restrictWithWork P test htest) :=
  match heap with
  | .done result => .done result
  | .charge localCells bound next => .charge localCells bound (next.restrictWithWork P test htest allocation ha)
  | .read key next continuation =>
    chargeOf (allocation key) (ha key)
      (by
        split
        · exact .read _ _ (fun word => (continuation word).restrictWithWork P test htest allocation ha)
        · exact (continuation (BinaryFraction.nat 0)).restrictWithWork P test htest allocation ha)


end EditApproximation.BitQuery.Heap

end OAI
