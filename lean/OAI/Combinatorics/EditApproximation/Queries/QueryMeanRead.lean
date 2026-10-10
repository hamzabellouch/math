import OAI.Combinatorics.EditApproximation.Binary.BitQuery
import OAI.Combinatorics.EditApproximation.Binary.BinaryWarmupAverage
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! Counted averaging of the warmup words actually requested. The fixed
requested denominator is retained even in the simulation of arbitrary
intermediate answer lists. -/

namespace EditApproximation
namespace BinaryFraction



@[simp] theorem queryMeanWithWork_value (count : ℕ) (words : List BinaryFraction) :
    (queryMeanWithWork count words).1.value = (words.map value).sum / count := by
  simp only [queryMeanWithWork, divWithWork_value, sumListWithWork_value, nat_value]

theorem queryMeanWithWork_eq_average (count : ℕ) (words : List BinaryFraction)
    (h : words.length = count) : queryMeanWithWork count words = warmupAverageWithWork words := by
  subst count
  rfl

end BinaryFraction



theorem queryMeanRead_refines {ι : Type*} (count : ℕ)
    (reader : Fin count → BitQuery ι BinaryFraction) (expected : Fin count → FiniteQuery ι)
    (hr : ∀ i, BitQuery.Refines (fun word value => word.value = value) (reader i) (expected i)) :
    BitQuery.Refines (fun word value => word.value = value) (queryMeanRead count reader)
      (FiniteQuery.collect expected (List.ofFn fun i : Fin count => i)
        (fun words => .done (words.sum / count))) := by
  apply BitQuery.Refines.charge
  apply BitQuery.Refines.collect reader expected hr
  intro words
  exact .charge _ (.done (BinaryFraction.queryMeanWithWork_value count words))

theorem queryMeanRead_work {ι : Type*} (count : ℕ)
    (reader : Fin count → BitQuery ι BinaryFraction)
    (oracle : ι → BinaryFraction) (readWork : ι → ℕ) :
    (queryMeanRead count reader).work oracle readWork =
      count + 1 + ((List.ofFn fun i : Fin count => i).map
        (fun i => (reader i).work oracle readWork + 3)).sum +
      (BinaryFraction.queryMeanWithWork count
        ((List.ofFn fun i : Fin count => i).map fun i => (reader i).value oracle)).2 := by
  simp only [queryMeanRead, BitQuery.work_collect, BitQuery.compute, BitQuery.work,
    Nat.add_zero, Nat.add_assoc]

end EditApproximation

end OAI
