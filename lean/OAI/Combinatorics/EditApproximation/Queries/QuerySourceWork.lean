import OAI.Combinatorics.EditApproximation.Queries.QueryGroupSources
import OAI.Combinatorics.EditApproximation.Queries.QueryOnlineSources

namespace OAI

/-! Exact execution counters for both source gathers. The online counter
includes construction of every range before issuing its random read. -/

namespace EditApproximation

theorem queryGroupSourceGather_work {ι β : Type*} {n : ℕ}
    (M N F Q exponent eM eF : ℕ) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF)
    (a : BinaryFraction) (initial : TargetInterval n → BinaryFraction × ℕ) (q : TargetInterval n)
    (reader : GroupScalarKey M F Q → BitQuery ι BinaryFraction)
    (next : List (GroupScalarKey M F Q) → List BinaryFraction → BitQuery ι β)
    (oracle : ι → BinaryFraction) (readWork : ι → ℕ) :
    let keys := BinaryFraction.queryGroupSourceKeysWithWork M N F Q exponent eM eF hM hF a
      (initial q).1 q
    (queryGroupSourceGather M N F Q exponent eM eF hM hF a initial q reader next).work oracle readWork =
      (initial q).2 + keys.2 +
        (keys.1.map fun key => (reader key).work oracle readWork + 3).sum +
        (next keys.1 (keys.1.map fun key => (reader key).value oracle)).work oracle readWork := by
  simp only [queryGroupSourceGather, BitQuery.work_bind, BitQuery.work_collect,
    BitQuery.compute, BitQuery.work, BitQuery.value, Nat.add_zero, Nat.add_assoc]

theorem queryOnlineSourceGather_work {ι β : Type*} {nx ny M : ℕ}
    (parent : TargetInterval nx) (N P F exponent H : ℕ) (hP : 0 < P)
    (tau a : BinaryFraction) (initial : TargetInterval ny → BinaryFraction × ℕ)
    (child : Fin M → TargetInterval ny → BinaryFraction × ℕ) (q : TargetInterval ny)
    (reader : (ℕ × TargetInterval ny) → ℕ → BitQuery ι BinaryFraction)
    (next : List (ℕ × TargetInterval ny) → List BinaryFraction → BitQuery ι β)
    (oracle : ι → BinaryFraction) (readWork : ι → ℕ) :
    let keys := BinaryFraction.queryOnlineKeysWithWork N P F hP a (initial q).1 q
    let range := BinaryFraction.queryOnlineRangeWithWork parent P exponent H tau child
    (queryOnlineSourceGather parent N P F exponent H hP tau a initial child q reader next).work
      oracle readWork =
      (initial q).2 + keys.2 +
        (keys.1.map fun key => (range key).2 + (reader key (range key).1).work oracle readWork + 3).sum +
        (next keys.1 (keys.1.map fun key => (reader key (range key).1).value oracle)).work oracle readWork := by
  simp only [queryOnlineSourceGather, BitQuery.work_bind, BitQuery.value_bind, BitQuery.work_collect,
    BitQuery.compute, BitQuery.work, BitQuery.value, Nat.add_zero, Nat.add_assoc]

end EditApproximation

end OAI
