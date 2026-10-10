import OAI.Combinatorics.EditApproximation.Queries.QueryGroupSamples
import OAI.Combinatorics.EditApproximation.Binary.BitQuery
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! Complete scalar-source key generation uses the original dyadic
query window, cell order, scale order, and sample order. -/

namespace EditApproximation
namespace BinaryFraction



theorem queryGroupSourceKeysWithWork_value {n : ℕ} (M N F Q exponent eM eF : ℕ)
    (hM : M = 2 ^ eM) (hF : F = 2 ^ eF) (a value : BinaryFraction)
    (q : TargetInterval n) :
    (queryGroupSourceKeysWithWork M N F Q exponent eM eF hM hF a value q).1 =
      groupScalarKeys M F Q (localGroupQueryKeys N F exponent a.value (fun _ => value.value) q) := by
  simp only [queryGroupSourceKeysWithWork, arithmeticFlatMapWithWork_value,
    targetCellsWithWork_value, canonicalMulWithWork_value, inversePowerTwo_value, nat_value,
    naturalCeilingWithWork_value, queryGroupKeySamplesWithWork_value]
  conv_rhs => unfold localGroupQueryKeys
  rw [← queryExponentsWithWork_value N F a value]
  simp only [groupScalarKeys, List.flatMap_map, List.flatMap_assoc,
    List.flatMap_cons, List.flatMap_nil, List.append_nil]

end BinaryFraction



theorem queryGroupSourceGather_refines {ι β : Type*} {n : ℕ} {relation : β → ℚ → Prop}
    (M N F Q exponent eM eF : ℕ) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF)
    (a : BinaryFraction) (initial : TargetInterval n → BinaryFraction × ℕ) (q : TargetInterval n)
    (reader : GroupScalarKey M F Q → BitQuery ι BinaryFraction)
    (expectedReader : GroupScalarKey M F Q → FiniteQuery ι)
    (next : List (GroupScalarKey M F Q) → List BinaryFraction → BitQuery ι β)
    (expectedNext : List (GroupScalarKey M F Q) → List ℚ → FiniteQuery ι)
    (hr : ∀ key, BitQuery.Refines (fun word value => word.value = value)
      (reader key) (expectedReader key))
    (hn : ∀ words,
      let keys := groupScalarKeys M F Q
        (localGroupQueryKeys N F exponent a.value (fun r => (initial r).1.value) q)
      BitQuery.Refines relation (next keys words) (expectedNext keys (words.map BinaryFraction.value))) :
    BitQuery.Refines relation
      (queryGroupSourceGather M N F Q exponent eM eF hM hF a initial q reader next)
      (let keys := groupScalarKeys M F Q
        (localGroupQueryKeys N F exponent a.value (fun r => (initial r).1.value) q)
       FiniteQuery.collect expectedReader keys (expectedNext keys)) := by
  apply BitQuery.Refines.charge
  change BitQuery.Refines relation (.charge _ _) _
  apply BitQuery.Refines.charge
  change BitQuery.Refines relation (BitQuery.collect reader _ _) _
  rw [BinaryFraction.queryGroupSourceKeysWithWork_value]
  exact BitQuery.Refines.collect reader expectedReader hr _ _ _ hn

end EditApproximation

end OAI
