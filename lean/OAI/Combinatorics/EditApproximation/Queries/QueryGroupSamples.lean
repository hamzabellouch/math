import OAI.Combinatorics.EditApproximation.Queries.QueryInitialSupport
import OAI.Combinatorics.EditApproximation.Geometry.LocalGroupSourceQuery
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! Group sample coordinates are enumerated from the computed dyadic
scale array and binary sample counts. Equalities used in index casts are
proofs only; the loop bounds are the values just computed. -/

namespace EditApproximation



@[simp] theorem queryFinRange_value (n m : ℕ) (h : n = m) :
    queryFinRange n m h = List.finRange m := by
  subst m
  simp only [queryFinRange, Fin.eta, List.map_id']

namespace BinaryFraction



@[simp] theorem queryScaleAt_value (words : List BinaryFraction) (scales : List ℚ)
    (h : words.map value = scales) (i : Fin scales.length) :
    (queryScaleAt words scales h i).value = scales[i.val] := by
  subst scales
  simp only [queryScaleAt, List.getElem_map]

theorem queryGroupScaleAt_value (M b F : ℕ) (words : List BinaryFraction)
    (h : words.map value = groupDyadicScales M b F)
    (i : Fin (groupDyadicScales M b F).length) :
    (queryScaleAt words (groupDyadicScales M b F) h i).value = groupDyadicScaleAt M b F i :=
  queryScaleAt_value words (groupDyadicScales M b F) h i



theorem queryGroupKeySamplesWithWork_value (M F Q eM eb eF : ℕ)
    (hM : M = 2 ^ eM) (hF : F = 2 ^ eF) (cell : ℕ × ℕ) :
    (queryGroupKeySamplesWithWork M F Q eM eb eF hM hF cell).1 =
      groupScalarKeys M F Q [(2 ^ eb, cell)] := by
  simp only [queryGroupKeySamplesWithWork, arithmeticFlatMapWithWork_value,
    arithmeticMapWithWork_value, queryFinRange_value, groupScalarKeys,
    List.flatMap_cons, List.flatMap_nil, List.append_nil]

end BinaryFraction
end EditApproximation

end OAI
