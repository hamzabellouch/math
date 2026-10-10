import OAI.Combinatorics.EditApproximation.Coarse.CoarseArraySimulation
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

namespace EditApproximation
namespace BinaryFraction

/-- Read one array cell; absent arrays represent exact zero. -/


 theorem coarseBinaryRead_value (array : CoarseBinaryArray) (i : ℕ) :
    (coarseBinaryRead array i).value = ((coarseBinaryContents array).getD [])[i]?.getD 0 := by
  cases array with
  | none => simp only [coarseBinaryRead, nat_value, Nat.cast_zero, coarseBinaryContents,
      Option.map_none, Option.getD_none, List.getElem?_nil]
  | some cells =>
    simp only [coarseBinaryRead, coarseBinaryContents, Option.map_some, Option.getD_some,
      List.getElem?_map]
    cases cells[i]? <;> simp only [ Option.getD_none, Option.map_none, nat_value,
      Nat.cast_zero, Option.getD_some, Option.map_some]

 theorem coarseBinaryRead_rep {n : ℕ} (array : CoarseBinaryArray) (spec : CoarseStoredArray n)
    (h : CoarseArrayRep array spec) (i : Fin n) :
    (coarseBinaryRead array i.val).value = coarseStoredRead spec i := by
  rw [coarseBinaryRead_value, h]
  cases spec with
  | none => rfl
  | some cells =>
    have hi : i.val < cells.1.length := by rw [cells.2]; exact i.isLt
    simp only [coarseRationalContents, Option.map_some, Option.getD_some, List.getElem?_eq_getElem hi,
      Option.getD_some, coarseStoredRead]

end BinaryFraction
end EditApproximation

end OAI
