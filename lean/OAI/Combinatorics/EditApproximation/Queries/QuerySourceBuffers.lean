import OAI.Combinatorics.EditApproximation.Queries.QuerySharedInputs
import OAI.Combinatorics.EditApproximation.Binary.BinaryGatheredValues
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! Source words are decoded only by counted buffer lookups, natural
floor and remainder routines. The resulting draws are exactly the draws
used by the semantic adaptive query, for every stored answer list. -/

namespace EditApproximation



@[simp] theorem queryGroupKeyEqualWithWork_value {M F Q : ℕ} (a b : GroupScalarKey M F Q) :
    (queryGroupKeyEqualWithWork a b).1 = true ↔ a = b := by
  simp only [queryGroupKeyEqualWithWork, Bool.and_eq_true, naturalEqualWithWork_value]
  constructor
  · rcases a with ⟨⟨a, c, d⟩, s, i⟩
    rcases b with ⟨⟨b, e, f⟩, t, j⟩
    rintro ⟨⟨⟨⟨hab, hce⟩, hdf⟩, hst⟩, hij⟩
    dsimp only at hab hce hdf hst hij
    cases hab
    cases hce
    cases hdf
    have hs : s = t := Fin.ext hst
    cases hs
    have hi : i = j := Fin.ext hij
    cases hi
    rfl
  · intro h
    subst b
    exact ⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩, rfl⟩



@[simp] theorem queryOnlineKeyEqualWithWork_value {n : ℕ} (a b : ℕ × TargetInterval n) :
    (queryOnlineKeyEqualWithWork a b).1 = true ↔ a = b := by
  simp only [queryOnlineKeyEqualWithWork, Bool.and_eq_true, naturalEqualWithWork_value,
    queryIntervalEqualWithWork_value, Prod.ext_iff]

namespace BinaryFraction



theorem queryGroupDrawReadWithWork_value {M F Q : ℕ} [NeZero M]
    (keys : List (GroupScalarKey M F Q)) (values : List BinaryFraction)
    (b : ℕ) (cell : ℕ × ℕ) (scale : Fin (groupDyadicScales M b F).length)
    (sample : Fin (groupSampleCount M Q b (groupDyadicScaleAt M b F scale))) :
    (queryGroupDrawReadWithWork keys values b cell scale sample).1 =
      groupDrawFromValues keys (values.map value) b cell scale sample := by
  apply Fin.ext
  simp only [queryGroupDrawReadWithWork,
    (binaryNaturalDivModWithWork_spec _ M (NeZero.pos M)).2,
    naturalFloorWithWork_value, gatheredWordLookupWithWork_value _ queryGroupKeyEqualWithWork_value,
    groupDrawFromValues, Fin.val_ofNat]



@[simp] theorem queryOnlineIntegerReadWithWork_value {n : ℕ} (keys : List (ℕ × TargetInterval n))
    (values : List BinaryFraction) (b : ℕ) (q : TargetInterval n) :
    (queryOnlineIntegerReadWithWork keys values b q).1 =
      ⌊finiteAnswerTable keys (values.map value) (b, q)⌋₊ := by
  simp only [queryOnlineIntegerReadWithWork, naturalFloorWithWork_value,
    gatheredWordLookupWithWork_value _ queryOnlineKeyEqualWithWork_value]

end BinaryFraction
end EditApproximation

end OAI
