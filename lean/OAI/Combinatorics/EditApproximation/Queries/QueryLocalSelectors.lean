import OAI.Combinatorics.EditApproximation.Binary.BinaryLocalSourceValues
import OAI.Combinatorics.EditApproximation.Queries.QueryDataBuffers

namespace OAI

/-! The concrete selectors of the adaptive local program. Source and table
lookups are evaluated by their counted finite-buffer routines. Their value
identities hold even for arbitrary gathered answer lists. -/

namespace EditApproximation
namespace BinaryFraction

section Selectors
variable {α : Type*} (source target : List α) {M : ℕ}
  (parent : TargetInterval source.length) (N P F exponent H Q eM eF : ℕ)
  (hP : 0 < P) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF)
  (tau a eta kappa : BinaryFraction)
  (parentInitial : TargetInterval target.length → BinaryFraction × ℕ)
  (child initial : Fin M → TargetInterval target.length → BinaryFraction × ℕ)
  (R : ℕ) (hc : ∀ i r, (child i r).2 ≤ R) (hi : ∀ i r, (initial i r).2 ≤ R)

def queryOnlineSelectWithWork (t : ℕ)
    (integer : ℕ → TargetInterval target.length → ℕ × ℕ)
    (keys : List (Fin M × ℕ × TargetInterval target.length)) (words : List BinaryFraction)
    (q : TargetInterval target.length) :=
  preparedLocalOnlineActionsSourceWithWork source target parent P F exponent H hP tau a eta kappa
    parentInitial child initial (queryHistoryReadWithWork keys words) R hc hi (t - 1) integer N q

theorem queryOnlineSelectWithWork_value (t : ℕ)
    (integer : ℕ → TargetInterval target.length → ℕ × ℕ)
    (keys : List (Fin M × ℕ × TargetInterval target.length)) (words : List BinaryFraction)
    (q : TargetInterval target.length) :
    ((queryOnlineSelectWithWork source target parent N P F exponent H hP tau a eta kappa
      parentInitial child initial R hc hi t integer keys words q).1.map BinaryBellmanAction.decode) =
      localOnlineCandidates source target parent N P F exponent H tau.value a.value eta.value kappa.value
        (fun r => (parentInitial r).1.value) (fun i r => (child i r).1.value)
        (fun i r => (initial i r).1.value)
        (fun i s r => finiteAnswerTable keys (words.map value) (i, s, r))
        (t - 1) (fun b r => (integer b r).1) q := by
  unfold queryOnlineSelectWithWork
  rw [preparedLocalOnlineActionsSourceWithWork_semantic_value]
  rw [preparedLocalOnlineActionsWithWork_value]
  simp only [queryHistoryReadWithWork_value]

def queryGroupSelectWithWork (draw : CountedCellGroupDraws M F Q)
    (keys : List (Fin M × TargetInterval target.length)) (words : List BinaryFraction)
    (q : TargetInterval target.length) :=
  preparedLocalCellGroupsSourceWithWork source target parent P F exponent Q eM eF hM hF hP tau a
    parentInitial child initial (queryChildReadWithWork keys words) R hc hi N draw q

theorem queryGroupSelectWithWork_value (draw : CountedCellGroupDraws M F Q)
    (keys : List (Fin M × TargetInterval target.length)) (words : List BinaryFraction)
    (q : TargetInterval target.length) :
    ((queryGroupSelectWithWork source target parent N P F exponent Q eM eF hP hM hF tau a
      parentInitial child initial R hc hi draw keys words q).1.map BinaryBellmanAction.decode) =
      localCellGroupActions source target parent N P F exponent Q tau.value a.value
        (fun r => (parentInitial r).1.value) (fun i r => (child i r).1.value)
        (fun i r => (initial i r).1.value)
        (fun i r => finiteAnswerTable keys (words.map value) (i, r))
        (fun b cell scale sample => (draw b cell scale sample).1) q := by
  unfold queryGroupSelectWithWork
  rw [preparedLocalCellGroupsSourceWithWork_semantic_value]
  rw [preparedLocalCellGroupsWithWork_value]
  simp only [queryChildReadWithWork_value]

end Selectors
end BinaryFraction
end EditApproximation

end OAI
