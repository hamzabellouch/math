import OAI.Combinatorics.EditApproximation.Queries.QueryLocalSelectors
import OAI.Combinatorics.EditApproximation.Binary.BinaryPreparedActionStorage
import OAI.Combinatorics.EditApproximation.Binary.BinaryPreparedListBounds

namespace OAI

namespace EditApproximation.BinaryFraction
section Selectors
variable {α : Type*} (source target : List α) {M : ℕ}
  (parent : TargetInterval source.length) (N P F exponent H Q eM eF : ℕ)
  (hP : 0 < P) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF)
  (tau a eta kappa : BinaryFraction)
  (parentInitial : TargetInterval target.length → BinaryFraction × ℕ)
  (child initial : Fin M → TargetInterval target.length → BinaryFraction × ℕ)
  (R : ℕ) (hc : ∀ i r, (child i r).2 ≤ R) (hi : ∀ i r, (initial i r).2 ≤ R)

theorem queryGroupSelectWithWork_geometry (draw : CountedCellGroupDraws M F Q)
    (keys : List (Fin M × TargetInterval target.length)) (words : List BinaryFraction)
    (q : TargetInterval target.length) (B : ℕ) (hN : Nat.size N ≤ B)
    (hn : Nat.size target.length + 2 ≤ B) (hw : 0 ≤ (parentInitial q).1.value) :
    let selected := queryGroupSelectWithWork source target parent N P F exponent Q eM eF hP hM hF
      tau a parentInitial child initial R hc hi draw keys words q
    selected.1.length ≤ (B + 1) * ((32 * F + 2) * 2 ^ exponent + 2) ^ 2 ∧
    ∀ action ∈ selected.1, action.connection.width ≤ connectionWordBudget M B := by
  have hv := preparedLocalCellGroupsSourceWithWork_semantic_value source target parent P F exponent Q
    eM eF hM hF hP tau a parentInitial child initial (queryChildReadWithWork keys words) R hc hi N draw q
  have hl := preparedLocalCellGroupsWithWork_length_le source target parent N P F exponent Q eM eF B
    hM hF hP tau a (fun r => (parentInitial r).1) (fun i r => (child i r).1)
    (fun i r => (initial i r).1) (fun i r => (queryChildReadWithWork keys words i r).1)
    (fun b cell scale sample => (draw b cell scale sample).1) q hN hw
  have hc' := preparedLocalCellGroupsWithWork_connection source target parent N P F exponent Q eM eF
    hM hF hP tau a (fun r => (parentInitial r).1) (fun i r => (child i r).1)
    (fun i r => (initial i r).1) (fun i r => (queryChildReadWithWork keys words i r).1)
    (fun b cell scale sample => (draw b cell scale sample).1) q B hn
  simpa only [queryGroupSelectWithWork, hv] using And.intro hl hc'

theorem queryOnlineSelectWithWork_geometry (t : ℕ)
    (integer : ℕ → TargetInterval target.length → ℕ × ℕ)
    (keys : List (Fin M × ℕ × TargetInterval target.length)) (words : List BinaryFraction)
    (q : TargetInterval target.length) (B : ℕ) (hN : Nat.size N ≤ B) :
    let selected := queryOnlineSelectWithWork source target parent N P F exponent H hP tau a eta kappa
      parentInitial child initial R hc hi t integer keys words q
    selected.1.length ≤ B + 1 ∧ ∀ action ∈ selected.1, action.connection = zero := by
  have hv := preparedLocalOnlineActionsSourceWithWork_semantic_value source target parent P F exponent H
    hP tau a eta kappa parentInitial child initial (queryHistoryReadWithWork keys words) R hc hi
    (t - 1) integer N q
  have hl := preparedLocalOnlineActionsWithWork_length_le source target parent N P F exponent H B hP
    tau a eta kappa (fun r => (parentInitial r).1) (fun i r => (child i r).1)
    (fun i r => (initial i r).1) (fun s input => (queryHistoryReadWithWork keys words s input).1)
    (t - 1) (fun b r => (integer b r).1) q hN
  have hc' := preparedLocalOnlineActionsWithWork_connection source target parent N P F exponent H hP
    tau a eta kappa (fun r => (parentInitial r).1) (fun i r => (child i r).1)
    (fun i r => (initial i r).1) (fun s input => (queryHistoryReadWithWork keys words s input).1)
    (t - 1) (fun b r => (integer b r).1) q
  simpa only [queryOnlineSelectWithWork, hv] using And.intro hl hc'

end Selectors
end EditApproximation.BinaryFraction

end OAI
