import OAI.Combinatorics.EditApproximation.Binary.BinaryLocalGroupSourceSpace
import OAI.Combinatorics.EditApproximation.Binary.BinaryLocalOnlineSourceSpace
import OAI.Combinatorics.EditApproximation.Queries.QueryLocalSelectors

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
  (parentAllocation : TargetInterval target.length → ℕ)
  (childAllocation initialAllocation : Fin M → TargetInterval target.length → ℕ)

def queryOnlineSelectAllocation (t : ℕ)
    (integer : ℕ → TargetInterval target.length → ℕ × ℕ)
    (integerAllocation : ℕ → TargetInterval target.length → ℕ)
    (keys : List (Fin M × ℕ × TargetInterval target.length)) (words : List BinaryFraction)
    (q : TargetInterval target.length) : ℕ :=
  preparedLocalOnlineActionsSourceAllocation source target parent P F exponent H hP tau a eta kappa
    parentInitial child initial (queryHistoryReadWithWork keys words) R hc hi (t - 1) integer
    parentAllocation childAllocation initialAllocation (queryHistoryReadAllocation keys words)
    integerAllocation N q

theorem queryOnlineSelectAllocation_le_work (t : ℕ)
    (integer : ℕ → TargetInterval target.length → ℕ × ℕ)
    (integerAllocation : ℕ → TargetInterval target.length → ℕ)
    (keys : List (Fin M × ℕ × TargetInterval target.length)) (words : List BinaryFraction)
    (q : TargetInterval target.length)
    (hp : ∀ r, parentAllocation r ≤ (parentInitial r).2)
    (hca : ∀ i r, childAllocation i r ≤ (child i r).2)
    (hia : ∀ i r, initialAllocation i r ≤ (initial i r).2)
    (hint : ∀ b r, integerAllocation b r ≤ (integer b r).2) :
    queryOnlineSelectAllocation source target parent N P F exponent H hP tau a eta kappa
      parentInitial child initial R hc hi parentAllocation childAllocation initialAllocation
      t integer integerAllocation keys words q ≤
      3 * (queryOnlineSelectWithWork source target parent N P F exponent H hP tau a eta kappa
        parentInitial child initial R hc hi t integer keys words q).2 :=
  preparedLocalOnlineActionsSourceAllocation_le_work source target parent P F exponent H hP tau a eta kappa
    parentInitial child initial (queryHistoryReadWithWork keys words) R hc hi (t - 1) integer
    parentAllocation childAllocation initialAllocation (queryHistoryReadAllocation keys words)
    integerAllocation N q hp hca hia (queryHistoryReadAllocation_le_work keys words) hint

def queryGroupSelectAllocation (draw : CountedCellGroupDraws M F Q)
    (drawAllocation : CellGroupSourceAllocations M F Q)
    (keys : List (Fin M × TargetInterval target.length)) (words : List BinaryFraction)
    (q : TargetInterval target.length) : ℕ :=
  preparedLocalCellGroupsSourceAllocation source target parent P F exponent Q eM eF hM hF hP tau a
    parentInitial child initial (queryChildReadWithWork keys words) R hc hi
    parentAllocation childAllocation initialAllocation (queryChildReadAllocation keys words)
    draw drawAllocation N q

theorem queryGroupSelectAllocation_le_work (draw : CountedCellGroupDraws M F Q)
    (drawAllocation : CellGroupSourceAllocations M F Q)
    (keys : List (Fin M × TargetInterval target.length)) (words : List BinaryFraction)
    (q : TargetInterval target.length)
    (hp : ∀ r, parentAllocation r ≤ (parentInitial r).2)
    (hca : ∀ i r, childAllocation i r ≤ (child i r).2)
    (hia : ∀ i r, initialAllocation i r ≤ (initial i r).2)
    (hd : ∀ b cell t i, drawAllocation b cell t i ≤ (draw b cell t i).2) :
    queryGroupSelectAllocation source target parent N P F exponent Q eM eF hP hM hF tau a
      parentInitial child initial R hc hi parentAllocation childAllocation initialAllocation
      draw drawAllocation keys words q ≤
      (queryGroupSelectWithWork source target parent N P F exponent Q eM eF hP hM hF tau a
        parentInitial child initial R hc hi draw keys words q).2 :=
  preparedLocalCellGroupsSourceAllocation_le_work source target parent P F exponent Q eM eF hM hF hP tau a
    parentInitial child initial (queryChildReadWithWork keys words) R hc hi
    parentAllocation childAllocation initialAllocation (queryChildReadAllocation keys words)
    draw drawAllocation N q hp hca hia (queryChildReadAllocation_le_work keys words) hd

end Selectors
end EditApproximation.BinaryFraction

end OAI
