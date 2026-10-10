import OAI.Combinatorics.EditApproximation.Binary.BinaryPreparedLocalOnline
import OAI.Combinatorics.EditApproximation.Binary.BinaryPreparedLocalGroups
import OAI.Combinatorics.EditApproximation.Binary.BinaryCachedContinuation

namespace OAI

/-! Full stored-data local refinement kernel. All candidate lists are
built by their literal counted routines, then the Bellman/online update
is performed. No action-list equality premise is assumed. -/

namespace EditApproximation
namespace BinaryFraction

def preparedLocalKernelWithWork {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (N P F exponent H Q eM eF : ℕ)
    (hP : 0 < P) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF)
    (tau a eta kappa delta : BinaryFraction)
    (parentInitial : TargetInterval target.length → BinaryFraction)
    (childMass childInitial : Fin M → TargetInterval target.length → BinaryFraction)
    (old current : Fin M × TargetInterval target.length → BinaryFraction)
    (history : ℕ → Fin M × TargetInterval target.length → BinaryFraction) (t : ℕ)
    (draw : CellGroupDraws M F Q) (integer : ℕ → TargetInterval target.length → ℕ)
    (query : TargetInterval target.length) : BinaryFraction × ℕ :=
  let representatives := localRepresentativesWithWork N P F a parentInitial query
  let groups := preparedLocalCellGroupsWithWork source target parent N P F exponent Q eM eF hM hF hP
    tau a parentInitial childMass childInitial (fun i r => current (i, r)) draw query
  let online := preparedLocalOnlineActionsWithWork source target parent N P F exponent H hP tau a eta kappa
    parentInitial childMass childInitial history t integer query
  let result := physicalContinuationWithWork parent representatives.1 P F delta (parentInitial query)
    old current groups.1 online.1 query
  (result.1, representatives.2 + groups.2 + online.2 + result.2 + 4)

theorem preparedLocalKernelWithWork_value {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (N P F exponent H Q eM eF : ℕ)
    (hP : 0 < P) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF)
    (tau a eta kappa delta : BinaryFraction)
    (parentInitial : TargetInterval target.length → BinaryFraction)
    (childMass childInitial : Fin M → TargetInterval target.length → BinaryFraction)
    (old current : Fin M × TargetInterval target.length → BinaryFraction)
    (history : ℕ → Fin M × TargetInterval target.length → BinaryFraction) (t : ℕ)
    (draw : CellGroupDraws M F Q) (integer : ℕ → TargetInterval target.length → ℕ)
    (query : TargetInterval target.length) :
    (preparedLocalKernelWithWork source target parent N P F exponent H Q eM eF hP hM hF
      tau a eta kappa delta parentInitial childMass childInitial old current history t draw integer query).1.value =
      rationalLocalWideStep source target parent N P F exponent Q tau.value a.value delta.value
        (fun r => (parentInitial r).value) (fun i r => (childMass i r).value)
        (fun i r => (childInitial i r).value) (fun i r => (old (i, r)).value)
        (fun i r => (current (i, r)).value) draw
        (localOnlineCandidates source target parent N P F exponent H tau.value a.value eta.value kappa.value
          (fun r => (parentInitial r).value) (fun i r => (childMass i r).value)
          (fun i r => (childInitial i r).value) (fun i s r => (history s (i, r)).value) t integer query) query := by
  unfold preparedLocalKernelWithWork
  rw [physicalContinuationWithWork_value _ _ _ _ _ _ _ _ _ _ _ hP]
  rw [localRepresentativesWithWork_value N P F hP a parentInitial query,
    preparedLocalCellGroupsWithWork_value source target parent N P F exponent Q eM eF hM hF hP tau a
      parentInitial childMass childInitial (fun i r => current (i, r)) draw query,
    preparedLocalOnlineActionsWithWork_value source target parent N P F exponent H hP tau a eta kappa
      parentInitial childMass childInitial history t integer query]
  rfl

def cachedPreparedLocalKernelWithWork {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (N P F exponent H Q eM eF : ℕ)
    (hP : 0 < P) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF)
    (tau a eta kappa delta : BinaryFraction)
    (parentInitial : TargetInterval target.length → BinaryFraction)
    (childMass childInitial : Fin M → TargetInterval target.length → BinaryFraction)
    (old current : Fin M × TargetInterval target.length → BinaryFraction)
    (history : ℕ → Fin M × TargetInterval target.length → BinaryFraction) (t : ℕ)
    (draw : CellGroupDraws M F Q) (integer : ℕ → TargetInterval target.length → ℕ)
    (query : TargetInterval target.length) (base : List Bool) (hbase : 0 < bitWordValue base)
    (remaining : ℕ) : BinaryFraction × ℕ :=
  finishCachedWithWork
    (preparedLocalKernelWithWork source target parent N P F exponent H Q eM eF hP hM hF
      tau a eta kappa delta parentInitial childMass childInitial old current history t draw integer query)
    base hbase remaining

end BinaryFraction
end EditApproximation

end OAI
