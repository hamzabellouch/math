import OAI.Combinatorics.EditApproximation.Queries.QueryLocalSelectors
import OAI.Combinatorics.EditApproximation.Queries.QueryRefinementGather
import OAI.Combinatorics.EditApproximation.Queries.QueryRefinementFinish

namespace OAI

/-! The complete charged local refinement request: earlier history, shared
samples, selected current inputs and the final binary continuation. -/

namespace EditApproximation

section Local
variable {ι α : Type*} (source target : List α) {M : ℕ}
  (parent : TargetInterval source.length) (N P F exponent H Q eM eF : ℕ)
  (hP : 0 < P) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF)
  (tau a eta kappa delta : BinaryFraction) (t : ℕ)
  (parentInitial : TargetInterval target.length → BinaryFraction × ℕ)
  (child initial : Fin M → TargetInterval target.length → BinaryFraction × ℕ)
  (R : ℕ) (hc : ∀ i r, (child i r).2 ≤ R) (hi : ∀ i r, (initial i r).2 ≤ R)
  (draw : CountedCellGroupDraws M F Q)
  (integer : ℕ → TargetInterval target.length → ℕ × ℕ)
  (q : TargetInterval target.length)
  (readEarlier : (Fin M × ℕ × TargetInterval target.length) → BitQuery ι BinaryFraction)
  (readCurrent : (Fin M × TargetInterval target.length) → BitQuery ι BinaryFraction)

def queryLocalRefinement : BitQuery ι BinaryFraction :=
  queryRefinementGather source target parent N P F exponent Q eM eF hP hM hF a t parentInitial draw q
    readEarlier readCurrent
    (fun keys words => BinaryFraction.queryOnlineSelectWithWork source target parent N P F exponent H hP
      tau a eta kappa parentInitial child initial R hc hi t integer keys words q)
    (fun keys words => BinaryFraction.queryGroupSelectWithWork source target parent N P F exponent Q
      eM eF hP hM hF tau a parentInitial child initial R hc hi draw keys words q)
    (fun earlierKeys earlierWords groups online currentKeys currentWords =>
      BitQuery.compute (BinaryFraction.queryRefinementFinishWithWork parent N P F a delta parentInitial
        t earlierKeys earlierWords groups online currentKeys currentWords q))

theorem queryLocalRefinement_refines
    (expectedEarlier : (Fin M × ℕ × TargetInterval target.length) → FiniteQuery ι)
    (expectedCurrent : (Fin M × TargetInterval target.length) → FiniteQuery ι)
    (he : ∀ key, BitQuery.Refines (fun word value => word.value = value)
      (readEarlier key) (expectedEarlier key))
    (hr : ∀ key, BitQuery.Refines (fun word value => word.value = value)
      (readCurrent key) (expectedCurrent key)) :
    BitQuery.Refines (fun word value => word.value = value)
      (queryLocalRefinement source target parent N P F exponent H Q eM eF hP hM hF
        tau a eta kappa delta t parentInitial child initial R hc hi draw integer q readEarlier readCurrent)
      (localRefinementStepQuery source target parent N P F exponent H Q
        tau.value a.value eta.value kappa.value delta.value t
        (fun r => (parentInitial r).1.value) (fun i r => (child i r).1.value)
        (fun i r => (initial i r).1.value) (fun b cell scale sample => (draw b cell scale sample).1)
        (fun b r => (integer b r).1) q expectedEarlier expectedCurrent) := by
  classical
  let Rp := ∑ r, (parentInitial r).2
  have hp : ∀ r, (parentInitial r).2 ≤ Rp := fun r =>
    Finset.single_le_sum (f := fun r => (parentInitial r).2) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ r)
  unfold queryLocalRefinement localRefinementStepQuery
  apply queryRefinementGather_refines (expectedEarlier := expectedEarlier)
    (expectedCurrent := expectedCurrent)
    (expectedOnline := fun keys words => localOnlineCandidates source target parent N P F exponent H
      tau.value a.value eta.value kappa.value (fun r => (parentInitial r).1.value)
      (fun i r => (child i r).1.value) (fun i r => (initial i r).1.value)
      (fun i s r => finiteAnswerTable keys words (i, s, r)) (t - 1)
      (fun b r => (integer b r).1) q)
    (expectedSelected := fun keys words => localCellGroupActions source target parent N P F exponent Q
      tau.value a.value (fun r => (parentInitial r).1.value)
      (fun i r => (child i r).1.value) (fun i r => (initial i r).1.value)
      (fun i r => finiteAnswerTable keys words (i, r))
      (fun b cell scale sample => (draw b cell scale sample).1) q)
    (expectedNext := fun earlierKeys earlierWords groups online currentKeys currentWords =>
      .done (rationalRefinementUpdate delta.value
        (rationalMinimum
          (rationalBellman (fun r => (parentInitial r).1.value)
            (fun q r => targetEndpointDistance q r) (128 * F)
            (rationalActualWideActions parent
              (localRefinementRepresentatives N P F a.value (fun r => (parentInitial r).1.value) q) P)
            (fun input => finiteAnswerTable earlierKeys earlierWords (input.1, t - 1, input.2)) q)
          (groups.map (rationalActionValue (fun q r => targetEndpointDistance q r) (128 * F)
            (finiteAnswerTable currentKeys currentWords) q)))
        (rationalOnlineMinimum (online.map
          (rationalActionValue (fun q r => targetEndpointDistance q r) (128 * F)
            (finiteAnswerTable currentKeys currentWords) q)))))
    (R := Rp) (hR := hp) (he := he) (hc := hr)
  · intro keys words
    exact BinaryFraction.queryOnlineSelectWithWork_value source target parent N P F exponent H hP
      tau a eta kappa parentInitial child initial R hc hi t integer keys words q
  · intro keys words
    exact BinaryFraction.queryGroupSelectWithWork_value source target parent N P F exponent Q eM eF
      hP hM hF tau a parentInitial child initial R hc hi draw keys words q
  · intro earlierKeys earlierWords groups online currentKeys currentWords
    apply BitQuery.Refines.charge
    apply BitQuery.Refines.done
    simpa only [rationalWideStep, rationalWideStepCone, rationalBellman] using
      BinaryFraction.queryRefinementFinishWithWork_value_only parent N P F a delta parentInitial
        t earlierKeys earlierWords groups online currentKeys currentWords q hP

end Local
end EditApproximation

end OAI
