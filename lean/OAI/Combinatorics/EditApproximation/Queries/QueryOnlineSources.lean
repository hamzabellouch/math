import OAI.Combinatorics.EditApproximation.Queries.QueryInitialGather
import OAI.Combinatorics.EditApproximation.Binary.BinaryBandReads
import OAI.Combinatorics.EditApproximation.Binary.BinaryKeyedOnline
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! An online random-source range is computed from the gathered mass
words before the source is requested. Band construction, dimension,
eighty-fold power, and triangular mass are all charged. -/

namespace EditApproximation
namespace BinaryFraction



theorem queryOnlineRangeWithWork_value {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (P exponent H : ℕ) (hP : 0 < P)
    (tau : BinaryFraction) (child : Fin M → TargetInterval target.length → BinaryFraction × ℕ)
    (key : ℕ × TargetInterval target.length) (R : ℕ) (hR : ∀ i r, (child i r).2 ≤ R) :
    (queryOnlineRangeWithWork parent P exponent H tau child key).1 =
      keyedOnlineSourceRange source target parent P exponent H tau.value
        (fun i r => (child i r).1.value) key := by
  have hb := (preparedRepresentativeReadWithWork_eq_cost parent key.2
    (parent.hi - parent.lo) key.1 P tau (inversePowerTwo exponent) child R hR).1
  simp only [queryOnlineRangeWithWork, saturatingSubtractWithWork_value, hb,
    triangularMassWithWork_value, bitPowerWithWork_value, bitWordValue_bits,
    onlineIndexSetupWithWork_value, listedBandCoordinates_length,
    preparedRepresentativeWithWork_value source target parent key.2 key.1 P hP,
    inversePowerTwo_value, keyedOnlineSourceRange, keyedOnlineBandG]

end BinaryFraction



theorem queryOnlineSourceGather_refines {ι β α : Type*} (source target : List α) {M : ℕ}
    {relation : β → ℚ → Prop} (parent : TargetInterval source.length)
    (N P F exponent H : ℕ) (hP : 0 < P) (tau a : BinaryFraction)
    (initial : TargetInterval target.length → BinaryFraction × ℕ)
    (child : Fin M → TargetInterval target.length → BinaryFraction × ℕ)
    (q : TargetInterval target.length) (R : ℕ) (hR : ∀ i r, (child i r).2 ≤ R)
    (reader : (ℕ × TargetInterval target.length) → ℕ → BitQuery ι BinaryFraction)
    (expectedReader : (ℕ × TargetInterval target.length) → ℕ → FiniteQuery ι)
    (next : List (ℕ × TargetInterval target.length) → List BinaryFraction → BitQuery ι β)
    (expectedNext : List (ℕ × TargetInterval target.length) → List ℚ → FiniteQuery ι)
    (hr : ∀ key range, BitQuery.Refines (fun word value => word.value = value)
      (reader key range) (expectedReader key range))
    (hn : ∀ words,
      let keys := localOnlineSourceKeys N P F a.value (fun r => (initial r).1.value) q
      BitQuery.Refines relation (next keys words) (expectedNext keys (words.map BinaryFraction.value))) :
    BitQuery.Refines relation
      (queryOnlineSourceGather parent N P F exponent H hP tau a initial child q reader next)
      (let keys := localOnlineSourceKeys N P F a.value (fun r => (initial r).1.value) q
       FiniteQuery.collect (fun key => expectedReader key
          (keyedOnlineSourceRange source target parent P exponent H tau.value
            (fun i r => (child i r).1.value) key)) keys (expectedNext keys)) := by
  apply BitQuery.Refines.charge
  change BitQuery.Refines relation (.charge _ _) _
  apply BitQuery.Refines.charge
  change BitQuery.Refines relation (BitQuery.collect _ _ _) _
  rw [BinaryFraction.queryOnlineKeysWithWork_value]
  apply BitQuery.Refines.collect
  · intro key
    change BitQuery.Refines _ (.charge _ _) _
    apply BitQuery.Refines.charge
    rw [BinaryFraction.queryOnlineRangeWithWork_value source target parent P exponent H hP tau child key R hR]
    exact hr key _
  · exact hn

end EditApproximation

end OAI
