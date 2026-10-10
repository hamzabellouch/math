import OAI.Combinatorics.EditApproximation.Queries.QueryRefinementSpace
import OAI.Combinatorics.EditApproximation.Queries.QueryLocalProgram

namespace OAI

namespace EditApproximation
open BitQuery

section Sources
variable {ι α : Type*} (source target : List α) {M : ℕ} [NeZero M]
  (parent : TargetInterval source.length) (N P F exponent H Q eM eF : ℕ)
  (hP : 0 < P) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF)
  (tau a eta kappa delta : BinaryFraction) (t : ℕ)
  (parentInitial : TargetInterval target.length → BinaryFraction × ℕ)
  (child initial : Fin M → TargetInterval target.length → BinaryFraction × ℕ)
  (R : ℕ) (hc : ∀ i r, (child i r).2 ≤ R) (hi : ∀ i r, (initial i r).2 ≤ R)
  (parentAllocation : TargetInterval target.length → ℕ)
  (childAllocation initialAllocation : Fin M → TargetInterval target.length → ℕ)
  (hp : ∀ r, parentAllocation r ≤ (parentInitial r).2)
  (hca : ∀ i r, childAllocation i r ≤ (child i r).2)
  (hia : ∀ i r, initialAllocation i r ≤ (initial i r).2)
  (q : TargetInterval target.length)
  (readGroup : GroupScalarKey M F Q → BitQuery ι BinaryFraction)
  (readInteger : (ℕ × TargetInterval target.length) → ℕ → BitQuery ι BinaryFraction)
  (readEarlier : (Fin M × ℕ × TargetInterval target.length) → BitQuery ι BinaryFraction)
  (readCurrent : (Fin M × TargetInterval target.length) → BitQuery ι BinaryFraction)
  (hg : ∀ key, Heap (readGroup key)) (hz : ∀ key range, Heap (readInteger key range))
  (he : ∀ key, Heap (readEarlier key)) (hr : ∀ key, Heap (readCurrent key))

open BinaryFraction in
def queryLocalRandomSourcesHeap : Heap (queryLocalRandomSources source target parent N P F exponent H Q eM eF
    hP hM hF tau a eta kappa delta t parentInitial child initial R hc hi q
    readGroup readInteger readEarlier readCurrent) :=
  queryGroupSourceGatherHeap M N F Q exponent eM eF hM hF a parentInitial parentAllocation hp q
    readGroup hg _ fun groupKeys groupWords =>
      queryOnlineSourceGatherHeap parent N P F exponent H hP tau a parentInitial parentAllocation
        child childAllocation hp hca q readInteger hz _ fun onlineKeys onlineWords =>
          queryLocalRefinementHeap source target parent N P F exponent H Q eM eF hP hM hF
            tau a eta kappa delta t parentInitial child initial R hc hi
            (queryGroupDrawReadWithWork groupKeys groupWords)
            (queryOnlineIntegerReadWithWork onlineKeys onlineWords)
            parentAllocation childAllocation initialAllocation
            (queryGroupDrawReadAllocation groupKeys groupWords)
            (queryOnlineIntegerReadAllocation onlineKeys onlineWords)
            hp hca hia (queryGroupDrawReadAllocation_le_work groupKeys groupWords)
            (queryOnlineIntegerReadAllocation_le_work onlineKeys onlineWords) q readEarlier readCurrent he hr

end Sources

section Band
variable {ι α : Type*} (source target : List α) {M : ℕ} [NeZero M]
  (parent : TargetInterval source.length) (N P F exponent H Q eM eF : ℕ)
  (hP : 0 < P) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF)
  (tau a eta kappa delta : BinaryFraction) (t : ℕ)
  (parentInitial : TargetInterval target.length → BinaryFraction × ℕ)
  (parentAllocation : TargetInterval target.length → ℕ)
  (hp : ∀ r, parentAllocation r ≤ (parentInitial r).2)
  (readMass readInitial : (Fin M × TargetInterval target.length) → BitQuery ι BinaryFraction)
  (readGroup : GroupScalarKey M F Q → BitQuery ι BinaryFraction)
  (readInteger : (ℕ × TargetInterval target.length) → ℕ → BitQuery ι BinaryFraction)
  (q : TargetInterval target.length)
  (readEarlier : (Fin M × ℕ × TargetInterval target.length) → BitQuery ι BinaryFraction)
  (readCurrent : (Fin M × TargetInterval target.length) → BitQuery ι BinaryFraction)
  (hm : ∀ key, Heap (readMass key)) (hi : ∀ key, Heap (readInitial key))
  (hg : ∀ key, Heap (readGroup key)) (hz : ∀ key range, Heap (readInteger key range))
  (he : ∀ key, Heap (readEarlier key)) (hr : ∀ key, Heap (readCurrent key))

open BinaryFraction in
def queryLocalBandHeap : Heap (queryLocalBand source target parent N P F exponent H Q eM eF hP hM hF
    tau a eta kappa delta t parentInitial readMass readInitial readGroup readInteger q readEarlier readCurrent) :=
  queryBandGatherHeap M parent N P F exponent hP a parentInitial parentAllocation hp q readMass readInitial hm hi _
    fun keys massWords initialWords =>
      queryLocalRandomSourcesHeap source target parent N P F exponent H Q eM eF hP hM hF
        tau a eta kappa delta t parentInitial
        (queryChildReadWithWork keys massWords) (queryChildReadWithWork keys initialWords)
        (queryDataReadBudget M target.length keys)
        (queryChildReadWithWork_budget keys massWords) (queryChildReadWithWork_budget keys initialWords)
        parentAllocation (queryChildReadAllocation keys massWords) (queryChildReadAllocation keys initialWords)
        hp (queryChildReadAllocation_le_work keys massWords) (queryChildReadAllocation_le_work keys initialWords)
        q readGroup readInteger readEarlier readCurrent hg hz he hr

end Band

section Program
variable {ι α : Type*} (source target : List α) {M : ℕ} [NeZero M]
  (parent : TargetInterval source.length) (N P F exponent H Q eM eF : ℕ)
  (hP : 0 < P) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF)
  (tau a eta kappa delta : BinaryFraction) (t : ℕ)
  (readParent : TargetInterval target.length → BitQuery ι BinaryFraction)
  (readMass readInitial : (Fin M × TargetInterval target.length) → BitQuery ι BinaryFraction)
  (readGroup : GroupScalarKey M F Q → BitQuery ι BinaryFraction)
  (readInteger : (ℕ × TargetInterval target.length) → ℕ → BitQuery ι BinaryFraction)
  (q : TargetInterval target.length)
  (readEarlier : (Fin M × ℕ × TargetInterval target.length) → BitQuery ι BinaryFraction)
  (readCurrent : (Fin M × TargetInterval target.length) → BitQuery ι BinaryFraction)
  (hp : ∀ key, Heap (readParent key))
  (hm : ∀ key, Heap (readMass key)) (hi : ∀ key, Heap (readInitial key))
  (hg : ∀ key, Heap (readGroup key)) (hz : ∀ key range, Heap (readInteger key range))
  (he : ∀ key, Heap (readEarlier key)) (hr : ∀ key, Heap (readCurrent key))

open BinaryFraction in
def queryLocalProgramHeap : Heap (queryLocalProgram source target parent N P F exponent H Q eM eF hP hM hF
    tau a eta kappa delta t readParent readMass readInitial readGroup readInteger q readEarlier readCurrent) :=
  queryInitialGatherHeap N P F exponent hP a q readParent hp _ fun keys words =>
    queryLocalBandHeap source target parent N P F exponent H Q eM eF hP hM hF tau a eta kappa delta t
      (queryParentReadWithWork keys words) (queryParentReadAllocation keys words) (queryParentReadAllocation_le_work keys words)
      readMass readInitial readGroup readInteger q readEarlier readCurrent hm hi hg hz he hr

end Program
end EditApproximation

end OAI
