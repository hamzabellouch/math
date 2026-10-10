import OAI.Combinatorics.EditApproximation.Queries.QueryLocalRefinement
import OAI.Combinatorics.EditApproximation.Queries.QueryGroupSources
import OAI.Combinatorics.EditApproximation.Queries.QueryOnlineSources
import OAI.Combinatorics.EditApproximation.Geometry.LocalRandomSourceQuery

namespace OAI

/-! Random words are gathered before the adaptive local selectors run.
The online sampling range is computed from the gathered mass words. -/

namespace EditApproximation

section Sources
variable {ι α : Type*} (source target : List α) {M : ℕ} [NeZero M]
  (parent : TargetInterval source.length) (N P F exponent H Q eM eF : ℕ)
  (hP : 0 < P) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF)
  (tau a eta kappa delta : BinaryFraction) (t : ℕ)
  (parentInitial : TargetInterval target.length → BinaryFraction × ℕ)
  (child initial : Fin M → TargetInterval target.length → BinaryFraction × ℕ)
  (R : ℕ) (hc : ∀ i r, (child i r).2 ≤ R) (hi : ∀ i r, (initial i r).2 ≤ R)
  (q : TargetInterval target.length)
  (readGroup : GroupScalarKey M F Q → BitQuery ι BinaryFraction)
  (readInteger : (ℕ × TargetInterval target.length) → ℕ → BitQuery ι BinaryFraction)
  (readEarlier : (Fin M × ℕ × TargetInterval target.length) → BitQuery ι BinaryFraction)
  (readCurrent : (Fin M × TargetInterval target.length) → BitQuery ι BinaryFraction)

def queryLocalRandomSources : BitQuery ι BinaryFraction :=
  queryGroupSourceGather M N F Q exponent eM eF hM hF a parentInitial q readGroup
    fun groupKeys groupWords =>
      queryOnlineSourceGather parent N P F exponent H hP tau a parentInitial child q readInteger
        fun onlineKeys onlineWords =>
          queryLocalRefinement source target parent N P F exponent H Q eM eF hP hM hF
            tau a eta kappa delta t parentInitial child initial R hc hi
            (BinaryFraction.queryGroupDrawReadWithWork groupKeys groupWords)
            (BinaryFraction.queryOnlineIntegerReadWithWork onlineKeys onlineWords)
            q readEarlier readCurrent

theorem queryLocalRandomSources_refines
    (expectedGroup : GroupScalarKey M F Q → FiniteQuery ι)
    (expectedInteger : (ℕ × TargetInterval target.length) → ℕ → FiniteQuery ι)
    (expectedEarlier : (Fin M × ℕ × TargetInterval target.length) → FiniteQuery ι)
    (expectedCurrent : (Fin M × TargetInterval target.length) → FiniteQuery ι)
    (hg : ∀ key, BitQuery.Refines (fun word value => word.value = value)
      (readGroup key) (expectedGroup key))
    (hz : ∀ key range, BitQuery.Refines (fun word value => word.value = value)
      (readInteger key range) (expectedInteger key range))
    (he : ∀ key, BitQuery.Refines (fun word value => word.value = value)
      (readEarlier key) (expectedEarlier key))
    (hr : ∀ key, BitQuery.Refines (fun word value => word.value = value)
      (readCurrent key) (expectedCurrent key)) :
    BitQuery.Refines (fun word value => word.value = value)
      (queryLocalRandomSources source target parent N P F exponent H Q eM eF hP hM hF
        tau a eta kappa delta t parentInitial child initial R hc hi q
        readGroup readInteger readEarlier readCurrent)
      (localRandomSourceStepQuery source target parent N P F exponent H Q
        tau.value a.value eta.value kappa.value delta.value t
        (fun r => (parentInitial r).1.value) (fun i r => (child i r).1.value)
        (fun i r => (initial i r).1.value) q
        expectedGroup expectedInteger expectedEarlier expectedCurrent) := by
  unfold queryLocalRandomSources localRandomSourceStepQuery
  apply queryGroupSourceGather_refines M N F Q exponent eM eF hM hF a parentInitial q readGroup
    expectedGroup (expectedNext := fun keys values =>
      localOnlineSourceStepQuery source target parent N P F exponent H Q
        tau.value a.value eta.value kappa.value delta.value t
        (fun r => (parentInitial r).1.value) (fun i r => (child i r).1.value)
        (fun i r => (initial i r).1.value) (groupDrawFromValues keys values)
        q expectedInteger expectedEarlier expectedCurrent) (hr := hg)
  intro groupWords
  let groupKeys := groupScalarKeys M F Q
    (localGroupQueryKeys N F exponent a.value (fun r => (parentInitial r).1.value) q)
  unfold localOnlineSourceStepQuery
  apply queryOnlineSourceGather_refines source target parent N P F exponent H hP tau a
    parentInitial child q R hc readInteger expectedInteger
    (expectedNext := fun keys values =>
      localRefinementStepQuery source target parent N P F exponent H Q
        tau.value a.value eta.value kappa.value delta.value t
        (fun r => (parentInitial r).1.value) (fun i r => (child i r).1.value)
        (fun i r => (initial i r).1.value)
        (groupDrawFromValues groupKeys (groupWords.map BinaryFraction.value))
        (fun b r => ⌊finiteAnswerTable keys values (b, r)⌋₊) q expectedEarlier expectedCurrent)
    (hr := hz)
  intro onlineWords
  let onlineKeys := localOnlineSourceKeys N P F a.value (fun r => (parentInitial r).1.value) q
  have h := queryLocalRefinement_refines source target parent N P F exponent H Q eM eF hP hM hF
    tau a eta kappa delta t parentInitial child initial R hc hi
    (BinaryFraction.queryGroupDrawReadWithWork groupKeys groupWords)
    (BinaryFraction.queryOnlineIntegerReadWithWork onlineKeys onlineWords)
    q readEarlier readCurrent expectedEarlier expectedCurrent he hr
  simpa only [BinaryFraction.queryGroupDrawReadWithWork_value,
    BinaryFraction.queryOnlineIntegerReadWithWork_value] using h

end Sources
end EditApproximation

end OAI
