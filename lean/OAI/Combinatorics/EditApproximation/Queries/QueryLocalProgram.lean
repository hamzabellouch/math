import OAI.Combinatorics.EditApproximation.Queries.QueryLocalBand

namespace OAI

/-! The concrete adaptive local program, beginning with the parent query.
Every intermediate buffer is constructed after the answers determining
its support, and every scalar source range is computed before its read. -/

namespace EditApproximation

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

def queryLocalProgram : BitQuery ι BinaryFraction :=
  queryInitialGather N P F exponent hP a q readParent fun keys words =>
    queryLocalBand source target parent N P F exponent H Q eM eF hP hM hF
      tau a eta kappa delta t (BinaryFraction.queryParentReadWithWork keys words)
      readMass readInitial readGroup readInteger q readEarlier readCurrent

theorem queryLocalProgram_refines
    (expectedParent : TargetInterval target.length → FiniteQuery ι)
    (expectedMass expectedInitial : (Fin M × TargetInterval target.length) → FiniteQuery ι)
    (expectedGroup : GroupScalarKey M F Q → FiniteQuery ι)
    (expectedInteger : (ℕ × TargetInterval target.length) → ℕ → FiniteQuery ι)
    (expectedEarlier : (Fin M × ℕ × TargetInterval target.length) → FiniteQuery ι)
    (expectedCurrent : (Fin M × TargetInterval target.length) → FiniteQuery ι)
    (hp : ∀ key, BitQuery.Refines (fun word value => word.value = value)
      (readParent key) (expectedParent key))
    (hm : ∀ key, BitQuery.Refines (fun word value => word.value = value)
      (readMass key) (expectedMass key))
    (hi : ∀ key, BitQuery.Refines (fun word value => word.value = value)
      (readInitial key) (expectedInitial key))
    (hg : ∀ key, BitQuery.Refines (fun word value => word.value = value)
      (readGroup key) (expectedGroup key))
    (hz : ∀ key range, BitQuery.Refines (fun word value => word.value = value)
      (readInteger key range) (expectedInteger key range))
    (he : ∀ key, BitQuery.Refines (fun word value => word.value = value)
      (readEarlier key) (expectedEarlier key))
    (hr : ∀ key, BitQuery.Refines (fun word value => word.value = value)
      (readCurrent key) (expectedCurrent key)) :
    BitQuery.Refines (fun word value => word.value = value)
      (queryLocalProgram source target parent N P F exponent H Q eM eF hP hM hF
        tau a eta kappa delta t readParent readMass readInitial readGroup readInteger
        q readEarlier readCurrent)
      (localRandomDataQuery source target parent N P F exponent H Q
        tau.value a.value eta.value kappa.value delta.value t
        expectedParent expectedMass expectedInitial expectedGroup expectedInteger
        q expectedEarlier expectedCurrent) := by
  unfold queryLocalProgram localRandomDataQuery
  apply queryInitialGather_refines N P F exponent hP a q readParent expectedParent
    (expectedNext := fun keys words =>
      localRandomBandDataQuery source target parent N P F exponent H Q
        tau.value a.value eta.value kappa.value delta.value t
        (finiteAnswerTable keys words) expectedMass expectedInitial expectedGroup expectedInteger
        q expectedEarlier expectedCurrent) (hr := hp)
  intro value words
  let keys := refinementInitialSupport N P F exponent a.value value.value q
  have h := queryLocalBand_refines source target parent N P F exponent H Q eM eF hP hM hF
    tau a eta kappa delta t (BinaryFraction.queryParentReadWithWork keys words)
    readMass readInitial readGroup readInteger q readEarlier readCurrent
    expectedMass expectedInitial expectedGroup expectedInteger expectedEarlier expectedCurrent
    hm hi hg hz he hr
  simpa only [BinaryFraction.queryParentReadWithWork_value] using h

end Program
end EditApproximation

end OAI
