import OAI.Combinatorics.EditApproximation.Queries.QueryLocalSources
import OAI.Combinatorics.EditApproximation.Queries.QueryLocalBuffers
import OAI.Combinatorics.EditApproximation.Queries.QueryBandGather
import OAI.Combinatorics.EditApproximation.Geometry.LocalRandomDataQuery

namespace OAI

/-! Mass and initial words are read into counted finite buffers before
any random source range or local action is constructed. -/

namespace EditApproximation

section Band
variable {ι α : Type*} (source target : List α) {M : ℕ} [NeZero M]
  (parent : TargetInterval source.length) (N P F exponent H Q eM eF : ℕ)
  (hP : 0 < P) (hM : M = 2 ^ eM) (hF : F = 2 ^ eF)
  (tau a eta kappa delta : BinaryFraction) (t : ℕ)
  (parentInitial : TargetInterval target.length → BinaryFraction × ℕ)
  (readMass readInitial : (Fin M × TargetInterval target.length) → BitQuery ι BinaryFraction)
  (readGroup : GroupScalarKey M F Q → BitQuery ι BinaryFraction)
  (readInteger : (ℕ × TargetInterval target.length) → ℕ → BitQuery ι BinaryFraction)
  (q : TargetInterval target.length)
  (readEarlier : (Fin M × ℕ × TargetInterval target.length) → BitQuery ι BinaryFraction)
  (readCurrent : (Fin M × TargetInterval target.length) → BitQuery ι BinaryFraction)

def queryLocalBand : BitQuery ι BinaryFraction :=
  queryBandGather M parent N P F exponent hP a parentInitial q readMass readInitial
    fun keys massWords initialWords =>
      queryLocalRandomSources source target parent N P F exponent H Q eM eF hP hM hF
        tau a eta kappa delta t parentInitial
        (BinaryFraction.queryChildReadWithWork keys massWords)
        (BinaryFraction.queryChildReadWithWork keys initialWords)
        (BinaryFraction.queryDataReadBudget M target.length keys)
        (BinaryFraction.queryChildReadWithWork_budget keys massWords)
        (BinaryFraction.queryChildReadWithWork_budget keys initialWords)
        q readGroup readInteger readEarlier readCurrent

theorem queryLocalBand_refines
    (expectedMass expectedInitial : (Fin M × TargetInterval target.length) → FiniteQuery ι)
    (expectedGroup : GroupScalarKey M F Q → FiniteQuery ι)
    (expectedInteger : (ℕ × TargetInterval target.length) → ℕ → FiniteQuery ι)
    (expectedEarlier : (Fin M × ℕ × TargetInterval target.length) → FiniteQuery ι)
    (expectedCurrent : (Fin M × TargetInterval target.length) → FiniteQuery ι)
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
      (queryLocalBand source target parent N P F exponent H Q eM eF hP hM hF
        tau a eta kappa delta t parentInitial readMass readInitial readGroup readInteger
        q readEarlier readCurrent)
      (localRandomBandDataQuery source target parent N P F exponent H Q
        tau.value a.value eta.value kappa.value delta.value t
        (fun r => (parentInitial r).1.value) expectedMass expectedInitial expectedGroup expectedInteger
        q expectedEarlier expectedCurrent) := by
  classical
  let Rp := ∑ r, (parentInitial r).2
  have hp : ∀ r, (parentInitial r).2 ≤ Rp := fun r =>
    Finset.single_le_sum (f := fun r => (parentInitial r).2) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ r)
  unfold queryLocalBand localRandomBandDataQuery
  apply queryBandGather_refines M parent N P F exponent hP a parentInitial q Rp hp
    readMass readInitial expectedMass expectedInitial
    (expectedNext := fun keys massWords initialWords =>
      localRandomSourceStepQuery source target parent N P F exponent H Q
        tau.value a.value eta.value kappa.value delta.value t
        (fun r => (parentInitial r).1.value)
        (fun i r => finiteAnswerTable keys massWords (i, r))
        (fun i r => finiteAnswerTable keys initialWords (i, r)) q
        expectedGroup expectedInteger expectedEarlier expectedCurrent)
    (hm := hm) (hi := hi)
  intro massWords initialWords
  let keys := refinementBandInputList (M := M) parent N P F exponent a.value
    (fun r => (parentInitial r).1.value) q
  have h := queryLocalRandomSources_refines source target parent N P F exponent H Q eM eF hP hM hF
    tau a eta kappa delta t parentInitial
    (BinaryFraction.queryChildReadWithWork keys massWords)
    (BinaryFraction.queryChildReadWithWork keys initialWords)
    (BinaryFraction.queryDataReadBudget M target.length keys)
    (BinaryFraction.queryChildReadWithWork_budget keys massWords)
    (BinaryFraction.queryChildReadWithWork_budget keys initialWords)
    q readGroup readInteger readEarlier readCurrent expectedGroup expectedInteger expectedEarlier
    expectedCurrent hg hz he hr
  simpa only [BinaryFraction.queryChildReadWithWork_value] using h

end Band
end EditApproximation

end OAI
