import OAI.NumberTheory.TwoPoint.Bounds.ExistentialWitnesses
import OAI.NumberTheory.TwoPoint.Bounds.LabeledWordSegments
import OAI.NumberTheory.TwoPoint.Bounds.PrimeSlotClasses

namespace OAI

/-! A numerical formulation of the witness event and its exact coded segments. -/

namespace TwoPointCorrelations

/-- All conditions involve the original numerical main and witness words. -/
def NumericalWitnessEvent {n : ℕ} {ι : Type*}
    (main : List SignedStep) (word : Fin n → List SignedStep) (value : ι → ℕ)
    (h s J : ℕ) (supply : ℕ → ℕ → Prop) : Prop :=
  ∃ (mark : Fin n → ι) (attachment position : Fin n → ℕ),
    Monotone attachment ∧ (∀ i, attachment i ≤ main.length) ∧
    Function.Injective value ∧ (∀ j, (value j).Prime) ∧
    (∀ i, MinimalWord (ForwardProhibited h s supply) (word i)) ∧
    (∀ i t, t ∈ word i → Squarefree t.tuple) ∧
    (∀ i t, t ∈ word i → t.tuple.primeFactors.card = J) ∧
    (∀ i p j, TuplePrimeAt (word i) p j → ¬p ∣ h ∧ ∀ t ∈ word i, ¬p ∣ t.padding) ∧
    (∀ i, value (mark i) ∈ wordPrimeSupport (word i)) ∧
    (∀ i j, j ≠ i → value (mark i) ∉ wordPrimeSupport (word j)) ∧
    (∀ i v, TuplePrimeAt main (value (mark i)) v → v = position i) ∧
    ∃ x : ℤ, ∀ i, PositiveWord h
      (x + wordDisplacement h (main.take (attachment i))) (word i)

lemma has_resampled_witnesses_iff {n : ℕ} {ι : Type*} [DecidableEq ι]
    (main : LabeledPrimeWord ι) (word : Fin n → LabeledPrimeWord ι)
    (h s J : ℕ) (supply : ℕ → ℕ → Prop) (value : ι → ℕ) :
    HasResampledWitnesses main word h s J supply value ↔
      NumericalWitnessEvent (main.resample value).word
        (fun i => ((word i).resample value).word) value h s J supply := by
  simp only [HasResampledWitnesses, NumericalWitnessEvent, ResampledWitnessEvent,
    LabeledPrimeWord.resample_length]

lemma CrudeWordCode.segment_resample_word {R N : ℕ} (c : CrudeWordCode R N R)
    (hc : c.KindConsistent) (hi : c.RowInjective)
    (a : c.tupleClasses → ℕ) (b : {z : c.usedClasses // z ∉ c.tupleClasses} → ℕ)
    (start len : ℕ) :
    (((c.labeledWord b).segment start len).resample a).word =
      ((c.numericalWord (joinCoordinates c.tupleClasses a b)).drop start).take len := by
  rw [LabeledPrimeWord.segment_resample_word, c.labeledWord_resample hc hi]

end TwoPointCorrelations

end OAI
