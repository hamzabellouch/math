import OAI.NumberTheory.TwoPoint.Bounds.PrimeSlotCode
import OAI.NumberTheory.TwoPoint.Walks.WordResampling
import OAI.NumberTheory.TwoPoint.Bounds.IndependentSampling

namespace OAI

/-! Tuple classes can be resampled while all padding classes remain fixed. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

namespace CrudeWordCode

variable {R N : ℕ}

def recordedSlots (c : CrudeWordCode R N R) (i : Fin R) (b : Bool) : Finset (Fin N) :=
  univ.filter (fun j => c.2.2.1 j = i ∧ c.2.2.2 j = b)

def KindConsistent (c : CrudeWordCode R N R) : Prop :=
  ∀ j, c.2.2.2 (c.2.1 j) = c.2.2.2 j

def RowInjective (c : CrudeWordCode R N R) : Prop :=
  ∀ i b, Set.InjOn c.2.1 (c.recordedSlots i b)

def tupleClasses (c : CrudeWordCode R N R) : Finset c.usedClasses :=
  univ.filter (fun z => c.2.2.2 z.val = false)

def tupleLabels (c : CrudeWordCode R N R) (i : Fin R) : Finset c.tupleClasses :=
  ((c.recordedSlots i false).image c.classAt).subtype (fun z => z ∈ c.tupleClasses)

lemma classAt_mem_tupleClasses (c : CrudeWordCode R N R) (hc : c.KindConsistent)
    (j : Fin N) (hj : c.2.2.2 j = false) : c.classAt j ∈ c.tupleClasses := by
  simp only [tupleClasses, mem_filter, mem_univ, true_and, classAt]
  exact (hc j).trans hj

lemma classAt_notMem_tupleClasses (c : CrudeWordCode R N R) (hc : c.KindConsistent)
    (j : Fin N) (hj : c.2.2.2 j = true) : c.classAt j ∉ c.tupleClasses := by
  simp only [tupleClasses, mem_filter, mem_univ, true_and, classAt]
  rw [hc j, hj]
  decide

/-- Rowwise squarefreeness makes the tuple product a product over its classes. -/
lemma tuple_product (c : CrudeWordCode R N R) (hc : c.KindConsistent)
    (hi : c.RowInjective) (i : Fin R) (a : c.tupleClasses → ℕ)
    (b : {z : c.usedClasses // z ∉ c.tupleClasses} → ℕ) :
    (∏ j ∈ c.recordedSlots i false,
      joinCoordinates c.tupleClasses a b (c.classAt j)) =
        ∏ z ∈ c.tupleLabels i, a z := by
  let f (j : Fin N) (hj : j ∈ c.recordedSlots i false) : c.tupleClasses :=
    ⟨c.classAt j, c.classAt_mem_tupleClasses hc j (mem_filter.mp hj).2.2⟩
  apply prod_bij f
  · intro j hj
    exact mem_subtype.mpr (mem_image.mpr ⟨j, hj, rfl⟩)
  · intro j hj k hk he
    exact hi i false hj hk (congrArg (fun z : c.tupleClasses => z.val.val) he)
  · intro z hz
    obtain ⟨j, hj, he⟩ := mem_image.mp (mem_subtype.mp hz)
    exact ⟨j, hj, Subtype.ext he⟩
  · intro j hj
    exact joinCoordinates_mem c.tupleClasses a b (f j hj)

lemma padding_product (c : CrudeWordCode R N R) (hc : c.KindConsistent)
    (i : Fin R) (a a' : c.tupleClasses → ℕ)
    (b : {z : c.usedClasses // z ∉ c.tupleClasses} → ℕ) :
    (∏ j ∈ c.recordedSlots i true, joinCoordinates c.tupleClasses a b (c.classAt j)) =
      ∏ j ∈ c.recordedSlots i true, joinCoordinates c.tupleClasses a' b (c.classAt j) := by
  apply prod_congr rfl
  intro j hj
  have hn := c.classAt_notMem_tupleClasses hc j (mem_filter.mp hj).2.2
  simp only [joinCoordinates, hn, dite_false]

/-- A fixed padding assignment and a tuple-class support define the symbolic word. -/
def labeledWord (c : CrudeWordCode R N R)
    (b : {z : c.usedClasses // z ∉ c.tupleClasses} → ℕ) : LabeledPrimeWord c.tupleClasses where
  word := c.numericalWord (joinCoordinates c.tupleClasses (fun _ => 1) b)
  labels i := c.tupleLabels ⟨i.val, by
    exact lt_of_lt_of_eq i.isLt (numericalWord_length c _)⟩

lemma labeledWord_length (c : CrudeWordCode R N R)
    (b : {z : c.usedClasses // z ∉ c.tupleClasses} → ℕ) :
    (c.labeledWord b).word.length = R := c.numericalWord_length _

/-- Resampling changes exactly the tuple primes, with no additional padding choices. -/
theorem labeledWord_resample (c : CrudeWordCode R N R) (hc : c.KindConsistent)
    (hi : c.RowInjective) (a : c.tupleClasses → ℕ)
    (b : {z : c.usedClasses // z ∉ c.tupleClasses} → ℕ) :
    ((c.labeledWord b).resample a).word =
      c.numericalWord (joinCoordinates c.tupleClasses a b) := by
  apply List.ext_getElem
  · rw [LabeledPrimeWord.resample_length, labeledWord_length, numericalWord_length]
  · intro i hi₁ hi₂
    have hiR : i < R := by simpa only [numericalWord_length] using hi₂
    let j : Fin R := ⟨i, hiR⟩
    have hp := c.padding_product hc j (fun _ => 1) a b
    have ht := c.tuple_product hc hi j a b
    have hf := c.numericalWord_get (joinCoordinates c.tupleClasses (fun _ => 1) b) j
    simp only [LabeledPrimeWord.resample, List.getElem_ofFn, labeledWord]
    rw [c.numericalWord_get _ j]
    congr 1
    · exact congrArg SignedStep.forward hf
    · exact ht.symm
    · exact (congrArg SignedStep.padding hf).trans hp

end CrudeWordCode

end TwoPointCorrelations

end OAI
