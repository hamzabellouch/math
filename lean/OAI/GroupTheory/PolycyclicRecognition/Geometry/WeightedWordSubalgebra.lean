import OAI.GroupTheory.PolycyclicRecognition.Algebra.TruncatedPrimitiveCoefficients
import Mathlib.Algebra.Algebra.Subalgebra.Basic

namespace OAI

/-! # Word length equals scalar degree in the universal construction -/

noncomputable section
namespace PolycyclicRecognition

variable (c n : ℕ)

def weightedWord (w : FreeMonoid (Fin n)) : TruncatedWords c n :=
  MonoidAlgebra.single w (truncatedScalarParameter c ^ w.length)

@[simp] theorem weightedWord_one : weightedWord c n 1 = 1 := by
  simp [weightedWord, FreeMonoid.length, MonoidAlgebra.one_def]

theorem weightedWord_mul (u v : FreeMonoid (Fin n)) :
    weightedWord c n (u * v) = weightedWord c n u * weightedWord c n v := by
  simp [weightedWord, FreeMonoid.length, pow_add]

def weightedWordSpan : Submodule ℚ (TruncatedWords c n) :=
  Submodule.span ℚ (Set.range (weightedWord c n))

theorem weightedWordSpan_mul {p q : TruncatedWords c n}
    (hp : p ∈ weightedWordSpan c n) (hq : q ∈ weightedWordSpan c n) :
    p * q ∈ weightedWordSpan c n := by
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨u, rfl⟩ := hp
    induction hq using Submodule.span_induction with
    | mem q hq =>
      obtain ⟨v, rfl⟩ := hq
      rw [← weightedWord_mul]
      exact Submodule.subset_span ⟨u * v, rfl⟩
    | zero => rw [mul_zero]; exact (weightedWordSpan c n).zero_mem
    | add q r _ _ hq hr =>
      rw [mul_add]
      exact (weightedWordSpan c n).add_mem hq hr
    | smul a q _ hq =>
      rw [Algebra.mul_smul_comm]
      exact (weightedWordSpan c n).smul_mem a hq
  | zero => rw [zero_mul]; exact (weightedWordSpan c n).zero_mem
  | add p r _ _ hp hr =>
    rw [add_mul]
    exact (weightedWordSpan c n).add_mem hp hr
  | smul a p _ hp =>
    rw [smul_mul_assoc]
    exact (weightedWordSpan c n).smul_mem a hp

def weightedWordSubalgebra : Subalgebra ℚ (TruncatedWords c n) where
  carrier := weightedWordSpan c n
  add_mem' := (weightedWordSpan c n).add_mem
  mul_mem' := weightedWordSpan_mul c n
  algebraMap_mem' q := by
    rw [Algebra.algebraMap_eq_smul_one]
    apply (weightedWordSpan c n).smul_mem
    rw [← weightedWord_one c n]
    exact Submodule.subset_span ⟨1, rfl⟩

theorem weightedWordSubalgebra_parameter_letter (i : Fin n) :
    truncatedScalarParameter c • truncatedWordLetter c n i ∈ weightedWordSubalgebra c n := by
  change _ ∈ weightedWordSpan c n
  have h : truncatedScalarParameter c • truncatedWordLetter c n i =
      weightedWord c n (FreeMonoid.of i) := by
    simp [truncatedWordLetter, weightedWord, FreeMonoid.length]
  rw [h]
  exact Submodule.subset_span ⟨_, rfl⟩

end PolycyclicRecognition

end

end OAI
