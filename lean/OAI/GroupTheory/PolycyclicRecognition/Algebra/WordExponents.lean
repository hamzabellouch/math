import OAI.GroupTheory.PolycyclicRecognition.Algebra.BracketWords

namespace OAI

/-! # Additive exponents of bracket words

Letter amplitudes add through every bracket. The sum in a word basis is the
letter-count expression used by the support datum.
-/

namespace PolycyclicRecognition

open scoped BigOperators

variable {I J : Type*} [Fintype I] [DecidableEq I]

def bracketWordExponent (s : I → ℝ) (w : FreeMagma I) : ℝ :=
  ∑ i, (bracketWordCount w i : ℝ) * s i

@[simp] theorem bracketWordExponent_of (s : I → ℝ) (i : I) :
    bracketWordExponent s (.of i) = s i := by
  simp [bracketWordExponent, bracketWordCount]

@[simp] theorem bracketWordExponent_mul (s : I → ℝ) (u v : FreeMagma I) :
    bracketWordExponent s (u * v) = bracketWordExponent s u + bracketWordExponent s v := by
  simp [bracketWordExponent, bracketWordCount, add_mul, Finset.sum_add_distrib]

theorem sum_bracketWordExponent [Fintype J] (s : I → ℝ) (words : J → FreeMagma I) :
    ∑ j, bracketWordExponent s (words j) =
      ∑ i, ((∑ j, bracketWordCount (words j) i : ℕ) : ℝ) * s i := by
  simp only [bracketWordExponent, Nat.cast_sum, Finset.sum_mul]
  exact Finset.sum_comm

@[simp] theorem bracketWordExponent_add (s t : I → ℝ) (w : FreeMagma I) :
    bracketWordExponent (s + t) w = bracketWordExponent s w + bracketWordExponent t w := by
  simp [bracketWordExponent, mul_add, Finset.sum_add_distrib]

/-- Multiplying all letter costs multiplies every bracket-word cost. -/
@[simp] theorem bracketWordExponent_const_mul (a : ℝ) (s : I → ℝ) (w : FreeMagma I) :
    bracketWordExponent (fun i => a * s i) w = a * bracketWordExponent s w := by
  simp only [bracketWordExponent, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

end PolycyclicRecognition

end OAI
