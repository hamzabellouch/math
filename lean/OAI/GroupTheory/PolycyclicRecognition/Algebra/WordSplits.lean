import OAI.GroupTheory.PolycyclicRecognition.Algebra.RationalWordEvaluation
import Mathlib.Data.List.TakeDrop

namespace OAI

/-! # The finite prefix/suffix convolution for word coefficients -/

noncomputable section
namespace PolycyclicRecognition

open scoped BigOperators

variable {n : ℕ}

def wordSplit (w : FreeMonoid (Fin n)) (i : Fin (w.length + 1)) :
    FreeMonoid (Fin n) × FreeMonoid (Fin n) :=
  (FreeMonoid.ofList (w.toList.take i.val), FreeMonoid.ofList (w.toList.drop i.val))

theorem wordSplit_mul (w : FreeMonoid (Fin n)) (i : Fin (w.length + 1)) :
    (wordSplit w i).1 * (wordSplit w i).2 = w := by
  apply FreeMonoid.toList.injective
  simp [wordSplit]

theorem wordSplit_left_length (w : FreeMonoid (Fin n)) (i : Fin (w.length + 1)) :
    (wordSplit w i).1.length = i.val := by
  have hi : i.val ≤ w.toList.length := Nat.le_of_lt_succ i.isLt
  simp [wordSplit, FreeMonoid.length, Nat.min_eq_left hi]

theorem wordSplit_injective (w : FreeMonoid (Fin n)) : Function.Injective (wordSplit w) := by
  intro i j h
  apply Fin.ext
  simpa only [wordSplit_left_length] using congrArg (fun p => p.1.length) h

theorem exists_wordSplit (w u v : FreeMonoid (Fin n)) (h : u * v = w) :
    ∃ i : Fin (w.length + 1), wordSplit w i = (u, v) := by
  subst w
  have hu : u.length < (u * v).length + 1 := by rw [FreeMonoid.length_mul]; omega
  refine ⟨⟨u.length, hu⟩, ?_⟩
  apply Prod.ext <;> apply FreeMonoid.toList.injective
  · simp [wordSplit, FreeMonoid.length]
  · simp [wordSplit, FreeMonoid.length]

theorem word_coeff_mul (p q : RationalWords n) (w : FreeMonoid (Fin n)) :
    (p * q).coeff w = ∑ i : Fin (w.length + 1),
      p.coeff (wordSplit w i).1 * q.coeff (wordSplit w i).2 := by
  classical
  let s := Finset.univ.image (wordSplit w)
  have hs {z : FreeMonoid (Fin n) × FreeMonoid (Fin n)} : z ∈ s ↔ z.1 * z.2 = w := by
    constructor
    · intro hz
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hz
      exact wordSplit_mul w i
    · intro hz
      obtain ⟨i, hi⟩ := exists_wordSplit w z.1 z.2 hz
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hi⟩
  rw [MonoidAlgebra.coeff_mul_antidiag p q w s (fun {_} => hs)]
  exact Finset.sum_image (fun _ _ _ _ h => wordSplit_injective w h)

end PolycyclicRecognition

end

end OAI
