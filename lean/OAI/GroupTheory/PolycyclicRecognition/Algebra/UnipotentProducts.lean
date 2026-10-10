import OAI.GroupTheory.PolycyclicRecognition.Algebra.NilpotentProducts
import Mathlib.Analysis.Matrix.Normed

namespace OAI

/-!
# Concrete polynomial bounds for unipotent matrix products

Products of `n` strictly upper triangular `n × n` matrices vanish, even when
the factors are different. Consequently the preceding fixed-degree estimate
applies to arbitrarily long products of unipotent increments.
-/

namespace PolycyclicRecognition

variable {n : ℕ} {R : Type*} [Ring R]

/-- Strict upper triangularity, with diagonal vanishing included. -/
def StrictUpper (A : Matrix (Fin n) (Fin n) R) : Prop :=
  ∀ i j, j ≤ i → A i j = 0

/-- Every strictly upper triangular factor advances the row-to-column index
by at least one. This is valid for ordered products of distinct matrices. -/
theorem strictUpper_prod_entry_zero (l : List (Matrix (Fin n) (Fin n) R))
    (hl : ∀ A ∈ l, StrictUpper A) (i j : Fin n)
    (hij : (j : ℕ) < (i : ℕ) + l.length) : l.prod i j = 0 := by
  induction l generalizing i j with
  | nil =>
    have hne : i ≠ j := by intro h; subst j; simp at hij
    simp [hne]
  | cons A l ih =>
    rw [List.prod_cons, Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro k _
    by_cases hk : k ≤ i
    · rw [hl A (by simp) i k hk, zero_mul]
    · have htail : ∀ B ∈ l, StrictUpper B := fun B hB => hl B (by simp [hB])
      have hkj : (j : ℕ) < (k : ℕ) + l.length := by
        have hik : (i : ℕ) < k := Fin.lt_def.mp (lt_of_not_ge hk)
        simp only [List.length_cons] at hij
        omega
      rw [ih htail k j hkj, mul_zero]

/-- The nilpotence bound is the matrix dimension and is independent of all
coefficients and of the choice of factors. -/
theorem strictUpper_prod_zero (l : List (Matrix (Fin n) (Fin n) R))
    (hl : ∀ A ∈ l, StrictUpper A) (hn : n ≤ l.length) : l.prod = 0 := by
  ext i j
  apply strictUpper_prod_entry_zero l hl i j
  have hj := j.isLt
  omega

/-- A strictly upper triangular matrix has nilpotence degree at most its size. -/
theorem StrictUpper.pow_eq_zero {A : Matrix (Fin n) (Fin n) R} (hA : StrictUpper A) :
    A ^ n = 0 := by
  have h := strictUpper_prod_zero (List.replicate n A)
    (fun B hB => by
      have heq : B = A := (List.mem_replicate.mp hB).2
      simpa only [heq] using hA)
    (by simp)
  simpa only [List.prod_replicate] using h

section Real

open scoped Matrix.Norms.Operator

variable [NeZero n]

/-- A fully concrete polynomial bound: uniformly bounded upper unipotent
increments have product norm bounded by a degree-`n` polynomial in their number. -/
theorem norm_unipotent_prod_le (l : List (Matrix (Fin n) (Fin n) ℝ))
    (hl : ∀ A ∈ l, StrictUpper A) {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ A ∈ l, ‖A‖ ≤ M) :
    ‖(l.map (fun A => 1 + A)).prod‖ ≤
      (n : ℝ) * (1 + M) ^ n * (1 + (l.length : ℝ)) ^ n := by
  let S : Set (Matrix (Fin n) (Fin n) ℝ) := {A | StrictUpper A ∧ ‖A‖ ≤ M}
  apply norm_prod_one_add_le_polynomial S n
    (fun xs hxs hlen => strictUpper_prod_zero xs (fun A hA => (hxs A hA).1) hlen) hM
    (fun A hA => hA.2) l
  exact fun A hA => ⟨hl A hA, hbound A hA⟩

end Real
end PolycyclicRecognition

end OAI
