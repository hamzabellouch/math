import OAI.GroupTheory.PolycyclicRecognition.Algebra.UnipotentProducts
import Mathlib.LinearAlgebra.Matrix.Block

namespace OAI

/-!
# Polynomial products with bounded diagonal prefixes

For an upper triangular matrix path, remove the diagonal of each prefix.
The resulting increments are unipotent. If the original increments are bounded
and all diagonal prefixes and their inverses are bounded, the unipotent
increments are uniformly bounded. Their products therefore have polynomial
size. This is the coordinate estimate behind bounded-height path packing.
-/

namespace PolycyclicRecognition

section Gauge

variable {R : Type*} [Ring R]

/-- Change of diagonal frame at each successive prefix of a word. -/
def gaugedFactors (d : ℕ → Rˣ) : ℕ → List R → List R
  | _, [] => []
  | k, a :: l => ((d k : R) * a * (↑(d (k + 1))⁻¹ : R)) :: gaugedFactors d (k + 1) l

@[simp] theorem gaugedFactors_length (d : ℕ → Rˣ) (k : ℕ) (l : List R) :
    (gaugedFactors d k l).length = l.length := by
  induction l generalizing k with
  | nil => rfl
  | cons a l ih => simp [gaugedFactors, ih]

/-- All internal changes of frame cancel exactly. -/
theorem gaugedFactors_prod (d : ℕ → Rˣ) (k : ℕ) (l : List R) :
    (gaugedFactors d k l).prod = (d k : R) * l.prod * (↑(d (k + l.length))⁻¹ : R) := by
  induction l generalizing k with
  | nil => simp [gaugedFactors]
  | cons a l ih =>
    simp only [gaugedFactors, List.prod_cons, ih, List.length_cons]
    have hi : k + 1 + l.length = k + (l.length + 1) := by omega
    rw [hi]
    simp only [mul_assoc, Units.inv_mul_cancel_left]

end Gauge

section Norm

variable {R : Type*} [NormedRing R] [NormOneClass R]

omit [NormOneClass R] in
/-- A bounded frame and its inverse give uniformly bounded gauged increments. -/
theorem norm_gaugedFactors_le (d : ℕ → Rˣ) (k : ℕ) (l : List R)
    {B M : ℝ} (hB : 0 ≤ B) (hM : 0 ≤ M)
    (hd : ∀ i, ‖(d i : R)‖ ≤ B ∧ ‖(↑(d i)⁻¹ : R)‖ ≤ B)
    (hl : ∀ a ∈ l, ‖a‖ ≤ M) :
    ∀ a ∈ gaugedFactors d k l, ‖a‖ ≤ B * M * B := by
  induction l generalizing k with
  | nil => simp [gaugedFactors]
  | cons a l ih =>
    intro x hx
    rcases List.mem_cons.mp hx with hxa | hxl
    · subst x
      exact (norm_mul_le _ _).trans
        (mul_le_mul ((norm_mul_le _ _).trans
          (mul_le_mul (hd k).1 (hl a (by simp)) (norm_nonneg _) hB))
          (hd (k + 1)).2 (norm_nonneg _) (mul_nonneg hB hM))
    · exact ih (k + 1) (fun a ha => hl a (by simp [ha])) x hxl

end Norm

section Matrix

open scoped Matrix.Norms.Operator

variable {n : ℕ}

/-- A diagonal unit is represented by a genuine invertible diagonal matrix. -/
def diagonalUnit (d : Fin n → ℝˣ) : (Matrix (Fin n) (Fin n) ℝ)ˣ where
  val := Matrix.diagonal fun i => (d i : ℝ)
  inv := Matrix.diagonal fun i => (↑(d i)⁻¹ : ℝ)
  val_inv := by
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    simp [Matrix.diagonal, Matrix.one_apply]
  inv_val := by
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    simp [Matrix.diagonal, Matrix.one_apply]

/-- Matching successive prefix diagonals makes each gauged increment unipotent. -/
theorem strictUpper_diagonal_gauge (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.IsUpperTriangular) (d e : Fin n → ℝˣ)
    (hdiag : ∀ i, (d i : ℝ) * A i i = (e i : ℝ)) :
    StrictUpper ((diagonalUnit d : Matrix (Fin n) (Fin n) ℝ) * A *
      (↑(diagonalUnit e)⁻¹ : Matrix (Fin n) (Fin n) ℝ) - 1) := by
  intro i j hji
  change ((Matrix.diagonal (fun i => (d i : ℝ)) * A *
    Matrix.diagonal (fun i => (↑(e i)⁻¹ : ℝ))) - 1) i j = 0
  rw [Matrix.sub_apply, Matrix.mul_diagonal, Matrix.diagonal_mul]
  rcases hji.eq_or_lt with hij | hij
  · subst j
    rw [hdiag, Matrix.one_apply_eq]
    simp
  · rw [hA hij, mul_zero, zero_mul, Matrix.one_apply_ne (ne_of_gt hij), sub_self]

variable [NeZero n]

/-- Uniformly bounded upper triangular increments and bounded diagonal prefixes
have polynomially bounded product. The strict-upper condition is supplied by
`strictUpper_diagonal_gauge` for the actual prefix diagonals. -/
theorem norm_triangular_prod_le (d : ℕ → (Matrix (Fin n) (Fin n) ℝ)ˣ)
    (l : List (Matrix (Fin n) (Fin n) ℝ)) {B M : ℝ} (hB : 0 ≤ B) (hM : 0 ≤ M)
    (hd0 : d 0 = 1)
    (hd : ∀ i, ‖(d i : Matrix (Fin n) (Fin n) ℝ)‖ ≤ B ∧
      ‖(↑(d i)⁻¹ : Matrix (Fin n) (Fin n) ℝ)‖ ≤ B)
    (hl : ∀ a ∈ l, ‖a‖ ≤ M)
    (hstrict : ∀ a ∈ gaugedFactors d 0 l, StrictUpper (a - 1)) :
    ‖l.prod‖ ≤ ((n : ℝ) * (1 + (B * M * B + 1)) ^ n *
      (1 + (l.length : ℝ)) ^ n) * B := by
  let xs := (gaugedFactors d 0 l).map (fun a => a - 1)
  have hxs : ∀ a ∈ xs, StrictUpper a := by
    intro a ha
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
    exact hstrict b hb
  have hnorm : ∀ a ∈ xs, ‖a‖ ≤ B * M * B + 1 := by
    intro a ha
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
    exact (norm_sub_le _ _).trans (by
      simpa only [norm_one] using add_le_add
        (norm_gaugedFactors_le d 0 l hB hM hd hl b hb) (le_refl ‖(1 : Matrix (Fin n) (Fin n) ℝ)‖))
  have hp := norm_unipotent_prod_le xs hxs (by positivity : 0 ≤ B * M * B + 1) hnorm
  have hcancel : (xs.map (fun a => 1 + a)).prod = (gaugedFactors d 0 l).prod := by
    simp [xs, List.map_map, Function.comp_def]
  rw [hcancel] at hp
  have hprod : l.prod = (gaugedFactors d 0 l).prod * (d l.length : Matrix (Fin n) (Fin n) ℝ) := by
    rw [gaugedFactors_prod, hd0]
    simp [mul_assoc]
  rw [hprod]
  apply (norm_mul_le _ _).trans
  apply mul_le_mul _ (hd l.length).1 (norm_nonneg _) _
  · simpa [xs] using hp
  · positivity

end Matrix
end PolycyclicRecognition

end OAI
