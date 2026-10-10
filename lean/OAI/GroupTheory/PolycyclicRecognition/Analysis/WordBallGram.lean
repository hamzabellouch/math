import OAI.GroupTheory.PolycyclicRecognition.Analysis.PolynomialHarmonicFunctions
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.AbsoluteValue
import Mathlib.Algebra.Order.Star.Real

namespace OAI

/-! # Gram matrices of word-ball evaluations

The determinant is the volume quantity used in Kleiner's scale selection.
Its positivity comes from separation by a finite ball, and its polynomial
upper bound comes directly from polynomial growth of the functions.
-/
noncomputable section
namespace PolycyclicRecognition
open Finset Matrix
variable {G : Type*} [Group G] [DecidableEq G]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def wordBallEvaluationMatrix (S : Finset G) (R : ℕ) (F : ι → G → ℝ) :
    Matrix (wordBall S R) ι ℝ := fun x i => F i x.val

def wordBallGram (S : Finset G) (R : ℕ) (F : ι → G → ℝ) : Matrix ι ι ℝ :=
  (wordBallEvaluationMatrix S R F)ᵀ * wordBallEvaluationMatrix S R F

omit [Fintype ι] [DecidableEq ι] in
theorem wordBallGram_apply (S : Finset G) (R : ℕ) (F : ι → G → ℝ) (i j : ι) :
    wordBallGram S R F i j = ∑ x ∈ wordBall S R, F i x * F j x := by
  simp only [wordBallGram, Matrix.mul_apply, Matrix.transpose_apply, wordBallEvaluationMatrix]
  exact sum_coe_sort (wordBall S R) (fun x : G => F i x * F j x)

omit [DecidableEq ι] in
theorem wordBallGram_posDef_of_separates (S : Finset G) (R : ℕ) (F : ι → G → ℝ)
    (hsep : ∀ v : ι → ℝ, (∀ x ∈ wordBall S R, ∑ i, F i x * v i = 0) → v = 0) :
    (wordBallGram S R F).PosDef := by
  have hi : Function.Injective (wordBallEvaluationMatrix S R F).mulVec := by
    change Function.Injective (wordBallEvaluationMatrix S R F).mulVecLin
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro v hv
    apply hsep v
    intro x hx
    exact congr_fun hv ⟨x, hx⟩
  simpa only [wordBallGram, conjTranspose_eq_transpose_of_trivial] using
    Matrix.PosDef.conjTranspose_mul_self (wordBallEvaluationMatrix S R F) hi

omit [DecidableEq ι] in
theorem exists_wordBallGram_posDef (S : Finset G)
    (hS : ∀ s ∈ S, s⁻¹ ∈ S) (hgen : Subgroup.closure (S : Set G) = ⊤)
    (V : Submodule ℝ (G → ℝ)) (b : Module.Basis ι ℝ V) :
    ∃ R, (wordBallGram S R (fun i => (b i).val)).PosDef := by
  let : Module.Finite ℝ V := Module.Finite.of_basis b
  obtain ⟨R, hR⟩ := exists_wordBall_detects_finiteDimensional_functions S hS hgen V
  refine ⟨R, wordBallGram_posDef_of_separates S R _ (fun v hv => ?_)⟩
  have he : b.equivFun.symm v = 0 := by
    apply hR
    intro x hx
    have hs : (b.equivFun.symm v).val x = ∑ i, (b i).val x * v i := by
      rw [b.equivFun_symm_apply]
      simp [mul_comm]
    rw [hs]
    exact hv x hx
  exact b.equivFun.symm.injective (by simpa using he)

omit [DecidableEq ι] in
theorem finite_family_polynomial_word_bound (S : Finset G) (d : ℕ) (F : ι → G → ℝ)
    (hF : ∀ i, PolynomiallyBoundedOnWords S d (F i)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ i n x, x ∈ wordBall S n → |F i x| ≤ C * (1 + (n : ℝ)) ^ d := by
  choose c hc hbound using hF
  refine ⟨∑ i, c i, sum_nonneg (fun i _ => hc i), fun i n x hx => ?_⟩
  exact (hbound i n x hx).trans (mul_le_mul_of_nonneg_right
    (single_le_sum (fun j _ => hc j) (mem_univ i)) (by positivity))

omit [Fintype ι] [DecidableEq ι] in
theorem wordBallGram_entry_bound (S : Finset G) (R d : ℕ) (F : ι → G → ℝ)
    (C : ℝ) (hC : 0 ≤ C)
    (hF : ∀ i x, x ∈ wordBall S R → |F i x| ≤ C * (1 + (R : ℝ)) ^ d) (i j : ι) :
    |wordBallGram S R F i j| ≤
      (wordBall S R).card * (C ^ 2 * (1 + (R : ℝ)) ^ (2 * d)) := by
  rw [wordBallGram_apply]
  calc
    _ ≤ ∑ x ∈ wordBall S R, |F i x * F j x| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _x ∈ wordBall S R, C ^ 2 * (1 + (R : ℝ)) ^ (2 * d) := by
      apply sum_le_sum
      intro x hx
      rw [abs_mul]
      calc
        _ ≤ (C * (1 + (R : ℝ)) ^ d) * (C * (1 + (R : ℝ)) ^ d) :=
          mul_le_mul (hF i x hx) (hF j x hx) (abs_nonneg _) (by positivity)
        _ = _ := by rw [two_mul d, pow_add]; ring
    _ = _ := by simp

theorem wordBallGram_det_bound (S : Finset G) (R d b : ℕ) (F : ι → G → ℝ)
    (C D : ℝ) (hC : 0 ≤ C)
    (hF : ∀ i x, x ∈ wordBall S R → |F i x| ≤ C * (1 + (R : ℝ)) ^ d)
    (hvol : ((wordBall S R).card : ℝ) ≤ D * (1 + (R : ℝ)) ^ b) :
    |(wordBallGram S R F).det| ≤
      (Fintype.card ι).factorial * (D * C ^ 2) ^ Fintype.card ι *
        (1 + (R : ℝ)) ^ ((b + 2 * d) * Fintype.card ι) := by
  have he (i j : ι) : |wordBallGram S R F i j| ≤
      (D * C ^ 2) * (1 + (R : ℝ)) ^ (b + 2 * d) := by
    calc
      _ ≤ _ := wordBallGram_entry_bound S R d F C hC hF i j
      _ ≤ (D * (1 + (R : ℝ)) ^ b) * (C ^ 2 * (1 + (R : ℝ)) ^ (2 * d)) :=
        mul_le_mul_of_nonneg_right hvol (by positivity)
      _ = _ := by rw [pow_add]; ring
  have hd := Matrix.det_le (abv := AbsoluteValue.abs) he
  simpa only [AbsoluteValue.abs_apply, nsmul_eq_mul, mul_pow, ← pow_mul, mul_assoc] using hd

end PolycyclicRecognition

end

end OAI
