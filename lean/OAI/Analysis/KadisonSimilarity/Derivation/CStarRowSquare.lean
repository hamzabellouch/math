import OAI.Analysis.KadisonSimilarity.Derivation.DicksonAdjoint
import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap

namespace OAI

/-! The positive row square and its native C-star matrix norm. -/

noncomputable section
namespace KadisonSimilarity
open scoped CStarAlgebra ComplexOrder WithCStarModule
open CStarModule

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- The sum of `xx*` of a row has norm bounded by its matrix norm squared. -/
theorem norm_rowSquare_le {n : ℕ} (X : Matrix (Fin 1) (Fin n) A) :
    ‖∑ j : Fin n, X 0 j * star (X 0 j)‖ ≤ ‖CStarMatrix.ofMatrix X‖ ^ 2 := by
  let M := CStarMatrix.ofMatrix X
  let v : C⋆ᵐᵒᵈ(A, Fin 1 → A) := (WithCStarModule.equiv A _).symm (fun _ => 1)
  have hvinner : inner A v v = (1 : A) := by
    change (∑ i : Fin 1, (1 : A) * star 1) = 1
    simp
  have hv : ‖v‖ ≤ 1 := by
    have h : ‖v‖ ^ 2 = ‖inner A v v‖ := CStarModule.norm_sq_eq A
    rw [hvinner] at h
    have h1 := CStarRing.norm_star_mul_self (x := (1 : A))
    simp only [star_one, one_mul] at h1
    have hone : ‖(1 : A)‖ ≤ 1 := by
      by_cases hz : ‖(1 : A)‖ = 0
      · simp [hz]
      · have he : ‖(1 : A)‖ * 1 = ‖(1 : A)‖ * ‖(1 : A)‖ := by simpa using h1
        have heq := mul_left_cancel₀ hz he
        linarith
    nlinarith [norm_nonneg v]
  have hi : inner A (CStarMatrix.toCLM M v) (CStarMatrix.toCLM M v) =
      ∑ j : Fin n, X 0 j * star (X 0 j) := by
    rw [CStarMatrix.toCLM_apply_eq_sum]
    change (∑ j : Fin n, (∑ i : Fin 1, (1 : A) * X i j) *
      star (∑ i : Fin 1, (1 : A) * X i j)) = _
    simp
  have hn : ‖∑ j : Fin n, X 0 j * star (X 0 j)‖ = ‖CStarMatrix.toCLM M v‖ ^ 2 := by
    rw [← hi, CStarModule.norm_sq_eq A]
  rw [hn]
  apply pow_le_pow_left₀ (norm_nonneg _) _ 2
  exact ((CStarMatrix.toCLM M).le_opNorm v).trans
    ((mul_le_mul_of_nonneg_left hv (norm_nonneg _)).trans_eq (mul_one _))

/-- A positive functional of mass at most one is bounded on the row square. -/
theorem positiveFunctional_rowSquare_le (f : A →ₚ[ℂ] ℂ) (hf : (f 1).re ≤ 1)
    {n : ℕ} (X : Matrix (Fin 1) (Fin n) A) :
    ∑ j : Fin n, (f (X 0 j * star (X 0 j))).re ≤ ‖CStarMatrix.ofMatrix X‖ ^ 2 := by
  let S := ∑ j : Fin n, X 0 j * star (X 0 j)
  have hS : 0 ≤ S := Finset.sum_nonneg fun _ _ => mul_star_self_nonneg _
  have hfnorm : ‖f 1‖ = (f 1).re := by
    have h := f.map_nonneg (zero_le_one : (0 : A) ≤ 1)
    exact (Complex.re_eq_norm.mpr h).symm
  calc
    _ = (f S).re := by simp [S]
    _ ≤ ‖f S‖ := Complex.re_le_norm _
    _ ≤ ‖f 1‖ * ‖S‖ := f.norm_apply_le_of_nonneg S hS
    _ ≤ 1 * ‖S‖ := mul_le_mul_of_nonneg_right (by rwa [hfnorm]) (norm_nonneg _)
    _ = ‖S‖ := one_mul _
    _ ≤ ‖CStarMatrix.ofMatrix X‖ ^ 2 := norm_rowSquare_le X

end KadisonSimilarity

end

end OAI
