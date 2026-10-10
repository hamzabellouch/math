import OAI.Analysis.KadisonKastler.HilbertRows

namespace OAI

/-! # Annihilation columns and their products -/

namespace KadisonKastler

open Finset

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {I J : Type*} [Fintype I] [Fintype J]

local instance hilbertColumnOrder : PartialOrder (H →L[ℂ] H) := CStarAlgebra.spectralOrder _
local instance hilbertColumnStarOrder : StarOrderedRing (H →L[ℂ] H) :=
  CStarAlgebra.spectralOrderedRing _

def operatorColumn (C : I → H →L[ℂ] H) : CStarMatrix I Unit (H →L[ℂ] H) :=
  CStarMatrix.ofMatrix (fun i _ => C i)

omit [CompleteSpace H] [Fintype I] in
@[simp]
theorem operatorColumn_apply (C : I → H →L[ℂ] H) (i : I) (u : Unit) :
    operatorColumn C i u = C i := rfl

theorem norm_operatorColumn_eq_row_star (C : I → H →L[ℂ] H) :
    ‖operatorColumn C‖ = ‖operatorRow (fun i => star (C i))‖ := by
  have he : operatorColumn C = (operatorRow (fun i => star (C i))).conjTranspose := by
    apply CStarMatrix.ext
    intro i u
    simp only [CStarMatrix.conjTranspose_apply, operatorRow_apply, operatorColumn_apply, star_star]
  rw [he, norm_rectangular_star]

theorem norm_operatorColumn_reindex (C : I → H →L[ℂ] H) (e : J ≃ I) :
    ‖operatorColumn (C ∘ e)‖ = ‖operatorColumn C‖ := by
  rw [norm_operatorColumn_eq_row_star, norm_operatorColumn_eq_row_star]
  exact norm_operatorRow_reindex (fun i => star (C i)) e

theorem norm_operatorColumn_comp_le (C : I → H →L[ℂ] H) (f : J → I)
    (hf : Function.Injective f) : ‖operatorColumn (C ∘ f)‖ ≤ ‖operatorColumn C‖ := by
  rw [norm_operatorColumn_eq_row_star, norm_operatorColumn_eq_row_star]
  exact norm_operatorRow_comp_le (fun i => star (C i)) f hf

theorem norm_operatorColumn_apply_le (C : I → H →L[ℂ] H) (z : H) :
    ‖WithLp.toLp 2 (fun i => C i z)‖ ≤ ‖operatorColumn C‖ * ‖z‖ := by
  have h := (rectangularHilbertMatrix (operatorColumn C)).le_opNorm
    (WithLp.toLp 2 (fun _ : Unit => z))
  rw [norm_rectangularHilbertMatrix] at h
  simpa only [PiLp.norm_eq_of_L2, rectangularHilbertMatrix_apply,
    Fintype.sum_unique, operatorColumn_apply, Real.sqrt_sq (norm_nonneg _)] using h

theorem norm_operatorColumn_le (C : I → H →L[ℂ] H) {c : ℝ} (hc : 0 ≤ c)
    (hC : ∀ z : H, ‖WithLp.toLp 2 (fun i => C i z)‖ ≤ c * ‖z‖) :
    ‖operatorColumn C‖ ≤ c := by
  rw [← norm_rectangularHilbertMatrix]
  apply ContinuousLinearMap.opNorm_le_bound _ hc
  intro x
  simpa only [PiLp.norm_eq_of_L2, rectangularHilbertMatrix_apply,
    Fintype.sum_unique, operatorColumn_apply, Real.sqrt_sq (norm_nonneg _)] using hC (x ())

theorem norm_operatorColumn_products_le (C : I → H →L[ℂ] H) (D : J → H →L[ℂ] H) :
    ‖operatorColumn (fun ij : I × J => C ij.1 * D ij.2)‖ ≤
      ‖operatorColumn C‖ * ‖operatorColumn D‖ := by
  apply norm_operatorColumn_le _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  intro z
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  have hD := pow_le_pow_left₀ (norm_nonneg _) (norm_operatorColumn_apply_le D z) 2
  rw [PiLp.norm_sq_eq_of_L2, mul_pow] at hD
  rw [PiLp.norm_sq_eq_of_L2, Fintype.sum_prod_type, sum_comm]
  calc
    _ ≤ ∑ j, (‖operatorColumn C‖ * ‖D j z‖) ^ 2 := by
      apply sum_le_sum
      intro j _
      have h := pow_le_pow_left₀ (norm_nonneg _) (norm_operatorColumn_apply_le C (D j z)) 2
      simpa only [PiLp.norm_sq_eq_of_L2, mul_apply_eq_comp] using h
    _ = ‖operatorColumn C‖ ^ 2 * ∑ j, ‖D j z‖ ^ 2 := by simp_rw [mul_pow]; rw [mul_sum]
    _ ≤ ‖operatorColumn C‖ ^ 2 * (‖operatorColumn D‖ ^ 2 * ‖z‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hD (sq_nonneg _)
    _ = _ := by ring

theorem norm_tupleOperatorColumn_le {α : Type*} [Fintype α] (n : ℕ)
    (C : Fin n → α → H →L[ℂ] H) {c : ℝ} (hc : 0 ≤ c)
    (hC : ∀ i, ‖operatorColumn (C i)‖ ≤ c) :
    ‖operatorColumn (tupleOperatorProduct C)‖ ≤ c ^ n := by
  classical
  induction n with
  | zero =>
    apply norm_operatorColumn_le _ (by simp)
    intro x
    simp [tupleOperatorProduct, PiLp.norm_eq_of_L2]
  | succ n ih =>
    let e : α × (Fin n → α) ≃ (Fin (n + 1) → α) := Fin.consEquiv (fun _ => α)
    have he : (tupleOperatorProduct C) ∘ e =
        fun a : α × (Fin n → α) => C 0 a.1 * tupleOperatorProduct (fun i => C i.succ) a.2 := by
      funext a
      simp [tupleOperatorProduct, e, Fin.consEquiv, List.ofFn_succ]
    rw [← norm_operatorColumn_reindex _ e, he]
    calc
      _ ≤ ‖operatorColumn (C 0)‖ * ‖operatorColumn (tupleOperatorProduct (fun i => C i.succ))‖ :=
        norm_operatorColumn_products_le _ _
      _ ≤ c * c ^ n := mul_le_mul (hC 0) (ih _ (fun i => hC i.succ)) (norm_nonneg _) hc
      _ = _ := (pow_succ' c n).symm

end

end KadisonKastler

end OAI
