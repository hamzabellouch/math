import OAI.Analysis.KadisonKastler.TupleMatrices
import Mathlib.Data.List.OfFn

namespace OAI

/-! # Products of operator rows on finite Hilbert sums -/

namespace KadisonKastler

open Finset

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {I J : Type*} [Fintype I] [Fintype J]

local instance hilbertRowOrder : PartialOrder (H →L[ℂ] H) := CStarAlgebra.spectralOrder _
local instance hilbertRowStarOrder : StarOrderedRing (H →L[ℂ] H) :=
  CStarAlgebra.spectralOrderedRing _

def operatorRow (C : I → H →L[ℂ] H) : CStarMatrix Unit I (H →L[ℂ] H) :=
  CStarMatrix.ofMatrix (fun _ i => C i)

omit [CompleteSpace H] [Fintype I] in
@[simp]
theorem operatorRow_apply (C : I → H →L[ℂ] H) (u : Unit) (i : I) :
    operatorRow C u i = C i := rfl

theorem norm_operatorRow_apply (C : I → H →L[ℂ] H) (x : Generator.FiniteHilbert I H) :
    ‖∑ i, C i (x i)‖ ≤ ‖operatorRow C‖ * ‖x‖ := by
  have h := (rectangularHilbertMatrix (operatorRow C)).le_opNorm x
  rw [norm_rectangularHilbertMatrix] at h
  simpa only [PiLp.norm_eq_of_L2, Fintype.sum_unique, rectangularHilbertMatrix_apply,
    operatorRow_apply, Real.sqrt_sq (norm_nonneg _)] using h

theorem norm_operatorRow_le (C : I → H →L[ℂ] H) {c : ℝ} (hc : 0 ≤ c)
    (hC : ∀ x : Generator.FiniteHilbert I H, ‖∑ i, C i (x i)‖ ≤ c * ‖x‖) :
    ‖operatorRow C‖ ≤ c := by
  rw [← norm_rectangularHilbertMatrix]
  apply ContinuousLinearMap.opNorm_le_bound _ hc
  intro x
  simpa only [PiLp.norm_eq_of_L2, Fintype.sum_unique, rectangularHilbertMatrix_apply,
    operatorRow_apply, Real.sqrt_sq (norm_nonneg _)] using hC x

/-- Repeating an operator row on each fibre does not enlarge its norm. -/
theorem norm_fibreRow_apply (D : J → H →L[ℂ] H)
    (x : Generator.FiniteHilbert (I × J) H) :
    ‖WithLp.toLp 2 (fun i => ∑ j, D j (x (i, j)))‖ ≤ ‖operatorRow D‖ * ‖x‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp
  rw [PiLp.norm_sq_eq_of_L2, mul_pow, PiLp.norm_sq_eq_of_L2, Fintype.sum_prod_type]
  rw [mul_sum]
  apply sum_le_sum
  intro i _
  have h := norm_operatorRow_apply D (WithLp.toLp 2 (fun j => x (i, j)))
  have hsq := pow_le_pow_left₀ (norm_nonneg _) h 2
  simpa only [mul_pow, PiLp.norm_sq_eq_of_L2] using hsq

/-- Creating another letter multiplies the row bound, even when the
letters act on the same Hilbert space and do not commute. -/
theorem norm_operatorRow_products_le (C : I → H →L[ℂ] H) (D : J → H →L[ℂ] H) :
    ‖operatorRow (fun ij : I × J => C ij.1 * D ij.2)‖ ≤
      ‖operatorRow C‖ * ‖operatorRow D‖ := by
  apply norm_operatorRow_le _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  intro x
  have he : (∑ ij : I × J, (C ij.1 * D ij.2) (x ij)) =
      ∑ i, C i (∑ j, D j (x (i, j))) := by
    simp only [Fintype.sum_prod_type, mul_apply_eq_comp, map_sum]
  rw [he]
  calc
    _ ≤ ‖operatorRow C‖ * ‖WithLp.toLp 2 (fun i => ∑ j, D j (x (i, j)))‖ :=
      norm_operatorRow_apply C _
    _ ≤ ‖operatorRow C‖ * (‖operatorRow D‖ * ‖x‖) :=
      mul_le_mul_of_nonneg_left (norm_fibreRow_apply D x) (norm_nonneg _)
    _ = _ := by ring

/-- Restricting a row to an injective selection of labels is contractive. -/
theorem norm_operatorRow_comp_le (C : I → H →L[ℂ] H) (f : J → I)
    (hf : Function.Injective f) : ‖operatorRow (C ∘ f)‖ ≤ ‖operatorRow C‖ := by
  classical
  have hn : ‖fiberReplication (H := H) f‖ ≤ 1 := by
    have h := norm_fiberReplication_le (H := H) f 1 (fun i => by
      apply card_le_one.mpr
      intro a ha b hb
      apply hf
      simp only [mem_filter, mem_univ, true_and] at ha hb
      exact ha.trans hb.symm)
    simpa only [Nat.cast_one, Real.sqrt_one] using h
  have he : operatorRow (C ∘ f) = operatorRow C * (fiberReplication (H := H) f).conjTranspose := by
    apply CStarMatrix.ext
    intro i j
    rw [mul_fiberReplication_star]
    rfl
  rw [he]
  refine (rectangularOperator_norm_mul_le _ _).trans ?_
  rw [norm_rectangular_star]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hn (norm_nonneg (operatorRow C))

theorem norm_operatorRow_reindex (C : I → H →L[ℂ] H) (e : J ≃ I) :
    ‖operatorRow (C ∘ e)‖ = ‖operatorRow C‖ := by
  apply le_antisymm (norm_operatorRow_comp_le C e e.injective)
  have h := norm_operatorRow_comp_le (C ∘ e) e.symm e.symm.injective
  simpa only [Function.comp_def, Equiv.apply_symm_apply] using h

def tupleOperatorProduct {α : Type*} {n : ℕ}
    (C : Fin n → α → H →L[ℂ] H) (a : Fin n → α) : H →L[ℂ] H :=
  (List.ofFn (fun i => C i (a i))).prod

/-- Iterated creation rows have the product of the one-letter row bounds. -/
theorem norm_tupleOperatorRow_le {α : Type*} [Fintype α] (n : ℕ)
    (C : Fin n → α → H →L[ℂ] H) {c : ℝ} (hc : 0 ≤ c)
    (hC : ∀ i, ‖operatorRow (C i)‖ ≤ c) :
    ‖operatorRow (tupleOperatorProduct C)‖ ≤ c ^ n := by
  classical
  induction n with
  | zero =>
    apply norm_operatorRow_le _ (by simp)
    intro x
    simp [tupleOperatorProduct, PiLp.norm_eq_of_L2]
  | succ n ih =>
    let e : α × (Fin n → α) ≃ (Fin (n + 1) → α) := Fin.consEquiv (fun _ => α)
    have he : (tupleOperatorProduct C) ∘ e =
        fun a : α × (Fin n → α) => C 0 a.1 * tupleOperatorProduct (fun i => C i.succ) a.2 := by
      funext a
      simp [tupleOperatorProduct, e, Fin.consEquiv, List.ofFn_succ]
    rw [← norm_operatorRow_reindex _ e, he]
    calc
      _ ≤ ‖operatorRow (C 0)‖ * ‖operatorRow (tupleOperatorProduct (fun i => C i.succ))‖ :=
        norm_operatorRow_products_le _ _
      _ ≤ c * c ^ n := mul_le_mul (hC 0) (ih _ (fun i => hC i.succ)) (norm_nonneg _) hc
      _ = _ := (pow_succ' c n).symm

end

end KadisonKastler

end OAI
