import OAI.Analysis.LipschitzHilbert.Trees.UnaryTelescope
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Module

namespace OAI

/-!
# Exact propagation along unary segments

Finite iteration of §10 `res:unary-decomposition`. The residual coefficient
is the actual product of preceding path coefficients. Discarded-top
errors are summed against mass drops rather than the number of tops or
levels, as required in `res:segment-perturbation`.
-/

noncomputable section

open scoped BigOperators

namespace LipschitzHilbert

def unaryPropagator (coeff : ℕ → ℂ) (start finish : ℕ) : ℂ :=
  ∏ j ∈ Finset.Ico start finish, coeff j

@[simp] theorem unaryPropagator_self (coeff : ℕ → ℂ) (start : ℕ) :
    unaryPropagator coeff start start = 1 := by simp [unaryPropagator]

theorem unaryPropagator_succ_right (coeff : ℕ → ℂ) {start finish : ℕ}
    (h : start ≤ finish) :
    unaryPropagator coeff start (finish + 1) = unaryPropagator coeff start finish * coeff finish :=
  Finset.prod_Ico_succ_top h coeff

theorem unaryPropagator_succ_left (coeff : ℕ → ℂ) {start finish : ℕ}
    (h : start < finish) :
    unaryPropagator coeff start finish = coeff start * unaryPropagator coeff (start + 1) finish :=
  Finset.prod_eq_prod_Ico_succ_bot h coeff

theorem unaryPropagator_norm_le_one (coeff : ℕ → ℂ) (start finish : ℕ)
    (hcoeff : ∀ j ∈ Finset.Ico start finish, ‖coeff j‖ ≤ 1) :
    ‖unaryPropagator coeff start finish‖ ≤ 1 := by
  rw [unaryPropagator, norm_prod]
  exact Finset.prod_le_one₀ (fun j _ => norm_nonneg _) hcoeff

section Vector

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

omit [NormedSpace ℂ E] in
private theorem sum_Ico_forward_difference (f : ℕ → E) {start finish : ℕ}
    (h : start ≤ finish) :
    (∑ i ∈ Finset.Ico start finish, (f i - f (i + 1))) = f start - f finish := by
  induction finish, h using Nat.le_induction with
  | base => simp
  | succ finish h ih =>
    rw [Finset.sum_Ico_succ_top h, ih]
    abel

/-- Iteration retains the exact common product on every residual term. -/
theorem unary_iteration (coeff : ℕ → ℂ) (A U W : ℕ → E) {start finish : ℕ}
    (h : start ≤ finish)
    (hstep : ∀ i ∈ Finset.Ico start finish, A i = coeff i • A (i + 1) + U i + W i) :
    A start - unaryPropagator coeff start finish • A finish =
      (∑ i ∈ Finset.Ico start finish, unaryPropagator coeff start i • U i) +
      ∑ i ∈ Finset.Ico start finish, unaryPropagator coeff start i • W i := by
  have hterm (i : ℕ) (hi : i ∈ Finset.Ico start finish) :
      unaryPropagator coeff start i • U i + unaryPropagator coeff start i • W i =
        unaryPropagator coeff start i • A i -
          unaryPropagator coeff start (i + 1) • A (i + 1) := by
    rw [unaryPropagator_succ_right coeff (Finset.mem_Ico.mp hi).1,
      mul_smul, hstep i hi, smul_add, smul_add]
    abel
  rw [← Finset.sum_add_distrib]
  rw [Finset.sum_congr rfl hterm]
  rw [sum_Ico_forward_difference (fun i => unaryPropagator coeff start i • A i) h]
  simp

theorem propagated_endpoint_contraction (coeff : ℕ → ℂ) (A : E) {i finish : ℕ}
    (hi : i < finish) (hcoeff : ‖coeff i‖ ≤ 1) :
    ‖unaryPropagator coeff i finish • A‖ ≤
      ‖unaryPropagator coeff (i + 1) finish • A‖ := by
  rw [unaryPropagator_succ_left coeff hi, mul_smul, norm_smul]
  exact mul_le_of_le_one_left (norm_nonneg _) hcoeff

/-- Whole discarded-top errors cost only the total mass drop. -/
theorem discarded_unary_error_sum (coeff : ℕ → ℂ) (W : ℕ → E) (n : ℕ → ℝ)
    {start finish : ℕ} {ε : ℝ} (h : start ≤ finish)
    (hcoeff : ∀ j ∈ Finset.Ico start finish, ‖coeff j‖ ≤ 1)
    (hW : ∀ j ∈ Finset.Ico start finish, ‖W j‖ ≤ ε * (n j - n (j + 1))) :
    ‖∑ i ∈ Finset.Ico start finish, unaryPropagator coeff start i • W i‖ ≤
      ε * (n start - n finish) := by
  calc
    _ ≤ ∑ i ∈ Finset.Ico start finish, ‖unaryPropagator coeff start i • W i‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.Ico start finish, ε * (n i - n (i + 1)) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [norm_smul]
      have hp := unaryPropagator_norm_le_one coeff start i (by
        intro j hj
        apply hcoeff j
        exact Finset.mem_Ico.mpr ⟨(Finset.mem_Ico.mp hj).1,
          (Finset.mem_Ico.mp hj).2.trans (Finset.mem_Ico.mp hi).2⟩)
      exact (mul_le_of_le_one_left (norm_nonneg _) hp).trans (hW i hi)
    _ = ε * (n start - n finish) := by
      rw [← Finset.mul_sum, sum_Ico_forward_difference n h]

/-- The propagated main residual sum and discarded-top error give the
amplitude perturbation used by the unary energy telescope. -/
theorem unary_perturbation_bound (coeff : ℕ → ℂ) (A U W : ℕ → E) (n : ℕ → ℝ)
    {start finish : ℕ} {ε D : ℝ} (h : start ≤ finish)
    (hcoeff : ∀ j ∈ Finset.Ico start finish, ‖coeff j‖ ≤ 1)
    (hstep : ∀ i ∈ Finset.Ico start finish, A i = coeff i • A (i + 1) + U i + W i)
    (hU : ‖∑ i ∈ Finset.Ico start finish, unaryPropagator coeff start i • U i‖ ≤ D)
    (hW : ∀ j ∈ Finset.Ico start finish, ‖W j‖ ≤ ε * (n j - n (j + 1))) :
    ‖A start - unaryPropagator coeff start finish • A finish‖ ≤
      D + ε * (n start - n finish) := by
  rw [unary_iteration coeff A U W h hstep]
  exact (norm_add_le _ _).trans (add_le_add hU
    (discarded_unary_error_sum coeff W n h hcoeff hW))

end Vector

end LipschitzHilbert

end

end OAI
