import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic

namespace OAI

/-!
# Finite smoothing channels

Nonnegative transition probabilities and a uniform output mass bound
imply the weighted square-norm estimate for finite smoothing channels.
-/

namespace JointDickman

open Finset

section Channel

variable {Ω A : Type*} [Fintype Ω] [Fintype A]

noncomputable def finiteChannel (w : Ω → ℝ) (μ : A → ℝ) (p : Ω → A → ℝ)
    (f : Ω → ℝ) (a : A) : ℝ := (∑ s, w s * p s a * f s) / μ a

noncomputable def finiteChannelAdjoint (p : Ω → A → ℝ) (g : A → ℝ) (s : Ω) : ℝ :=
  ∑ a, p s a * g a

/-- Exact weighted adjoint identity, before any norm estimate. -/
theorem finiteChannel_adjoint (w : Ω → ℝ) (μ : A → ℝ) (p : Ω → A → ℝ)
    (hμ : ∀ a, μ a ≠ 0) (f : Ω → ℝ) (g : A → ℝ) :
    (∑ a, μ a * finiteChannel w μ p f a * g a) =
      ∑ s, w s * f s * finiteChannelAdjoint p g s := by
  unfold finiteChannel finiteChannelAdjoint
  simp_rw [mul_div_cancel₀ _ (hμ _), sum_mul, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro s _
  apply sum_congr rfl
  intro a _
  ring

private theorem channel_cell_square (w : Ω → ℝ) (p : Ω → ℝ)
    (hw : ∀ s, 0 ≤ w s) (hp : ∀ s, 0 ≤ p s) (f : Ω → ℝ) :
    (∑ s, w s * p s * f s) ^ 2 ≤
      (∑ s, w s * p s) * ∑ s, w s * p s * f s ^ 2 := by
  apply sum_sq_le_sum_mul_sum_of_sq_le_mul
  · intro s _
    exact mul_nonneg (hw s) (hp s)
  · intro s _
    exact mul_nonneg (mul_nonneg (hw s) (hp s)) (sq_nonneg _)
  · intro s _
    ring_nf
    exact le_rfl

/-- The first channel bound follows just from its output marginal and
its subprobability row sums. This is a weighted finite Schur bound. -/
theorem finiteChannel_square_bound (w : Ω → ℝ) (μ : A → ℝ) (p : Ω → A → ℝ)
    (hw : ∀ s, 0 ≤ w s) (hμ : ∀ a, 0 < μ a) (hp : ∀ s a, 0 ≤ p s a)
    {C : ℝ} (hC : 0 ≤ C)
    (hmarginal : ∀ a, (∑ s, w s * p s a) ≤ C * μ a)
    (hrow : ∀ s, (∑ a, p s a) ≤ 1) (f : Ω → ℝ) :
    (∑ a, μ a * finiteChannel w μ p f a ^ 2) ≤ C * ∑ s, w s * f s ^ 2 := by
  have hcell (a : A) : μ a * finiteChannel w μ p f a ^ 2 ≤
      C * ∑ s, w s * p s a * f s ^ 2 := by
    have hsq := channel_cell_square w (fun s => p s a) hw (fun s => hp s a) f
    have hnonneg : 0 ≤ ∑ s, w s * p s a * f s ^ 2 :=
      sum_nonneg fun s _ => mul_nonneg (mul_nonneg (hw s) (hp s a)) (sq_nonneg _)
    have hbound := hsq.trans (mul_le_mul_of_nonneg_right (hmarginal a) hnonneg)
    unfold finiteChannel
    apply (mul_le_mul_iff_right₀ (hμ a)).mp
    convert hbound using 1 <;> field_simp [ne_of_gt (hμ a)]
  calc
    _ ≤ ∑ a, C * ∑ s, w s * p s a * f s ^ 2 := sum_le_sum fun a _ => hcell a
    _ = C * ∑ s, w s * f s ^ 2 * ∑ a, p s a := by
      rw [← mul_sum, sum_comm]
      congr 1
      apply sum_congr rfl
      intro s _
      rw [mul_sum]
      apply sum_congr rfl
      intro a _
      ring
    _ ≤ C * ∑ s, w s * f s ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ hC
      apply sum_le_sum
      intro s _
      exact (mul_le_mul_of_nonneg_left (hrow s)
        (mul_nonneg (hw s) (sq_nonneg _))).trans_eq (mul_one _)

/-- The two-split kernel, expressed without an assumed adjoint theorem. -/
noncomputable def finiteTwoSplitKernel (w : Ω → ℝ) (μ : A → ℝ)
    (p : Ω → A → ℝ) (a b : A) : ℝ :=
  (∑ s, w s * p s a * p s b) / (μ a * μ b)

omit [Fintype A] in
theorem finiteTwoSplitKernel_symm (w : Ω → ℝ) (μ : A → ℝ)
    (p : Ω → A → ℝ) (a b : A) :
    finiteTwoSplitKernel w μ p a b = finiteTwoSplitKernel w μ p b a := by
  unfold finiteTwoSplitKernel
  congr 1
  · apply sum_congr rfl
    intro s _
    ring
  · ring

/-- Integral action of a kernel on a finite space with atom masses `μ`. -/
noncomputable def finiteKernelAction (μ : A → ℝ) (K : A → A → ℝ)
    (g : A → ℝ) (a : A) : ℝ := ∑ b, μ b * K a b * g b

/-- The two-split kernel is exactly the channel followed by its adjoint. -/
theorem finiteTwoSplitKernel_action (w : Ω → ℝ) (μ : A → ℝ)
    (p : Ω → A → ℝ) (hμ : ∀ a, μ a ≠ 0) (g : A → ℝ) (a : A) :
    finiteKernelAction μ (finiteTwoSplitKernel w μ p) g a =
      finiteChannel w μ p (finiteChannelAdjoint p g) a := by
  unfold finiteKernelAction finiteTwoSplitKernel finiteChannel finiteChannelAdjoint
  simp only [sum_div, sum_mul, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro s _
  apply sum_congr rfl
  intro b _
  field_simp [hμ a, hμ b]

omit [Fintype Ω] in
/-- Two weighted absolute row/column estimates give a finite Schur bound.
This form also applies to signed differences of probability kernels. -/
theorem finiteKernelAction_square_bound (μ : A → ℝ) (K : A → A → ℝ)
    (hμ : ∀ a, 0 ≤ μ a) {C : ℝ} (hC : 0 ≤ C)
    (hrow : ∀ a, (∑ b, μ b * |K a b|) ≤ C)
    (hcol : ∀ b, (∑ a, μ a * |K a b|) ≤ C) (g : A → ℝ) :
    (∑ a, μ a * finiteKernelAction μ K g a ^ 2) ≤
      C ^ 2 * ∑ a, μ a * g a ^ 2 := by
  have hcell (a : A) : finiteKernelAction μ K g a ^ 2 ≤
      C * ∑ b, μ b * |K a b| * g b ^ 2 := by
    have habs : |finiteKernelAction μ K g a| ≤ ∑ b, μ b * |K a b| * |g b| := by
      unfold finiteKernelAction
      calc
        _ ≤ ∑ b, |μ b * K a b * g b| := abs_sum_le_sum_abs _ _
        _ = _ := by simp_rw [abs_mul, abs_of_nonneg (hμ _)]
    have hsum : 0 ≤ ∑ b, μ b * |K a b| * |g b| :=
      sum_nonneg fun b _ => mul_nonneg (mul_nonneg (hμ b) (abs_nonneg _)) (abs_nonneg _)
    have hsq := (sq_le_sq₀ (abs_nonneg _) hsum).2 habs
    rw [sq_abs] at hsq
    have hcs := channel_cell_square μ (fun b => |K a b|) hμ
      (fun b => abs_nonneg _) (fun b => |g b|)
    simp_rw [sq_abs] at hcs
    exact hsq.trans (hcs.trans (mul_le_mul_of_nonneg_right (hrow a)
      (sum_nonneg fun b _ => mul_nonneg (mul_nonneg (hμ b) (abs_nonneg _)) (sq_nonneg _))))
  calc
    _ ≤ ∑ a, μ a * (C * ∑ b, μ b * |K a b| * g b ^ 2) :=
      sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (hcell a) (hμ a)
    _ = C * ∑ b, μ b * g b ^ 2 * ∑ a, μ a * |K a b| := by
      simp_rw [mul_sum]
      rw [sum_comm]
      apply sum_congr rfl
      intro b _
      apply sum_congr rfl
      intro a _
      ring
    _ ≤ C * ∑ b, μ b * g b ^ 2 * C := by
      apply mul_le_mul_of_nonneg_left _ hC
      exact sum_le_sum fun b _ => mul_le_mul_of_nonneg_left (hcol b)
        (mul_nonneg (hμ b) (sq_nonneg _))
    _ = _ := by rw [← sum_mul]; ring

end Channel


end JointDickman

end OAI
