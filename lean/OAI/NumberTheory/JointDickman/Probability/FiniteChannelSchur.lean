import OAI.NumberTheory.JointDickman.Probability.FiniteChannels

namespace OAI

/-!
# From two-split kernels to channel estimates

The channel input may be signed: the estimates here therefore also apply
when the transition probabilities have been centered in their residue
coordinate. No probabilistic or analytic estimate is assumed implicitly.
-/

namespace JointDickman

open Finset

private theorem weighted_product_cauchy {Ω : Type*} [Fintype Ω]
    (w f g : Ω → ℝ) (hw : ∀ s, 0 ≤ w s) :
    (∑ s, w s * f s * g s) ^ 2 ≤
      (∑ s, w s * f s ^ 2) * ∑ s, w s * g s ^ 2 := by
  apply sum_sq_le_sum_mul_sum_of_sq_le_mul
  · intro s _
    exact mul_nonneg (hw s) (sq_nonneg _)
  · intro s _
    exact mul_nonneg (hw s) (sq_nonneg _)
  · intro s _
    ring_nf
    exact le_rfl

/-- The quadratic-form version of the weighted Schur bound. -/
theorem finiteKernelAction_quadratic_bound {A : Type*} [Fintype A]
    (μ : A → ℝ) (K : A → A → ℝ) (hμ : ∀ a, 0 ≤ μ a)
    {C : ℝ} (hrow : ∀ a, (∑ b, μ b * |K a b|) ≤ C)
    (hcol : ∀ b, (∑ a, μ a * |K a b|) ≤ C) (g : A → ℝ) :
    (∑ a, μ a * g a * finiteKernelAction μ K g a) ≤
      C * ∑ a, μ a * g a ^ 2 := by
  have hpoint (a b : A) :
      2 * (μ a * g a * (μ b * K a b * g b)) ≤
        μ a * μ b * |K a b| * (g a ^ 2 + g b ^ 2) := by
    have habs : K a b * g a * g b ≤ |K a b| * |g a| * |g b| := by
      simpa only [abs_mul] using le_abs_self (K a b * g a * g b)
    have hsq := sq_nonneg (|g a| - |g b|)
    rw [sub_sq, sq_abs, sq_abs] at hsq
    have hbase : 2 * (K a b * g a * g b) ≤ |K a b| * (g a ^ 2 + g b ^ 2) := by
      nlinarith [mul_nonneg (abs_nonneg (K a b)) hsq]
    convert mul_le_mul_of_nonneg_left hbase (mul_nonneg (hμ a) (hμ b)) using 1 <;> ring
  have hdouble :
      2 * (∑ a, μ a * g a * finiteKernelAction μ K g a) ≤
        ∑ a, ∑ b, μ a * μ b * |K a b| * (g a ^ 2 + g b ^ 2) := by
    simp only [finiteKernelAction, mul_sum]
    exact sum_le_sum fun a _ => sum_le_sum fun b _ => hpoint a b
  have hsplit :
      (∑ a, ∑ b, μ a * μ b * |K a b| * (g a ^ 2 + g b ^ 2)) =
        (∑ a, μ a * g a ^ 2 * ∑ b, μ b * |K a b|) +
        ∑ b, μ b * g b ^ 2 * ∑ a, μ a * |K a b| := by
    simp_rw [mul_add, sum_add_distrib]
    congr 1
    · simp_rw [mul_sum]
      apply sum_congr rfl
      intro a _
      apply sum_congr rfl
      intro b _
      ring
    · rw [sum_comm]
      simp_rw [mul_sum]
      apply sum_congr rfl
      intro b _
      apply sum_congr rfl
      intro a _
      ring
  rw [hsplit] at hdouble
  have hr : (∑ a, μ a * g a ^ 2 * ∑ b, μ b * |K a b|) ≤
      C * ∑ a, μ a * g a ^ 2 := by
    rw [mul_sum]
    exact sum_le_sum fun a _ => by
      simpa [mul_comm C] using mul_le_mul_of_nonneg_left (hrow a)
        (mul_nonneg (hμ a) (sq_nonneg _))
  have hc : (∑ b, μ b * g b ^ 2 * ∑ a, μ a * |K a b|) ≤
      C * ∑ b, μ b * g b ^ 2 := by
    rw [mul_sum]
    exact sum_le_sum fun b _ => by
      simpa [mul_comm C] using mul_le_mul_of_nonneg_left (hcol b)
        (mul_nonneg (hμ b) (sq_nonneg _))
  linarith

/-- A bound for the two-split kernel controls the original channel.
Unlike a marginal estimate, this applies to signed, centered channels. -/
theorem finiteChannel_square_of_kernel_rows {Ω A : Type*} [Fintype Ω] [Fintype A]
    (w : Ω → ℝ) (μ : A → ℝ) (p : Ω → A → ℝ)
    (hw : ∀ s, 0 ≤ w s) (hμ : ∀ a, 0 < μ a) {C : ℝ} (hC : 0 ≤ C)
    (hrow : ∀ a, (∑ b, μ b * |finiteTwoSplitKernel w μ p a b|) ≤ C)
    (f : Ω → ℝ) :
    (∑ a, μ a * finiteChannel w μ p f a ^ 2) ≤ C * ∑ s, w s * f s ^ 2 := by
  let g := finiteChannel w μ p f
  let h := finiteChannelAdjoint p g
  let E := ∑ a, μ a * g a ^ 2
  let F := ∑ s, w s * f s ^ 2
  let H := ∑ s, w s * h s ^ 2
  have hμ0 : ∀ a, μ a ≠ 0 := fun a => ne_of_gt (hμ a)
  have hE : 0 ≤ E := sum_nonneg fun a _ => mul_nonneg (hμ a).le (sq_nonneg _)
  have hF : 0 ≤ F := sum_nonneg fun s _ => mul_nonneg (hw s) (sq_nonneg _)
  have hpair : E = ∑ s, w s * f s * h s := by
    calc
      E = ∑ a, μ a * finiteChannel w μ p f a * g a := by
        apply sum_congr rfl
        intro a _
        dsimp [g]
        ring
      _ = _ := finiteChannel_adjoint w μ p hμ0 f g
  have hcauchy : E ^ 2 ≤ F * H := by
    rw [hpair]
    exact weighted_product_cauchy w f h hw
  have hcol : ∀ b, (∑ a, μ a * |finiteTwoSplitKernel w μ p a b|) ≤ C := by
    intro b
    simpa only [finiteTwoSplitKernel_symm w μ p] using hrow b
  have hquad := finiteKernelAction_quadratic_bound μ (finiteTwoSplitKernel w μ p)
    (fun a => (hμ a).le) hrow hcol g
  have hkernel : H = ∑ a, μ a * g a *
      finiteKernelAction μ (finiteTwoSplitKernel w μ p) g a := by
    calc
      H = ∑ a, μ a * finiteChannel w μ p h a * g a := by
        rw [finiteChannel_adjoint w μ p hμ0 h g]
        apply sum_congr rfl
        intro s _
        dsimp [h]
        ring
      _ = _ := by
        apply sum_congr rfl
        intro a _
        rw [finiteTwoSplitKernel_action w μ p hμ0]
        change μ a * finiteChannel w μ p h a * g a =
          μ a * g a * finiteChannel w μ p h a
        ring
  rw [← hkernel] at hquad
  have hmain : E ^ 2 ≤ F * (C * E) :=
    hcauchy.trans (mul_le_mul_of_nonneg_left hquad hF)
  change E ≤ C * F
  by_cases hzero : E = 0
  · rw [hzero]
    exact mul_nonneg hC hF
  · have hpos : 0 < E := lt_of_le_of_ne hE (Ne.symm hzero)
    nlinarith

end JointDickman

end OAI
