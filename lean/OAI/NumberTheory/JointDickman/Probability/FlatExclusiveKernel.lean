import OAI.NumberTheory.JointDickman.Probability.CenteredKernelRows

namespace OAI

/-!
# Flattening the retained exclusive-product kernel

Conditioned on the common variable, the two retained exclusive outputs
are independent. An additive local-law error for each cell therefore
gives an explicit error for their product and for the integrated kernel.
The approximating profile may be signed: its required bound follows from
the local law and the fact that the actual cell probabilities lie in `[0,1]`.
-/

namespace JointDickman

open scoped BigOperators

/-- Kernel of two conditionally independent exclusive outputs sharing the
common variable. The denominators are the output-cell masses. -/
noncomputable def exclusiveProductKernel {C D R : Type*} [Fintype C]
    (w : C → ℝ) (μ : D → ℝ) (p : C → D × R → ℝ) (a b : D × R) : ℝ :=
  (∑ c, w c * p c a * p c b) / (μ a.1 * μ b.1)

/-- The local-law profile is independent of the residue coordinate. -/
noncomputable def flatExclusiveKernel {C D : Type*} [Fintype C]
    (w : C → ℝ) (μ : D → ℝ) (v : C → D → ℝ) (d e : D) : ℝ :=
  (∑ c, w c * v c d * v c e) / (μ d * μ e)

theorem exclusiveProductKernel_eq_finiteTwoSplitKernel {C D R : Type*}
    [Fintype C] [Fintype D] [Fintype R]
    (w : C → ℝ) (μ : D → ℝ) (p : C → D × R → ℝ) (a b : D × R) :
    exclusiveProductKernel w μ p a b =
      finiteTwoSplitKernel w (fun a : D × R => μ a.1) p a b := rfl

theorem local_profile_abs_le {a v η : ℝ} (ha₀ : 0 ≤ a) (ha₁ : a ≤ 1)
    (hlocal : |a - v| ≤ η) : |v| ≤ 1 + η := by
  calc
    |v| = |a + (v - a)| := by congr 1; ring
    _ ≤ |a| + |v - a| := abs_add_le _ _
    _ = a + |a - v| := by rw [abs_of_nonneg ha₀, abs_sub_comm]
    _ ≤ 1 + η := add_le_add ha₁ hlocal

/-- Product error from two genuine cell probabilities and their additive
local laws. No separate size bound for the profile is assumed. -/
theorem exclusive_probability_product_error {a b u v η : ℝ}
    (ha₀ : 0 ≤ a) (ha₁ : a ≤ 1) (hb₀ : 0 ≤ b) (hb₁ : b ≤ 1)
    (hη : 0 ≤ η) (ha : |a - u| ≤ η) (hb : |b - v| ≤ η) :
    |a * b - u * v| ≤ 2 * η + η ^ 2 := by
  have hu := local_profile_abs_le ha₀ ha₁ ha
  have hbabs : |b| ≤ 1 := by simpa only [abs_of_nonneg hb₀] using hb₁
  calc
    |a * b - u * v| = |(a - u) * b + u * (b - v)| := by congr 1; ring
    _ ≤ |(a - u) * b| + |u * (b - v)| := abs_add_le _ _
    _ = |a - u| * |b| + |u| * |b - v| := by rw [abs_mul, abs_mul]
    _ ≤ η * 1 + (1 + η) * η := add_le_add
      (mul_le_mul ha hbabs (abs_nonneg _) hη)
      (mul_le_mul hu hb (abs_nonneg _) (by linarith))
    _ = 2 * η + η ^ 2 := by ring

/-- Integrating the local-law product error against the actual common law
does not increase it. -/
theorem exclusiveProductKernel_flat_error {C D R : Type*} [Fintype C]
    (w : C → ℝ) (μ : D → ℝ) (p : C → D × R → ℝ) (v : C → D → ℝ)
    (hw : ∀ c, 0 ≤ w c) (hwnorm : ∑ c, w c = 1)
    (hμ : ∀ d, 0 < μ d) (hp₀ : ∀ c a, 0 ≤ p c a) (hp₁ : ∀ c a, p c a ≤ 1)
    {η : ℝ} (hη : 0 ≤ η)
    (hlocal : ∀ c d r, |p c (d, r) - v c d| ≤ η) (d e : D) (r s : R) :
    |exclusiveProductKernel w μ p (d, r) (e, s) - flatExclusiveKernel w μ v d e| ≤
      (2 * η + η ^ 2) / (μ d * μ e) := by
  have hnum : |(∑ c, w c * p c (d, r) * p c (e, s)) -
      ∑ c, w c * v c d * v c e| ≤ 2 * η + η ^ 2 := by
    calc
      _ = |∑ c, w c * (p c (d, r) * p c (e, s) - v c d * v c e)| := by
        congr 1
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro c _
        ring
      _ ≤ ∑ c, |w c * (p c (d, r) * p c (e, s) - v c d * v c e)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = ∑ c, w c * |p c (d, r) * p c (e, s) - v c d * v c e| := by
        simp_rw [abs_mul, abs_of_nonneg (hw _)]
      _ ≤ ∑ c, w c * (2 * η + η ^ 2) := by
        apply Finset.sum_le_sum
        intro c _
        exact mul_le_mul_of_nonneg_left
          (exclusive_probability_product_error (hp₀ c _) (hp₁ c _) (hp₀ c _) (hp₁ c _)
            hη (hlocal c d r) (hlocal c e s)) (hw c)
      _ = 2 * η + η ^ 2 := by rw [← Finset.sum_mul, hwnorm, one_mul]
  unfold exclusiveProductKernel flatExclusiveKernel
  rw [← sub_div, abs_div, abs_of_pos (mul_pos (hμ d) (hμ e))]
  exact div_le_div_of_nonneg_right hnum (mul_nonneg (hμ d).le (hμ e).le)

/-- A common positive lower bound for the cell weights makes the kernel
error uniform over all pairs of output cells. -/
theorem exclusiveProductKernel_flat_error_uniform {C D R : Type*} [Fintype C]
    (w : C → ℝ) (μ : D → ℝ) (p : C → D × R → ℝ) (v : C → D → ℝ)
    (hw : ∀ c, 0 ≤ w c) (hwnorm : ∑ c, w c = 1)
    {m : ℝ} (hm : 0 < m) (hmin : ∀ d, m ≤ μ d)
    (hp₀ : ∀ c a, 0 ≤ p c a) (hp₁ : ∀ c a, p c a ≤ 1)
    {η : ℝ} (hη : 0 ≤ η)
    (hlocal : ∀ c d r, |p c (d, r) - v c d| ≤ η) (d e : D) (r s : R) :
    |exclusiveProductKernel w μ p (d, r) (e, s) - flatExclusiveKernel w μ v d e| ≤
      (2 * η + η ^ 2) / (m * m) := by
  have hμ (d : D) : 0 < μ d := hm.trans_le (hmin d)
  exact (exclusiveProductKernel_flat_error w μ p v hw hwnorm hμ hp₀ hp₁ hη hlocal
    d e r s).trans (div_le_div_of_nonneg_left
      (add_nonneg (mul_nonneg (by norm_num) hη) (sq_nonneg η)) (mul_pos hm hm)
      (mul_le_mul (hmin d) (hmin e) hm.le (hμ d).le))

/-- The finite cutoff and flattening step for the actual channel. The high
kernel is the independently retained exclusive-product law; only its
cellwise local law is required, not an assumed kernel approximation. -/
theorem residueChannel_square_of_exclusive_local_law {Ω C D R : Type*}
    [Fintype Ω] [Fintype C] [Fintype D] [Fintype R] [Nonempty R]
    (wΩ : Ω → ℝ) (μ : D → ℝ) (q : Ω → D × R → ℝ)
    (w : C → ℝ) (p : C → D × R → ℝ) (v : C → D → ℝ)
    (L : D × R → D × R → ℝ)
    (hwΩ : ∀ x, 0 ≤ wΩ x) (hw : ∀ c, 0 ≤ w c) (hwnorm : ∑ c, w c = 1)
    {m : ℝ} (hm : 0 < m) (hmin : ∀ d, m ≤ μ d)
    (hp₀ : ∀ c a, 0 ≤ p c a) (hp₁ : ∀ c a, p c a ≤ 1)
    (hL : ∀ a b, 0 ≤ L a b)
    (hdecomp : ∀ a b, finiteTwoSplitKernel wΩ (fun a : D × R => μ a.1) q a b =
      L a b + exclusiveProductKernel w μ p a b)
    {B η : ℝ} (hB : 0 ≤ B) (hη : 0 ≤ η)
    (hrow : ∀ a, (∑ b : D × R, μ b.1 * L a b) ≤ B)
    (hlocal : ∀ c d r, |p c (d, r) - v c d| ≤ η) (f : Ω → ℝ) :
    (∑ a : D × R, μ a.1 *
      (finiteChannel wΩ (fun a : D × R => μ a.1) q f a -
        finiteResidueAverage (fun t =>
          finiteChannel wΩ (fun a : D × R => μ a.1) q f (a.1, t))) ^ 2) ≤
      (4 * B + 4 * ((2 * η + η ^ 2) / (m * m)) * ∑ a : D × R, μ a.1) *
        ∑ x, wΩ x * f x ^ 2 := by
  exact residueChannel_square_of_discarded wΩ μ q L (exclusiveProductKernel w μ p)
    (flatExclusiveKernel w μ v) hwΩ (fun d => hm.trans_le (hmin d)) hL hdecomp hB
    (div_nonneg (add_nonneg (mul_nonneg (by norm_num) hη) (sq_nonneg η))
      (mul_nonneg hm.le hm.le)) hrow
    (exclusiveProductKernel_flat_error_uniform w μ p v hw hwnorm hm hmin hp₀ hp₁ hη hlocal) f

end JointDickman

end OAI
