import OAI.NumberTheory.JointDickman.Probability.ResidueAttenuation

namespace OAI

/-!
# Centered rows after discarding a small part of a kernel

Uniform averaging in a residue coordinate preserves weighted sums because
all residues over a base cell have the same weight. A nonnegative discarded
kernel therefore costs at most four times its row bound after centering.
The remaining kernel can be compared with a residue-independent kernel.
-/

namespace JointDickman

open scoped BigOperators

theorem finiteResidueAverage_nonneg {R : Type*} [Fintype R]
    (f : R → ℝ) (hf : ∀ r, 0 ≤ f r) : 0 ≤ finiteResidueAverage f := by
  exact div_nonneg (Finset.sum_nonneg fun r _ => hf r) (Nat.cast_nonneg _)

theorem finiteResidueAverage_mono {R : Type*} [Fintype R]
    (f g : R → ℝ) (hfg : ∀ r, f r ≤ g r) :
    finiteResidueAverage f ≤ finiteResidueAverage g := by
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum fun r _ => hfg r)
    (Nat.cast_nonneg _)

theorem finiteResidueAverage_le {R : Type*} [Fintype R] [Nonempty R]
    (f : R → ℝ) {C : ℝ} (hf : ∀ r, f r ≤ C) : finiteResidueAverage f ≤ C := by
  simpa only [finiteResidueAverage_const] using
    finiteResidueAverage_mono f (fun _ => C) hf

theorem sum_finiteResidueAverage {R : Type*} [Fintype R] [Nonempty R]
    (f : R → ℝ) : (∑ _r : R, finiteResidueAverage f) = ∑ r, f r := by
  have hn : (Fintype.card R : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, finiteResidueAverage]
  field_simp

/-- Averaging within an equal-weight residue fibre preserves total mass. -/
theorem weighted_sum_residueAverage {D R : Type*}
    [Fintype D] [Fintype R] [Nonempty R] (μ : D → ℝ) (f : D × R → ℝ) :
    (∑ a : D × R, μ a.1 * finiteResidueAverage (fun t => f (a.1, t))) =
      ∑ a : D × R, μ a.1 * f a := by
  simp only [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro d _
  simp_rw [← finiteResidueAverage_const_mul]
  exact sum_finiteResidueAverage (fun t => μ d * f (d, t))

theorem residueCenteredKernel_add {D R : Type*} [Fintype R]
    (K L : D × R → D × R → ℝ) (a b : D × R) :
    residueCenteredKernel (fun a b => K a b + L a b) a b =
      residueCenteredKernel K a b + residueCenteredKernel L a b := by
  unfold residueCenteredKernel
  simp only [finiteResidueAverage_add]
  ring

/-- All four nonnegative terms of the centering formula have controlled
weighted row sums. Only equality of weights inside each fibre is used. -/
theorem residueCenteredKernel_nonneg_rows {D R : Type*}
    [Fintype D] [Fintype R] [Nonempty R]
    (μ : D → ℝ) (K : D × R → D × R → ℝ)
    (hμ : ∀ d, 0 ≤ μ d) (hK : ∀ a b, 0 ≤ K a b) {C : ℝ}
    (hrow : ∀ a, (∑ b : D × R, μ b.1 * K a b) ≤ C) (a : D × R) :
    (∑ b : D × R, μ b.1 * |residueCenteredKernel K a b|) ≤ 4 * C := by
  have hfirst : (∑ b : D × R, μ b.1 *
      finiteResidueAverage (fun t => K (a.1, t) b)) ≤ C := by
    simp_rw [← finiteResidueAverage_const_mul]
    rw [← finiteResidueAverage_sum]
    exact finiteResidueAverage_le _ (fun t => hrow (a.1, t))
  have hsecond : (∑ b : D × R, μ b.1 *
      finiteResidueAverage (fun u => K a (b.1, u))) ≤ C := by
    rw [weighted_sum_residueAverage]
    exact hrow a
  have hboth : (∑ b : D × R, μ b.1 *
      finiteResidueAverage (fun t =>
        finiteResidueAverage (fun u => K (a.1, t) (b.1, u)))) ≤ C := by
    simp_rw [← finiteResidueAverage_const_mul]
    rw [← finiteResidueAverage_sum]
    apply finiteResidueAverage_le
    intro t
    simp_rw [finiteResidueAverage_const_mul]
    rw [weighted_sum_residueAverage]
    exact hrow (a.1, t)
  have hp (b : D × R) : |residueCenteredKernel K a b| ≤
      K a b + finiteResidueAverage (fun t => K (a.1, t) b) +
        finiteResidueAverage (fun u => K a (b.1, u)) +
          finiteResidueAverage (fun t =>
            finiteResidueAverage (fun u => K (a.1, t) (b.1, u))) := by
    have h₀ := hK a b
    have h₁ := finiteResidueAverage_nonneg _ (fun t => hK (a.1, t) b)
    have h₂ := finiteResidueAverage_nonneg _ (fun u => hK a (b.1, u))
    have h₃ := finiteResidueAverage_nonneg _ (fun t =>
      finiteResidueAverage_nonneg _ (fun u => hK (a.1, t) (b.1, u)))
    unfold residueCenteredKernel
    rw [abs_le]
    constructor <;> linarith
  calc
    _ ≤ ∑ b : D × R, μ b.1 *
        (K a b + finiteResidueAverage (fun t => K (a.1, t) b) +
          finiteResidueAverage (fun u => K a (b.1, u)) +
            finiteResidueAverage (fun t =>
              finiteResidueAverage (fun u => K (a.1, t) (b.1, u)))) :=
      Finset.sum_le_sum fun b _ => mul_le_mul_of_nonneg_left (hp b) (hμ b.1)
    _ ≤ 4 * C := by
      simp only [mul_add, Finset.sum_add_distrib]
      linarith [hrow a]

/-- Decompose the actual kernel into a nonnegative discarded part with
small row mass and a part uniformly close to a residue-independent kernel. -/
theorem residueCenteredKernel_rows_of_discarded {D R : Type*}
    [Fintype D] [Fintype R] [Nonempty R]
    (μ : D → ℝ) (K L H : D × R → D × R → ℝ) (G : D → D → ℝ)
    (hμ : ∀ d, 0 ≤ μ d) (hL : ∀ a b, 0 ≤ L a b)
    (hdecomp : ∀ a b, K a b = L a b + H a b) {C ε : ℝ}
    (hrow : ∀ a, (∑ b : D × R, μ b.1 * L a b) ≤ C)
    (hflat : ∀ d e r s, |H (d, r) (e, s) - G d e| ≤ ε) (a : D × R) :
    (∑ b : D × R, μ b.1 * |residueCenteredKernel K a b|) ≤
      4 * C + 4 * ε * ∑ b : D × R, μ b.1 := by
  have hKeq : K = fun a b => L a b + H a b := by
    funext a b
    exact hdecomp a b
  rw [hKeq]
  simp_rw [residueCenteredKernel_add]
  calc
    _ ≤ ∑ b : D × R, μ b.1 *
        (|residueCenteredKernel L a b| + |residueCenteredKernel H a b|) :=
      Finset.sum_le_sum fun b _ => mul_le_mul_of_nonneg_left (abs_add_le _ _) (hμ b.1)
    _ = (∑ b : D × R, μ b.1 * |residueCenteredKernel L a b|) +
        ∑ b : D × R, μ b.1 * |residueCenteredKernel H a b| := by
      simp only [mul_add, Finset.sum_add_distrib]
    _ ≤ 4 * C + ∑ b : D × R, μ b.1 * (4 * ε) := by
      apply add_le_add (residueCenteredKernel_nonneg_rows μ L hμ hL hrow a)
      exact Finset.sum_le_sum fun b _ => mul_le_mul_of_nonneg_left
        (residueCenteredKernel_abs_le H G hflat a.1 b.1 a.2 b.2) (hμ b.1)
    _ = _ := by rw [← Finset.sum_mul]; ring

/-- The discarded-plus-flat kernel estimate controls the entire centered
channel, uniformly for every real input. -/
theorem residueChannel_square_of_discarded {Ω D R : Type*}
    [Fintype Ω] [Fintype D] [Fintype R] [Nonempty R]
    (w : Ω → ℝ) (μ : D → ℝ) (p : Ω → D × R → ℝ)
    (L H : D × R → D × R → ℝ) (G : D → D → ℝ)
    (hw : ∀ x, 0 ≤ w x) (hμ : ∀ d, 0 < μ d) (hL : ∀ a b, 0 ≤ L a b)
    (hdecomp : ∀ a b, finiteTwoSplitKernel w (fun a : D × R => μ a.1) p a b =
      L a b + H a b) {C ε : ℝ} (hC : 0 ≤ C) (hε : 0 ≤ ε)
    (hrow : ∀ a, (∑ b : D × R, μ b.1 * L a b) ≤ C)
    (hflat : ∀ d e r s, |H (d, r) (e, s) - G d e| ≤ ε) (f : Ω → ℝ) :
    (∑ a : D × R, μ a.1 *
      (finiteChannel w (fun a : D × R => μ a.1) p f a -
        finiteResidueAverage (fun t =>
          finiteChannel w (fun a : D × R => μ a.1) p f (a.1, t))) ^ 2) ≤
      (4 * C + 4 * ε * ∑ a : D × R, μ a.1) * ∑ x, w x * f x ^ 2 := by
  have hrows (a : D × R) :
      (∑ b : D × R, μ b.1 * |finiteTwoSplitKernel w (fun a : D × R => μ a.1)
        (residueCenteredTransition p) a b|) ≤
        4 * C + 4 * ε * ∑ b : D × R, μ b.1 := by
    have hk (a b : D × R) :
        finiteTwoSplitKernel w (fun a : D × R => μ a.1)
          (residueCenteredTransition p) a b =
          residueCenteredKernel (finiteTwoSplitKernel w (fun a : D × R => μ a.1) p) a b := by
      rcases a with ⟨d, r⟩
      rcases b with ⟨e, s⟩
      exact finiteTwoSplitKernel_residueCentered w μ p d e r s
    simp_rw [hk]
    exact residueCenteredKernel_rows_of_discarded μ _ L H G
      (fun d => (hμ d).le) hL hdecomp hrow hflat a
  have hbound := finiteChannel_square_of_kernel_rows w (fun a : D × R => μ a.1)
    (residueCenteredTransition p) hw (fun a => hμ a.1)
    (add_nonneg (mul_nonneg (by norm_num) hC)
      (mul_nonneg (mul_nonneg (by norm_num) hε)
        (Finset.sum_nonneg fun a _ => (hμ a.1).le))) hrows f
  convert hbound using 1
  apply Finset.sum_congr rfl
  intro a _
  rw [finiteChannel_residueCentered]

end JointDickman

end OAI
