import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Integral.DominatedConvergence

namespace OAI

/-! Bounded scalar multipliers on real L², including convergence when the
multiplier converges almost everywhere and the multiplied vector converges
strongly.  This is the analytic closure step in the scalar H¹ chain rule. -/

namespace PositiveEinsteinFour.Geometry

open MeasureTheory Filter
open scoped Topology

noncomputable section

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

def scalarCompositionL2Multiply (a : X → ℝ) (ha : AEStronglyMeasurable a μ)
    {C : ℝ} (hC : ∀ x, |a x| ≤ C) (f : Lp ℝ 2 μ) : Lp ℝ 2 μ :=
  ((Lp.memLp f).of_le_mul (ha.mul (Lp.aestronglyMeasurable f))
    (Eventually.of_forall fun x => by
      simpa only [Pi.mul_apply, Real.norm_eq_abs, abs_mul] using
        mul_le_mul_of_nonneg_right (hC x) (abs_nonneg (f x)))).toLp _

theorem scalarCompositionL2Multiply_coe (a : X → ℝ) (ha : AEStronglyMeasurable a μ)
    {C : ℝ} (hC : ∀ x, |a x| ≤ C) (f : Lp ℝ 2 μ) :
    scalarCompositionL2Multiply a ha hC f =ᵐ[μ] fun x => a x * f x :=
  MemLp.coeFn_toLp _

theorem scalarCompositionL2Multiply_norm_le (a : X → ℝ) (ha : AEStronglyMeasurable a μ)
    {C : ℝ} (hC : ∀ x, |a x| ≤ C) (f : Lp ℝ 2 μ) :
    ‖scalarCompositionL2Multiply a ha hC f‖ ≤ C * ‖f‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [scalarCompositionL2Multiply_coe a ha hC f] with x hx
  rw [hx, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
  exact mul_le_mul_of_nonneg_right (hC x) (abs_nonneg _)

theorem scalarL2_norm_sq (f : Lp ℝ 2 μ) :
    ‖f‖ ^ 2 = ∫ x, f x ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simp only [real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]

/-- Almost-everywhere convergence of uniformly bounded multipliers is strong
on each fixed L² vector. -/
theorem scalarCompositionL2Multiply_tendsto_fixed {a : ℕ → X → ℝ} {b : X → ℝ}
    (ha : ∀ n, AEStronglyMeasurable (a n) μ) (hb : AEStronglyMeasurable b μ)
    {C : ℝ} (hC : 0 ≤ C) (haC : ∀ n x, |a n x| ≤ C) (hbC : ∀ x, |b x| ≤ C)
    (hab : ∀ᵐ x ∂μ, Tendsto (fun n => a n x) atTop (𝓝 (b x)))
    (f : Lp ℝ 2 μ) :
    Tendsto (fun n => scalarCompositionL2Multiply (a n) (ha n) (haC n) f) atTop
      (𝓝 (scalarCompositionL2Multiply b hb hbC f)) := by
  let q : ℕ → Lp ℝ 2 μ := fun n =>
    scalarCompositionL2Multiply (a n) (ha n) (haC n) f - scalarCompositionL2Multiply b hb hbC f
  have hq (n : ℕ) : q n =ᵐ[μ] fun x => (a n x - b x) * f x := by
    filter_upwards [Lp.coeFn_sub (scalarCompositionL2Multiply (a n) (ha n) (haC n) f)
      (scalarCompositionL2Multiply b hb hbC f), scalarCompositionL2Multiply_coe (a n) (ha n) (haC n) f,
      scalarCompositionL2Multiply_coe b hb hbC f] with x hsub hx hy
    simpa only [q, Pi.sub_apply, hx, hy, sub_mul] using hsub
  have hi : Integrable (fun x => (2 * C) ^ 2 * f x ^ 2) μ :=
    (Lp.memLp f).integrable_sq.const_mul _
  have hd := tendsto_integral_of_dominated_convergence
    (fun x => (2 * C) ^ 2 * f x ^ 2)
    (fun n => ((ha n).sub hb).mul (Lp.aestronglyMeasurable f) |>.pow 2)
    hi (fun n => Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), mul_pow]
      have hbound : |a n x - b x| ≤ 2 * C :=
        (abs_sub (a n x) (b x)).trans (by linarith [haC n x, hbC x])
      have hs : (a n x - b x) ^ 2 ≤ (2 * C) ^ 2 := by
        simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (by positivity)).2 hbound
      exact mul_le_mul_of_nonneg_right hs (sq_nonneg _))
    (f := fun _ => (0 : ℝ)) (by
      filter_upwards [hab] with x hx
      have h0 : Tendsto (fun n => (a n x - b x) * f x) atTop (𝓝 0) := by
        simpa only [sub_self, zero_mul] using (hx.sub_const (b x)).mul_const (f x)
      simpa only [Pi.pow_apply, Pi.mul_apply, Pi.sub_apply,
        zero_pow (by decide : (2 : ℕ) ≠ 0)] using! h0.pow 2)
  have hs : Tendsto (fun n => ‖q n‖ ^ 2) atTop (𝓝 0) := by
    convert hd using 1
    · funext n
      rw [scalarL2_norm_sq]
      exact integral_congr_ae ((hq n).fun_comp fun r : ℝ => r ^ 2)
    · simp
  have hn : Tendsto (fun n => ‖q n‖) atTop (𝓝 0) := by
    have h := Real.continuous_sqrt.continuousAt.tendsto.comp hs
    simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _),
      Real.sqrt_zero] using h
  exact tendsto_iff_norm_sub_tendsto_zero.mpr hn

/-- Both factors may move: bounded multiplier convergence and strong L²
convergence imply strong convergence of their product. -/
theorem scalarCompositionL2Multiply_tendsto {a : ℕ → X → ℝ} {b : X → ℝ}
    (ha : ∀ n, AEStronglyMeasurable (a n) μ) (hb : AEStronglyMeasurable b μ)
    {C : ℝ} (hC : 0 ≤ C) (haC : ∀ n x, |a n x| ≤ C) (hbC : ∀ x, |b x| ≤ C)
    (hab : ∀ᵐ x ∂μ, Tendsto (fun n => a n x) atTop (𝓝 (b x)))
    {f : ℕ → Lp ℝ 2 μ} {g : Lp ℝ 2 μ} (hfg : Tendsto f atTop (𝓝 g)) :
    Tendsto (fun n => scalarCompositionL2Multiply (a n) (ha n) (haC n) (f n)) atTop
      (𝓝 (scalarCompositionL2Multiply b hb hbC g)) := by
  have heq (n : ℕ) : scalarCompositionL2Multiply (a n) (ha n) (haC n) (f n) =
      scalarCompositionL2Multiply (a n) (ha n) (haC n) (f n - g) +
        scalarCompositionL2Multiply (a n) (ha n) (haC n) g := by
    apply Lp.ext
    filter_upwards [scalarCompositionL2Multiply_coe (a n) (ha n) (haC n) (f n),
      scalarCompositionL2Multiply_coe (a n) (ha n) (haC n) (f n - g),
      scalarCompositionL2Multiply_coe (a n) (ha n) (haC n) g, Lp.coeFn_sub (f n) g,
      Lp.coeFn_add (scalarCompositionL2Multiply (a n) (ha n) (haC n) (f n - g))
        (scalarCompositionL2Multiply (a n) (ha n) (haC n) g)] with x h₁ h₂ h₃ h₄ h₅
    simp only [Pi.sub_apply, Pi.add_apply] at h₄ h₅
    rw [h₁, h₅, h₂, h₃, h₄]
    ring
  have hzero : Tendsto (fun n => scalarCompositionL2Multiply (a n) (ha n) (haC n) (f n - g))
      atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero (fun n => norm_nonneg _)
      (fun n => scalarCompositionL2Multiply_norm_le (a n) (ha n) (haC n) (f n - g))
    simpa using (tendsto_const_nhds.mul (tendsto_iff_norm_sub_tendsto_zero.mp hfg))
  simpa only [heq, zero_add] using
    hzero.add (scalarCompositionL2Multiply_tendsto_fixed ha hb hC haC hbC hab g)

end
end PositiveEinsteinFour.Geometry

end OAI
