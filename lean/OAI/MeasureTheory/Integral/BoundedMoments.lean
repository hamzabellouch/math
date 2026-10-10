import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

namespace OAI

open Filter MeasureTheory
open scoped Topology

namespace LittlewoodFiniteFlatness

/-- A threshold estimate, including exponents strictly between zero and one. -/
lemma bounded_rpow_threshold {x δ p : ℝ} {k : ℕ}
    (hx : 0 ≤ x) (hx1 : x ≤ 1) (hδ : 0 < δ) (hp : 0 < p) :
    x ^ p ≤ δ ^ p + x ^ k / δ ^ k := by
  by_cases h : x ≤ δ
  · exact (Real.rpow_le_rpow hx h hp.le).trans
      (le_add_of_nonneg_right (div_nonneg (pow_nonneg hx _) (pow_nonneg hδ.le _)))
  · have hd : δ ^ k ≤ x ^ k := pow_le_pow_left₀ hδ.le (le_of_not_ge h) k
    have hratio : (1 : ℝ) ≤ x ^ k / δ ^ k := by
      apply (le_div_iff₀ (pow_pos hδ k)).2
      simpa using hd
    exact (Real.rpow_le_one hx hx1 hp.le).trans
      (hratio.trans (le_add_of_nonneg_left (Real.rpow_nonneg hδ.le p)))

/-- Bounded measurable functions: convergence of any positive integer moment
implies convergence of every positive real moment. No pointwise convergence is assumed. -/
theorem tendsto_integral_rpow_of_bounded_moment
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    (g : ℕ → α → ℝ) (hg : ∀ n, Measurable (g n))
    (hb : ∀ᶠ n in atTop, ∀ x, 0 ≤ g n x ∧ g n x ≤ 1)
    (k : ℕ) (_hk : 0 < k)
    (hmoment : Tendsto (fun n => ∫ x, g n x ^ k ∂μ) atTop (𝓝 0))
    (p : ℝ) (hp : 0 < p) :
    Tendsto (fun n => ∫ x, g n x ^ p ∂μ) atTop (𝓝 0) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    filter_upwards [hb] with n hn
    exact ha.trans_le (integral_nonneg fun x => Real.rpow_nonneg (hn x).1 p)
  · intro ε hε
    let δ : ℝ := (ε / 2) ^ (1 / p)
    have hδ : 0 < δ := Real.rpow_pos_of_pos (by positivity) _
    have hδp : δ ^ p = ε / 2 := by
      dsimp [δ]
      rw [← Real.rpow_mul (by positivity), one_div_mul_cancel (ne_of_gt hp), Real.rpow_one]
    have ht : Tendsto (fun n => (∫ x, g n x ^ k ∂μ) / δ ^ k) atTop (𝓝 0) := by
      simpa using hmoment.div_const (δ ^ k)
    have he : ∀ᶠ n in atTop, (∫ x, g n x ^ k ∂μ) / δ ^ k < ε / 2 :=
      (tendsto_order.1 ht).2 (ε / 2) (by positivity)
    filter_upwards [hb, he] with n hn he
    have hi : Integrable (fun x => g n x ^ p) μ := by
      apply (integrable_const (1 : ℝ)).mono'
        (((Real.continuous_rpow_const hp.le).measurable.comp (hg n)).aestronglyMeasurable)
      exact ae_of_all μ fun x => by
        change ‖g n x ^ p‖ ≤ (1 : ℝ)
        rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (hn x).1 p)]
        exact Real.rpow_le_one (hn x).1 (hn x).2 hp.le
    have hik : Integrable (fun x => g n x ^ k) μ := by
      apply (integrable_const (1 : ℝ)).mono' ((hg n).pow_const k).aestronglyMeasurable
      exact ae_of_all μ fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (hn x).1 k)]
        simpa using pow_le_pow_left₀ (hn x).1 (hn x).2 k
    have hbound : (∫ x, g n x ^ p ∂μ) ≤ δ ^ p + (∫ x, g n x ^ k ∂μ) / δ ^ k := by
      calc
        _ ≤ ∫ x, (δ ^ p + g n x ^ k / δ ^ k) ∂μ :=
          integral_mono hi ((integrable_const _).add (hik.div_const _))
            (fun x => bounded_rpow_threshold (hn x).1 (hn x).2 hδ hp)
        _ = _ := by rw [integral_add (integrable_const _) (hik.div_const _), integral_div]; simp
    rw [hδp] at hbound
    linarith

/-- The interface used by the normalized Littlewood family. -/
theorem tendsto_integral_abs_sub_one_rpow
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    (f : ℕ → α → ℝ) (hf : ∀ n, Measurable (f n))
    (h0 : ∀ n x, 0 ≤ f n x)
    (h2 : ∀ᶠ n in atTop, ∀ x, f n x ≤ 2)
    (hmoment : Tendsto (fun n => ∫ x, (f n x - 1) ^ (2 : ℕ) ∂μ) atTop (𝓝 0))
    (p : ℝ) (hp : 0 < p) :
    Tendsto (fun n => ∫ x, |f n x - 1| ^ p ∂μ) atTop (𝓝 0) := by
  apply tendsto_integral_rpow_of_bounded_moment μ (fun n x => |f n x - 1|)
    (fun n => continuous_abs.measurable.comp ((hf n).sub measurable_const)) ?_ 2 (by decide) ?_ p hp
  · filter_upwards [h2] with n hn
    intro x
    exact ⟨abs_nonneg _, abs_le.2 ⟨by linarith [h0 n x], by linarith [hn x]⟩⟩
  · simpa only [sq_abs] using hmoment

/-- Fourth-moment variant with exactly the same boundedness hypotheses. -/
theorem tendsto_integral_abs_sub_one_rpow_of_fourth
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    (f : ℕ → α → ℝ) (hf : ∀ n, Measurable (f n))
    (h0 : ∀ n x, 0 ≤ f n x)
    (h2 : ∀ᶠ n in atTop, ∀ x, f n x ≤ 2)
    (hmoment : Tendsto (fun n => ∫ x, (f n x - 1) ^ (4 : ℕ) ∂μ) atTop (𝓝 0))
    (p : ℝ) (hp : 0 < p) :
    Tendsto (fun n => ∫ x, |f n x - 1| ^ p ∂μ) atTop (𝓝 0) := by
  apply tendsto_integral_rpow_of_bounded_moment μ (fun n x => |f n x - 1|)
    (fun n => continuous_abs.measurable.comp ((hf n).sub measurable_const)) ?_ 4 (by decide) ?_ p hp
  · filter_upwards [h2] with n hn
    intro x
    exact ⟨abs_nonneg _, abs_le.2 ⟨by linarith [h0 n x], by linarith [hn x]⟩⟩
  · have hpow : ∀ a : ℝ, |a| ^ (4 : ℕ) = a ^ (4 : ℕ) := by
      intro a
      rw [← abs_pow, abs_of_nonneg (by positivity)]
    simpa only [hpow] using hmoment

end LittlewoodFiniteFlatness

end OAI
