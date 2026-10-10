import OAI.Analysis.KadisonKastler.StripContourBounds
import OAI.Analysis.KadisonKastler.StripContourRectangle
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

namespace OAI

/-! # Letting the horizontal strip edges tend to infinity -/

namespace KadisonKastler

open MeasureTheory Filter Set
open scoped Topology

noncomputable section

theorem stripSineQuotient_horizontal_tendsto (φ : ℝ) (hφ : |φ| < Real.pi)
    (f : ℂ → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ z : ℂ, |z.re| ≤ 1 / 2 → ‖f z‖ ≤ B)
    (σ : ℝ) (hσ : |σ| = 1) :
    Tendsto (fun n : ℕ => ∫ x : ℝ in (-1 / 2 : ℝ)..(1 / 2 : ℝ),
      stripSineQuotient φ f ((x : ℂ) + (σ * n : ℝ) * Complex.I)) atTop (𝓝 0) := by
  have ht : Tendsto (fun n : ℕ => Real.exp (-(Real.pi - |φ|) * (n : ℝ))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp
      (tendsto_const_nhds.neg_mul_atTop (neg_lt_zero.mpr (sub_pos.mpr hφ))
        tendsto_natCast_atTop_atTop)
  have hl := ht.const_mul (8 * B)
  rw [mul_zero] at hl
  apply squeeze_zero_norm' _ hl
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn' : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have habs : |σ * (n : ℝ)| = n := by rw [abs_mul, hσ, one_mul, abs_of_nonneg (Nat.cast_nonneg n)]
  have hlarge : 1 ≤ Real.pi * |σ * (n : ℝ)| := by
    rw [habs]
    nlinarith [Real.two_le_pi]
  have h : ‖∫ x : ℝ in (-1 / 2 : ℝ)..(1 / 2 : ℝ),
      stripSineQuotient φ f ((x : ℂ) + (σ * n : ℝ) * Complex.I)‖ ≤
      (8 * B * Real.exp (-(Real.pi - |φ|) * (n : ℝ))) * |(1 / 2 : ℝ) - (-1 / 2)| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro x hx
    have hx' : |x| ≤ 1 / 2 := by
      rw [Set.uIoc_of_le (by norm_num)] at hx
      exact abs_le.mpr ⟨by linarith [hx.1], hx.2⟩
    simpa only [habs] using stripSineQuotient_decay φ f B hB hb x (σ * n) hx' hlarge
  norm_num only [show (1 / 2 : ℝ) - (-1 / 2) = 1 by norm_num, abs_one, mul_one] at h
  simpa only [neg_div] using h

theorem stripSineQuotient_integral_edges_eq (φ : ℝ) (hφ : |φ| < Real.pi)
    (f : ℂ → ℂ)
    (hc : ContinuousOn f {z : ℂ | |z.re| ≤ 1 / 2})
    (hd : DifferentiableOn ℂ f {z : ℂ | |z.re| < 1 / 2})
    (B : ℝ) (hB : 0 ≤ B) (hb : ∀ z : ℂ, |z.re| ≤ 1 / 2 → ‖f z‖ ≤ B)
    (hr : Integrable (fun t : ℝ => stripSineQuotient φ f ((1 / 2 : ℂ) + t * Complex.I)))
    (hl : Integrable (fun t : ℝ => stripSineQuotient φ f ((-1 / 2 : ℂ) + t * Complex.I))) :
    (∫ t : ℝ, stripSineQuotient φ f ((1 / 2 : ℂ) + t * Complex.I)) =
      ∫ t : ℝ, stripSineQuotient φ f ((-1 / 2 : ℂ) + t * Complex.I) := by
  have htop := stripSineQuotient_horizontal_tendsto φ hφ f B hB hb 1 (by norm_num)
  have hbottom := stripSineQuotient_horizontal_tendsto φ hφ f B hB hb (-1) (by norm_num)
  have hright := intervalIntegral_tendsto_integral hr
    (tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop) tendsto_natCast_atTop_atTop
  have hleft := intervalIntegral_tendsto_integral hl
    (tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop) tendsto_natCast_atTop_atTop
  have he := ((hbottom.sub htop).add (hright.const_mul Complex.I)).sub (hleft.const_mul Complex.I)
  have hzero : Tendsto (fun n : ℕ =>
      (∫ x : ℝ in (-1 / 2 : ℝ)..(1 / 2 : ℝ),
        stripSineQuotient φ f ((x : ℂ) + (-1 * n : ℝ) * Complex.I)) -
      (∫ x : ℝ in (-1 / 2 : ℝ)..(1 / 2 : ℝ),
        stripSineQuotient φ f ((x : ℂ) + (1 * n : ℝ) * Complex.I)) +
      Complex.I * (∫ t : ℝ in -(n : ℝ)..(n : ℝ),
        stripSineQuotient φ f ((1 / 2 : ℂ) + t * Complex.I)) -
      Complex.I * (∫ t : ℝ in -(n : ℝ)..(n : ℝ),
        stripSineQuotient φ f ((-1 / 2 : ℂ) + t * Complex.I))) atTop (𝓝 0) := by
    have hf : (fun n : ℕ =>
      (∫ x : ℝ in (-1 / 2 : ℝ)..(1 / 2 : ℝ),
        stripSineQuotient φ f ((x : ℂ) + (-1 * n : ℝ) * Complex.I)) -
      (∫ x : ℝ in (-1 / 2 : ℝ)..(1 / 2 : ℝ),
        stripSineQuotient φ f ((x : ℂ) + (1 * n : ℝ) * Complex.I)) +
      Complex.I * (∫ t : ℝ in -(n : ℝ)..(n : ℝ),
        stripSineQuotient φ f ((1 / 2 : ℂ) + t * Complex.I)) -
      Complex.I * (∫ t : ℝ in -(n : ℝ)..(n : ℝ),
        stripSineQuotient φ f ((-1 / 2 : ℂ) + t * Complex.I))) = fun _ => 0 := by
      funext n
      simpa using stripSineQuotient_rectangle φ f hc hd (n : ℝ)
    rw [hf]
    exact tendsto_const_nhds
  have h := tendsto_nhds_unique he hzero
  simp only [sub_self, zero_add, sub_eq_zero, mul_eq_mul_left_iff, Complex.I_ne_zero,
    or_false] at h
  exact h

end

end KadisonKastler

end OAI
