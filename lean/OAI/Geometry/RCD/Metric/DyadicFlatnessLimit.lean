import OAI.Geometry.RCD.Metric.PointedScaleChange
import OAI.Geometry.RCD.Coordinates.FiniteDepthNormalization

namespace OAI

/-! # Metric Euclidean convergence at a sequence of deep dyadic scales -/

open Metric Filter
open scoped Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X]

theorem dyadic_flatness_limit {n : ℕ} (p : ℕ → X) (R ε : ℕ → ℝ) (d : ℕ → ℕ)
    (hR : ∀ k, 0 < R k) (hd : Tendsto d atTop atTop) (hε : Tendsto ε atTop (𝓝 0))
    (hflat : ∀ k, ∀ t : ℝ, 0 < t → t ≤ R k →
      ∃ f : X → Euclidean n, IsPointedApproximation (p k) 0 t 1 (ε k) f) :
    ∀ S η : ℝ, 0 < S → 0 < η → ∀ᶠ k in atTop,
      ∃ f : X → Euclidean n,
        IsPointedApproximation (p k) 0 (R k/(2 : ℝ)^(d k)) S η f := by
  intro S η hS hη
  have hsmall : Tendsto (fun k => S*(1/2 : ℝ)^(d k)) atTop (𝓝 0) := by
    simpa only [mul_zero,Function.comp_def] using
      ((tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1/2)
        (by norm_num : (1/2 : ℝ) < 1)).comp hd).const_mul S
  have herr : Tendsto (fun k => S*ε k) atTop (𝓝 0) := by
    simpa only [mul_zero] using hε.const_mul S
  filter_upwards [hsmall.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    herr.eventually (Iio_mem_nhds hη)] with k hk he
  have hrad : S*(R k/(2 : ℝ)^(d k)) ≤ R k := by
    have hm := mul_le_mul_of_nonneg_right hk.le (hR k).le
    have hp : (1/2 : ℝ)^(d k) = ((2 : ℝ)^(d k))⁻¹ := by rw [one_div,inv_pow]
    rw [hp] at hm
    simpa only [one_mul,mul_one,div_eq_mul_inv,mul_assoc,mul_left_comm,mul_comm] using hm
  have hr : 0 < R k/(2 : ℝ)^(d k) := div_pos (hR k) (by positivity)
  obtain ⟨f,hf⟩ := hflat k (S*(R k/(2 : ℝ)^(d k))) (mul_pos hS hr) hrad
  exact ⟨fun x => S • f x,(hf.rescale_unit hr hS).mono_error he.le⟩

end RegularPointCoordinates

end

end OAI
