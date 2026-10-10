import OAI.Geometry.RCD.Sobolev.WeakLocalizedTests
import OAI.Geometry.RCD.Sobolev.BoundedLipschitzProduct

namespace OAI

/-! # Uniform bounded Lipschitz tests on a continuity ball

The common quantitative outer test bound and a single family of inner
cutoffs provide uniform, rather than pointwise-in-test, localization.
-/

open Set Metric Filter MeasureTheory
open scoped Topology BoundedContinuousFunction NNReal
noncomputable section
namespace RegularPointCoordinates
variable {Y : Type*} [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]

theorem uniform_localized_lipschitz_tests
    {ν : ProbabilityMeasure Y} {νs : ℕ → ProbabilityMeasure Y}
    (hweak : Tendsto νs atTop (𝓝 ν)) (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0))
    {s : Set Y} (hs : MeasurableSet s)
    (hmass : Tendsto (fun k => (νs k : Measure Y).real s) atTop (𝓝 ((ν : Measure Y).real s)))
    (χ : ℕ → Y →ᵇ ℝ) (L : ℕ → ℝ≥0) (hχL : ∀ m, LipschitzWith (L m) (χ m))
    (hχ : ∀ m x, 0≤χ m x ∧ χ m x≤1) (hχ0 : ∀ m x, x∉s → χ m x=0)
    (hχlim : ∀ x, Tendsto (fun m => χ m x) atTop (𝓝 (s.indicator (fun _ => (1:ℝ)) x)))
    (hbound : ∀ k (C : ℝ≥0), 0<C → ∀ F : Y → ℝ, LipschitzWith C F →
      (∀ x, |F x|≤C) → |(∫ x, F x ∂(νs k : Measure Y))-(∫ x, F x ∂(ν : Measure Y))|≤C*ε k) :
    ∀ η : ℝ, 0<η → ∀ᶠ k in atTop, ∀ φ : Y →ᵇ ℝ, LipschitzWith 1 φ → ‖φ‖≤1 →
      |(∫ x in s, φ x ∂(νs k : Measure Y))-(∫ x in s, φ x ∂(ν : Measure Y))|<η := by
  have hcut := tendsto_integral_of_dominated_convergence (μ := (ν : Measure Y))
    (fun _ => (1:ℝ)) (fun m => (χ m).continuous.aestronglyMeasurable)
    (integrable_const 1) (fun m => Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs,abs_of_nonneg (hχ m x).1]
      exact (hχ m x).2) (Eventually.of_forall hχlim)
  simp only [integral_indicator hs,setIntegral_const,smul_eq_mul,mul_one] at hcut
  have hdef : Tendsto (fun m => (ν : Measure Y).real s-∫ x, χ m x ∂(ν : Measure Y))
      atTop (𝓝 0) := by simpa only [sub_self] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (ν : Measure Y).real s)
          atTop (𝓝 ((ν : Measure Y).real s))).sub hcut
  intro η hη
  obtain ⟨m,hm⟩ := (hdef.eventually (Iio_mem_nhds (show 0<η/4 by positivity))).exists
  have hdev := (hmass.sub (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hweak (χ m))).eventually
    (Iio_mem_nhds (show (ν : Measure Y).real s-(∫ x, χ m x ∂(ν : Measure Y))<η/4 from hm))
  have hsmall := (hε.const_mul ((L m+1:ℝ≥0):ℝ)).eventually
    (Iio_mem_nhds (show ((L m+1:ℝ≥0):ℝ)*0<η/4 by simp; positivity))
  filter_upwards [hdev,hsmall] with k hk hek
  intro φ hφ hφn
  have hφb (x : Y) : |φ x|≤1 := by
    simpa only [Real.norm_eq_abs] using (φ.norm_coe_le_norm x).trans hφn
  have hχb (x : Y) : |χ m x|≤1 := by rw [abs_of_nonneg (hχ m x).1]; exact (hχ m x).2
  have hp := hbound k (L m+1) (by positivity) (fun x => χ m x*φ x)
    (bounded_unit_lipschitz_product (hχL m) hφ hχb hφb) (fun x => by
      rw [abs_mul]
      exact (mul_le_mul (hχb x) (hφb x) (abs_nonneg _) zero_le_one).trans (by simp))
  have he₁ := bounded_test_cutoff_error (νs k : Measure Y) hs φ (χ m) (hχ m) (hχ0 m)
  have he₂ := bounded_test_cutoff_error (ν : Measure Y) hs φ (χ m) (hχ m) (hχ0 m)
  have hb₁ : |(∫ x in s, φ x ∂(νs k : Measure Y))-
      (∫ x, χ m x*φ x ∂(νs k : Measure Y))|≤η/4 :=
    he₁.trans ((mul_le_mul_of_nonneg_left hk.le (norm_nonneg φ)).trans
      (mul_le_of_le_one_left (by positivity) hφn))
  have hb₂ : |(∫ x in s, φ x ∂(ν : Measure Y))-
      (∫ x, χ m x*φ x ∂(ν : Measure Y))|≤η/4 :=
    he₂.trans ((mul_le_mul_of_nonneg_left hm.le (norm_nonneg φ)).trans
      (mul_le_of_le_one_left (by positivity) hφn))
  have hb₃ := hp.trans_lt hek
  have ht₁ := abs_sub_le (∫ x in s, φ x ∂(νs k : Measure Y))
    (∫ x, χ m x*φ x ∂(νs k : Measure Y)) (∫ x in s, φ x ∂(ν : Measure Y))
  have ht₂ := abs_sub_le (∫ x, χ m x*φ x ∂(νs k : Measure Y))
    (∫ x, χ m x*φ x ∂(ν : Measure Y)) (∫ x in s, φ x ∂(ν : Measure Y))
  rw [abs_sub_comm (∫ x, χ m x*φ x ∂(ν : Measure Y))] at ht₂
  linarith

end RegularPointCoordinates

end

end OAI
