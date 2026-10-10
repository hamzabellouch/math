import OAI.Probability.InvariantIsing.Cavity.CavityFiberFactor
import Mathlib.MeasureTheory.Function.ContinuousMapDense

namespace OAI

/-! Continuous overlap tests determine a bounded measurable residual
once it is known to be a function of that overlap. -/

noncomputable section
open MeasureTheory Set
open scoped Topology BoundedContinuousFunction

namespace InvariantIsing

theorem cavity_ae_zero_of_measurable_overlap_tests {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : Ω → ℝ) (hp : Measurable p)
    (f : ℝ → ℝ) (hf : Measurable f) (hb : ∀ z, |f z| ≤ 1)
    (htest : ∀ Φ : ℝ →ᵇ ℝ, (∫ x, Φ (p x) * f (p x) ∂μ) = 0) :
    ∀ᵐ x ∂μ, f (p x) = 0 := by
  let ν := μ.map p
  let : IsProbabilityMeasure ν := (Measure.isProbabilityMeasure_map_iff hp.aemeasurable).mpr inferInstance
  have hi : Integrable f ν := Integrable.of_bound hf.aestronglyMeasurable 1
    (ae_of_all _ fun z => by simpa only [Real.norm_eq_abs] using hb z)
  have hs : Integrable (fun z => f z ^ 2) ν :=
    Integrable.of_bound (hf.pow_const 2).aestronglyMeasurable 1 (ae_of_all _ fun z => by
      rw [Real.norm_eq_abs, abs_pow]
      exact (pow_le_pow_left₀ (abs_nonneg _) (hb z) 2).trans_eq (one_pow 2))
  have hsmall (ε : ℝ) (hε : 0 < ε) : (∫ z, f z ^ 2 ∂ν) ≤ ε := by
    obtain ⟨Φ, hΦ, hiΦ⟩ := hi.exists_boundedContinuous_integral_sub_le hε
    have hicross : Integrable (fun z => Φ z * f z) ν := by
      apply Integrable.of_bound (Φ.continuous.measurable.mul hf).aestronglyMeasurable ‖Φ‖
      exact ae_of_all _ fun z => by
        rw [Real.norm_eq_abs, Pi.mul_apply, abs_mul]
        exact (mul_le_mul (Φ.norm_coe_le_norm z) (hb z) (abs_nonneg _) (norm_nonneg _)).trans_eq
          (mul_one _)
    have herr : Integrable (fun z => (f z - Φ z) * f z) ν := by
      apply (hi.sub hiΦ).abs.mono'
        (((hf.sub Φ.continuous.measurable).mul hf).aestronglyMeasurable)
      exact ae_of_all _ fun z => by
        rw [Real.norm_eq_abs, Pi.mul_apply, Pi.sub_apply, abs_mul]
        exact mul_le_of_le_one_right (abs_nonneg _) (hb z)
    have hz : (∫ z, Φ z * f z ∂ν) = 0 := by
      change (∫ z, (Φ * f) z ∂μ.map p) = 0
      rw [integral_map hp.aemeasurable ((Φ.continuous.measurable.mul hf).aestronglyMeasurable)]
      exact htest Φ
    have he : (∫ z, f z ^ 2 ∂ν) = (∫ z, (f z - Φ z) * f z ∂ν) +
        ∫ z, Φ z * f z ∂ν := by
      rw [← integral_add herr hicross]
      apply integral_congr_ae
      exact ae_of_all _ fun z => by ring
    rw [he, hz, add_zero]
    calc
      _ ≤ ∫ z, |f z - Φ z| ∂ν := integral_mono herr (hi.sub hiΦ).abs (fun z => by
        exact (le_abs_self _).trans (by
          rw [abs_mul]
          exact mul_le_of_le_one_right (abs_nonneg _) (hb z)))
      _ ≤ ε := by simpa only [Real.norm_eq_abs] using hΦ
  have hzero : (∫ z, f z ^ 2 ∂ν) = 0 := by
    apply le_antisymm _ (integral_nonneg (fun z => sq_nonneg (f z)))
    by_contra hn
    have hpos : 0 < ∫ z, f z ^ 2 ∂ν := lt_of_not_ge hn
    have hh := hsmall ((∫ z, f z ^ 2 ∂ν) / 2) (half_pos hpos)
    linarith
  have hae : ∀ᵐ z ∂ν, f z = 0 := by
    filter_upwards [(integral_eq_zero_iff_of_nonneg (fun z => sq_nonneg (f z)) hs).mp hzero] with z hz
    exact sq_eq_zero_iff.mp hz
  exact (ae_map_iff hp.aemeasurable (hf (measurableSet_singleton 0))).mp hae

/-- This is the separation step in cavity self-consistency, including
positive-mass plateaus of the limiting total-overlap path. -/
theorem cavity_overlap_self_consistency (p B : OverlapPath) (g : ℝ → ℝ)
    (hg : Monotone g) (hgb : ∀ z, 0 ≤ g z ∧ g z ≤ 1)
    (hfactor : B.val =ᵐ[pathMeasure] fun s => g (p s))
    (htest : ∀ Φ : ℝ →ᵇ ℝ, (∫ s, Φ (p s) * (B s - p s) ∂pathMeasure) = 0) :
    B.val =ᵐ[pathMeasure] p.val := by
  let f := fun z => g z - max 0 (min 1 z)
  have hf : Measurable f := hg.measurable.sub (measurable_const.max (measurable_const.min measurable_id))
  have hb (z : ℝ) : |f z| ≤ 1 := by
    have hc : 0 ≤ max 0 (min 1 z) ∧ max 0 (min 1 z) ≤ 1 := by
      exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩
    exact abs_le.mpr ⟨by dsimp [f]; linarith [(hgb z).1, hc.2],
      by dsimp [f]; linarith [(hgb z).2, hc.1]⟩
  have he (s : ℝ) : max 0 (min 1 (p s)) = p s :=
    (congrArg (max 0) (min_eq_right (p.le_one s))).trans (max_eq_right (p.nonneg s))
  have hz := cavity_ae_zero_of_measurable_overlap_tests pathMeasure p p.measurable f hf hb (by
    intro Φ
    rw [← htest Φ]
    apply integral_congr_ae
    filter_upwards [hfactor] with s hs
    simp only [f, he, hs])
  filter_upwards [hfactor, hz] with s hs hsz
  rw [hs]
  exact sub_eq_zero.mp (by simpa only [f, he] using hsz)

end InvariantIsing

end

end OAI
