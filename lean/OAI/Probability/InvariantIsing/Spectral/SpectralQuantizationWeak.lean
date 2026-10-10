import OAI.Probability.InvariantIsing.Spectral.SpectralNullBoundaryCover

namespace OAI

/-! Uniformly small spectral quantizations converge weakly to the
original law. This uses bounded Lipschitz tests, with explicit error control. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace InvariantIsing

lemma spectral_quantization_weak (μ : ProbabilityMeasure ℝ)
    (q : ℕ → ℝ → ℝ) (hq : ∀ k, Measurable (q k)) (δ : ℕ → ℝ)
    (hδ : Tendsto δ atTop (𝓝 0)) (hclose : ∀ k, ∀ᵐ x ∂(μ : Measure ℝ), dist (q k x) x ≤ δ k) :
    Tendsto (fun k => μ.map (q k)) atTop (𝓝 μ) := by
  apply tendsto_iff_forall_lipschitz_integral_tendsto.mpr
  intro f hf hfLip
  obtain ⟨C,hC⟩ := hf
  obtain ⟨L,hL⟩ := hfLip
  have hb x : ‖f x‖ ≤ C+|f 0| := by
    have hh := abs_add_le (f x-f 0) (f 0)
    rw [sub_add_cancel] at hh
    exact hh.trans (add_le_add (by simpa only [Real.dist_eq] using hC x 0) le_rfl)
  have hfi : Integrable f (μ : Measure ℝ) :=
    (integrable_const (C+|f 0|)).mono' hL.continuous.measurable.aestronglyMeasurable
      (ae_of_all _ hb)
  have hqi k : Integrable (fun x => f (q k x)) (μ : Measure ℝ) :=
    (integrable_const (C+|f 0|)).mono' (hL.continuous.measurable.comp (hq k)).aestronglyMeasurable
      (ae_of_all _ fun x => hb (q k x))
  have he k : |(∫ x, f x ∂(μ.map (q k) : Measure ℝ)) - ∫ x, f x ∂(μ : Measure ℝ)| ≤
      (L : ℝ)*δ k := by
    rw [ProbabilityMeasure.toMeasure_map, integral_map (hq k).aemeasurable
      hL.continuous.measurable.aestronglyMeasurable,← integral_sub (hqi k) hfi,← Real.norm_eq_abs]
    have hh : ∀ᵐ x ∂(μ : Measure ℝ), ‖f (q k x)-f x‖ ≤ (L : ℝ)*δ k := by
      filter_upwards [hclose k] with x hx
      calc
        _ ≤ (L : ℝ)*dist (q k x) x := by simpa only [dist_eq_norm] using hL.dist_le_mul (q k x) x
        _ ≤ _ := mul_le_mul_of_nonneg_left hx L.coe_nonneg
    simpa only [probReal_univ,mul_one] using norm_integral_le_of_norm_le_const hh
  have hz : Tendsto (fun k => (∫ x, f x ∂(μ.map (q k) : Measure ℝ))-
      ∫ x, f x ∂(μ : Measure ℝ)) atTop (𝓝 0) :=
    squeeze_zero_norm (fun k => by simpa only [Real.norm_eq_abs] using he k)
      (by simpa only [mul_zero] using hδ.const_mul (L : ℝ))
  simpa only [sub_add_cancel,zero_add] using hz.add_const (∫ x, f x ∂(μ : Measure ℝ))

end InvariantIsing

end

end OAI
