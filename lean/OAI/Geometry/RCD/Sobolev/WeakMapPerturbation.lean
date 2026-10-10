import OAI.Geometry.RCD.Metric.MeasuredBallLaw

namespace OAI

/-! # Uniform metric errors preserve weak limits of measurable images -/

open Set Filter MeasureTheory Metric
open scoped Topology BoundedContinuousFunction
noncomputable section
namespace RegularPointCoordinates

theorem weak_limit_of_map_error {A Y : Type*} [MeasurableSpace A]
    [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (P : ℕ → ProbabilityMeasure A) (f g : ℕ → A → Y)
    (hf : ∀ k, Measurable (f k)) (hg : ∀ k, Measurable (g k))
    {δ : ℕ → ℝ} (hδ : Tendsto δ atTop (𝓝 0))
    (hdist : ∀ k, ∀ᵐ x ∂(P k : Measure A), dist (f k x) (g k x)≤δ k)
    {ν : ProbabilityMeasure Y}
    (hweak : Tendsto (fun k => (P k).map (g k)) atTop (𝓝 ν)) :
    Tendsto (fun k => (P k).map (f k)) atTop (𝓝 ν) := by
  apply MeasureTheory.tendsto_iff_forall_lipschitz_integral_tendsto.mpr
  intro φ hb hLip
  obtain ⟨L,hL⟩ := hLip
  let φ' : Y →ᵇ ℝ := ⟨⟨φ,hL.continuous⟩,hb⟩
  have hi (k : ℕ) (F : A → Y) (hF : Measurable F) :
      Integrable (fun x => φ (F x)) (P k : Measure A) :=
    (integrable_const ‖φ'‖).mono' (hL.continuous.measurable.comp hF).aestronglyMeasurable
      (Eventually.of_forall fun x => φ'.norm_coe_le_norm (F x))
  have hfi (k : ℕ) : (∫ y, φ y ∂((P k).map (f k) : Measure Y))=
      ∫ x, φ (f k x) ∂(P k : Measure A) := by
    rw [ProbabilityMeasure.toMeasure_map,integral_map (hf k).aemeasurable
      hL.continuous.aestronglyMeasurable]
  have hgi (k : ℕ) : (∫ y, φ y ∂((P k).map (g k) : Measure Y))=
      ∫ x, φ (g k x) ∂(P k : Measure A) := by
    rw [ProbabilityMeasure.toMeasure_map,integral_map (hg k).aemeasurable
      hL.continuous.aestronglyMeasurable]
  have herr (k : ℕ) :
      ‖(∫ x, φ (f k x) ∂(P k : Measure A))-(∫ x, φ (g k x) ∂(P k : Measure A))‖≤L*δ k := by
    rw [← integral_sub (hi k (f k) (hf k)) (hi k (g k) (hg k))]
    have hh := norm_integral_le_of_norm_le_const (μ := (P k : Measure A))
      (f := fun x => φ (f k x)-φ (g k x)) (hdist k |>.mono fun x hx => by
        rw [← dist_eq_norm]
        exact (hL.dist_le_mul _ _).trans (mul_le_mul_of_nonneg_left hx L.coe_nonneg))
    simpa using hh
  have hz : Tendsto (fun k => (∫ x, φ (f k x) ∂(P k : Measure A))-
      (∫ x, φ (g k x) ∂(P k : Measure A))) atTop (𝓝 0) := by
    apply Metric.tendsto_nhds.mpr
    intro η hη
    have hlim : Tendsto (fun k => (L:ℝ)*δ k) atTop (𝓝 0) := by
      simpa only [mul_zero] using hδ.const_mul (L:ℝ)
    filter_upwards [hlim.eventually (Iio_mem_nhds hη)] with k hk
    simpa only [dist_zero_right] using (herr k).trans_lt hk
  have ht := MeasureTheory.tendsto_iff_forall_lipschitz_integral_tendsto.mp hweak φ hb ⟨L,hL⟩
  simp_rw [hgi] at ht
  simpa only [hfi,zero_add,sub_add_cancel] using hz.add ht

end RegularPointCoordinates

end

end OAI
