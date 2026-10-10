import OAI.Geometry.RCD.Sobolev.WeakMapPerturbation
import OAI.Geometry.RCD.Coordinates.NormalizedUniformMean

namespace OAI

/-! # Uniform source values paired with weakly converging image laws -/

open Set Filter MeasureTheory
open scoped Topology BoundedContinuousFunction
noncomputable section
namespace RegularPointCoordinates

theorem weak_map_uniform_integrals {A Y : Type*} [MeasurableSpace A]
    [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (P : ℕ → ProbabilityMeasure A) (v : ℕ → A → Y)
    (hv : ∀ k, Measurable (v k)) {Q : ProbabilityMeasure Y}
    (hweak : Tendsto (fun k => (P k).map (v k)) atTop (𝓝 Q))
    (u : ℕ → A → ℝ) (hu : ∀ k, Integrable (u k) (P k : Measure A))
    (F : Y →ᵇ ℝ)
    (herr : ∀ δ : ℝ, 0<δ → ∀ᶠ k in atTop,
      ∀ᵐ x ∂(P k : Measure A), |u k x-F (v k x)|≤δ) :
    Tendsto (fun k => ∫ x, u k x ∂(P k : Measure A)) atTop
      (𝓝 (∫ z, F z ∂(Q : Measure Y))) := by
  have hi (k : ℕ) : Integrable (fun x => F (v k x)) (P k : Measure A) :=
    (integrable_const ‖F‖).mono' (F.continuous.measurable.comp (hv k)).aestronglyMeasurable
      (Eventually.of_forall fun x => F.norm_coe_le_norm (v k x))
  have hz := normalized_mean_tendsto_zero (fun k => (P k : Measure A))
    (fun _ => by simp only [Measure.real,measure_univ,ENNReal.toReal_one]; norm_num)
    (fun k x => u k x-F (v k x)) herr
  simp only [Measure.real,measure_univ,ENNReal.toReal_one,inv_one,one_mul] at hz
  have ht := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hweak F
  have heq (k : ℕ) : (∫ z, F z ∂((P k).map (v k) : Measure Y))=
      ∫ x, F (v k x) ∂(P k : Measure A) := by
    rw [ProbabilityMeasure.toMeasure_map,integral_map (hv k).aemeasurable
      F.continuous.aestronglyMeasurable]
  simp only [heq] at ht
  have hh := hz.add ht
  simpa only [integral_sub (hu _) (hi _),sub_add_cancel,zero_add] using hh

end RegularPointCoordinates

end

end OAI
