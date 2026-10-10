import OAI.Analysis.IrrationalRotation.Model.Analytic
import OAI.Analysis.IrrationalRotation.Rotation.ExponentialWeight
import OAI.Analysis.IrrationalRotation.Analysis.TruncatedLogIntegral

namespace OAI

open Filter MeasureTheory
open scoped ENNReal Topology

namespace Invariant233

@[simp] theorem negLogCost_zero : negLogCost 0 = ∞ := by
  simp [negLogCost]

theorem negLogCost_of_pos {t : ℝ} (ht : 0 < t) :
    negLogCost t = ENNReal.ofReal (-Real.log t) := by
  simp [negLogCost, ht.ne', abs_of_pos ht]

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem lintegral_negLogCost_eq_of_ae_pos (f : X → ℝ)
    (hpos : ∀ᵐ x ∂μ, 0 < f x) :
    (∫⁻ x, negLogCost (f x) ∂μ) =
      ∫⁻ x, ENNReal.ofReal (-Real.log (f x)) ∂μ := by
  apply lintegral_congr_ae
  filter_upwards [hpos] with x hx
  exact negLogCost_of_pos hx

theorem hasNegInfiniteLogIntegral_iff_of_ae_pos (f : X → ℝ)
    (hpos : ∀ᵐ x ∂μ, 0 < f x) :
    HasNegInfiniteLogIntegral μ f ↔
      (∫⁻ x, ENNReal.ofReal (-Real.log (f x)) ∂μ) = ∞ := by
  unfold HasNegInfiniteLogIntegral
  rw [lintegral_negLogCost_eq_of_ae_pos f hpos]

theorem scalarWeightDeterminant_eq_zero_of_log_integral
    (f : X → ℝ) (h : HasNegInfiniteLogIntegral μ f) :
    scalarWeightDeterminant μ f = 0 := by
  unfold scalarWeightDeterminant
  rw [show (∫⁻ x, negLogCost (f x) ∂μ) = ∞ from h]
  simp

theorem ae_pos_of_nonneg_singleton_zero (f : X → ℝ) (a : X)
    (ha : μ {a} = 0) (hf : ∀ x, 0 ≤ f x)
    (hz : ∀ x, f x = 0 ↔ x = a) : ∀ᵐ x ∂μ, 0 < f x := by
  have hne : ∀ᵐ x ∂μ, x ≠ a := by
    simpa only [ae_iff, not_not, Set.ofPred_eq_eq_singleton] using ha
  filter_upwards [hne] with x hx
  exact lt_of_le_of_ne (hf x) (Ne.symm (fun h => hx ((hz x).mp h)))

@[simp] theorem circleMeasure_singleton (x : Circle) : circleMeasure {x} = 0 := by
  change volume {x} = 0
  rw [← Metric.closedBall_zero, AddCircle.volume_closedBall]
  norm_num

theorem IsContinuousCircleWeight.ae_pos {f : Circle → ℝ}
    (hf : IsContinuousCircleWeight f) : ∀ᵐ x ∂circleMeasure, 0 < f x := by
  apply ae_pos_of_nonneg_singleton_zero f 0
  · simp only [circleMeasure_singleton]
  · exact fun x => (hf.2.1 x).1
  · exact hf.2.2.1

theorem exists_continuous_circle_weight_of_cost (g : Circle → ℝ)
    (hc : ContinuousOn g ({0}ᶜ))
    (hg : ∀ x ≠ 0, 0 ≤ g x)
    (hlim : Tendsto g (𝓝[≠] 0) atTop)
    (hint : (∫⁻ x, ENNReal.ofReal (g x) ∂circleMeasure) = ∞) :
    ∃ f : Circle → ℝ, IsContinuousCircleWeight f ∧
      (∀ x ≠ 0, -Real.log (f x) = g x) := by
  obtain ⟨f, hfcont, hfrange, hfzero, hflog, hfinf⟩ :=
    exists_continuous_weight_of_cost circleMeasure 0 g (by simp only [circleMeasure_singleton])
      hc hg hlim hint
  have hpos : ∀ᵐ x ∂circleMeasure, 0 < f x :=
    ae_pos_of_nonneg_singleton_zero f 0 (by simp only [circleMeasure_singleton])
      (fun x => (hfrange x).1) hfzero
  exact ⟨f, ⟨hfcont, hfrange, hfzero,
    (hasNegInfiniteLogIntegral_iff_of_ae_pos f hpos).mpr hfinf⟩, hflog⟩

theorem IsContinuousCircleWeight.exists_truncated_log_integral_lt
    {f : Circle → ℝ} (hf : IsContinuousCircleWeight f) (a : ℝ) :
    ∃ M : ℝ, 0 < M ∧
      (∫ x, Real.log (max (f x) (Real.exp (-M))) ∂circleMeasure) < -2 * a := by
  let : IsFiniteMeasure circleMeasure := by unfold circleMeasure; infer_instance
  apply exists_pos_truncated_log_integral_lt f hf.1.measurable
    (fun x => (hf.2.1 x).1) (fun x => (hf.2.1 x).2) hf.ae_pos
  exact (hasNegInfiniteLogIntegral_iff_of_ae_pos f hf.ae_pos).mp hf.2.2.2

end Invariant233

end OAI
