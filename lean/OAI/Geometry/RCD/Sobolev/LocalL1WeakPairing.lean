import OAI.Geometry.RCD.Metric.ProbabilityDominationL1

namespace OAI

/-! # Local L1 convergence paired with weakly convergent bounded densities -/

open Set Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

theorem local_L1_weak_pairing (μ : Measure X) [μ.WeaklyRegular]
    (P : ℕ → ProbabilityMeasure X) (Q : ProbabilityMeasure X)
    (hweak : Tendsto P atTop (𝓝 Q)) {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hP : ∀ k, (P k : Measure X) ≤ C • μ)
    {Ω : Set X} (hΩ : MeasurableSet Ω)
    (F : ℕ → X → ℝ) (hF : ∀ k, Integrable (F k) μ)
    (hz : ∀ k x, x ∉ Ω → F k x = 0)
    (J : Lp ℝ 1 (μ.restrict Ω))
    (hlim : Tendsto (fun k => ∫ x in Ω, |F k x-J x| ∂μ) atTop (𝓝 0)) :
    Tendsto (fun k => ∫ x, F k x ∂(P k : Measure X)) atTop
      (𝓝 (∫ x in Ω, J x ∂(Q : Measure X))) := by
  let f := Ω.indicator (fun x => J x)
  have hf : Integrable f μ := (integrable_indicator_iff hΩ).mpr
    (memLp_one_iff_integrable.mp (Lp.memLp J))
  have he (k : ℕ) : (∫ x, |F k x-f x| ∂μ) = ∫ x in Ω, |F k x-J x| ∂μ := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ω)]
    · apply integral_congr_ae
      filter_upwards [ae_restrict_mem hΩ] with x hx
      rw [show f x=J x from indicator_of_mem hx _]
    · intro x hx
      rw [hz k x hx,show f x=0 from indicator_of_notMem hx _]
      norm_num
  have hh := weak_probability_integral_L1_varying μ P Q hweak hC hP F f hF hf
    (by simpa only [he] using hlim)
  simpa only [f,integral_indicator hΩ] using hh

end RegularPointCoordinates

end

end OAI
