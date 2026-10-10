import Mathlib
import OAI.Geometry.CAT0Fillings.Currents.ComponentMass

namespace OAI

section
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open Set MeasureTheory Filter
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
open Filter Set
open scoped Topology NNReal
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder

namespace CAT0Fillings
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}
lemma tsum_lintegral_norm_ne_top {f : ℕ → X → ℝ}
    (hf : ∀ i, Integrable (f i) μ)
    (hS : Summable (fun i => ∫ x, ‖f i x‖ ∂μ)) :
    ∑' i, ∫⁻ x, ‖f i x‖ₑ ∂μ ≠ ⊤ := by
  have h i : ∫⁻ x, ‖f i x‖ₑ ∂μ = ‖∫ x, ‖f i x‖ ∂μ‖ₑ := by
    dsimp [enorm]
    rw [lintegral_coe_eq_integral _ (hf i).norm]
    simp only [ENNReal.coe_nnreal_eq,coe_nnnorm,Real.norm_eq_abs]
    rw [abs_of_nonneg (integral_nonneg (fun x => abs_nonneg (f i x)))]
  rw [funext h]
  exact ENNReal.tsum_coe_ne_top_iff_summable.2 (NNReal.summable_coe.1 hS.abs)

lemma ae_summable_norm_of_integral {f : ℕ → X → ℝ}
    (hf : ∀ i, Integrable (f i) μ)
    (hS : Summable (fun i => ∫ x, ‖f i x‖ ∂μ)) :
    ∀ᵐ x ∂μ, Summable (fun i => ‖f i x‖) := by
  have ht := tsum_lintegral_norm_ne_top hf hS
  rw [←lintegral_tsum (fun i => (hf i).aestronglyMeasurable.enorm)] at ht
  filter_upwards [ae_lt_top' (AEMeasurable.tsum
    (fun i => (hf i).aestronglyMeasurable.enorm)) ht] with x hx
  exact tsum_enorm_ne_top_iff_summable_norm.mp hx.ne

lemma integrable_series_norm {f : ℕ → X → ℝ}
    (hf : ∀ i, Integrable (f i) μ)
    (hS : Summable (fun i => ∫ x, ‖f i x‖ ∂μ)) :
    Integrable (fun x => ∑' i, ‖f i x‖) μ := by
  refine ⟨by fun_prop,?_⟩
  have hfin : ∫⁻ x, ∑' i, ‖f i x‖ₑ ∂μ < ⊤ := by
    rw [lintegral_tsum (fun i => (hf i).aestronglyMeasurable.enorm)]
    exact (tsum_lintegral_norm_ne_top hf hS).lt_top
  change (∫⁻ x, ‖∑' i, ‖f i x‖‖ₑ ∂μ) < ⊤
  convert hfin using 1
  apply lintegral_congr_ae
  filter_upwards [ae_summable_norm_of_integral hf hS] with x hx
  simp_rw [←coe_nnnorm,←NNReal.coe_tsum,enorm_eq_nnnorm,NNReal.nnnorm_eq]
  exact ENNReal.coe_tsum (NNReal.summable_coe.mp hx)

lemma integrable_series {f : ℕ → X → ℝ}
    (hf : ∀ i, Integrable (f i) μ)
    (hS : Summable (fun i => ∫ x, ‖f i x‖ ∂μ)) :
    Integrable (fun x => ∑' i, f i x) μ := by
  apply (integrable_series_norm hf hS).mono' (by fun_prop)
  filter_upwards [ae_summable_norm_of_integral hf hS] with x hx
  exact norm_tsum_le_tsum_norm hx

end CAT0Fillings

namespace CAT0Fillings
open Set MeasureTheory Filter
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] {k : ℕ}

lemma summable_actions_all {T : ℕ → Functional X k}
    (hT : ∀ i, IsMetricCurrent (T i)) (hS : Summable (fun i => mass (T i)))
    (b : X → ℝ) (π : Fin k → X → ℝ) : Summable (fun i => T i b π) := by
  by_cases hab : Admissible b π
  · exact summable_actions_of_summable_masses hT hS hab
  · simp only [fun i => (hT i).offDomain b π hab,summable_zero]

theorem isMetricCurrent_tsum {T : ℕ → Functional X k}
    (hT : ∀ i, IsMetricCurrent (T i)) (hS : Summable (fun i => mass (T i))) :
    IsMetricCurrent (fun b π => ∑' i, T i b π) := by
  have hs := summable_actions_all hT hS
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · intro b π hab
    simp only [fun i => (hT i).offDomain b π hab,tsum_zero]
  · intro b c π a d hb hc hπ
    simp only [fun i => (hT i).linearFirst b c π a d hb hc hπ]
    rw [((hs b π).mul_left a).tsum_add ((hs c π).mul_left d)]
    simp only [tsum_mul_left]
  · intro b π j f a c hab hf
    simp only [fun i => (hT i).linearCoord b π j f a c hab hf]
    rw [((hs b π).mul_left a).tsum_add ((hs b (Function.update π j f)).mul_left c)]
    simp only [tsum_mul_left]
  · intro b π πs hb hπs hlim
    choose K hK using hπs
    obtain ⟨M,hM⟩ := hb.2
    apply tendsto_tsum_of_dominated_convergence
      (hS.mul_left ((∏ j, (K j : ℝ)) * M))
      (fun i => (hT i).sequentialContinuity b π πs hb (fun j => ⟨K j,hK j⟩) hlim)
    exact Eventually.of_forall (fun j i => (hT i).mass_bound_uniform hb K (fun l => hK l j) hM)
  · intro b π hab hloc
    simp only [fun i => (hT i).locality b π hab hloc,tsum_zero]
  · choose μ hfin hμ heq using fun i => (hT i).exists_controls_mass_eq
    let : ∀ i, IsFiniteMeasure (μ i) := hfin
    have hm : Summable (fun i => (μ i).real univ) := by simpa only [←heq] using hS
    let := finite_sum_measure_of_summable_total μ hm
    exact ⟨Measure.sum μ,inferInstance,controls_sum hμ (fun _ _ => rfl)⟩

lemma mass_tsum_le {T : ℕ → Functional X k}
    (hT : ∀ i, IsMetricCurrent (T i)) (hS : Summable (fun i => mass (T i))) :
    mass (fun b π => ∑' i, T i b π) ≤ ∑' i, mass (T i) := by
  choose μ hfin hμ heq using fun i => (hT i).exists_controls_mass_eq
  let : ∀ i, IsFiniteMeasure (μ i) := hfin
  have hm : Summable (fun i => (μ i).real univ) := by simpa only [←heq] using hS
  let := finite_sum_measure_of_summable_total μ hm
  apply (mass_le_measure (inferInstance : IsFiniteMeasure (Measure.sum μ)) (controls_sum hμ (fun _ _ => rfl))).trans_eq
  rw [measureReal_def,Measure.sum_apply _ MeasurableSet.univ, ENNReal.tsum_toReal_eq]
  · exact tsum_congr (fun i => (heq i).symm)
  · intro i
    exact measure_ne_top _ _

end CAT0Fillings
end

end OAI
