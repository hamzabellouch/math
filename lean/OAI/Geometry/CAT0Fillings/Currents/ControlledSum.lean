import Mathlib
import OAI.Geometry.CAT0Fillings.Currents.ComponentMass
import OAI.Geometry.CAT0Fillings.Currents.SumControls

namespace OAI

section
section
open Filter Set
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal
open Set MeasureTheory
open scoped RealInnerProductSpace
open Matrix
open scoped RealInnerProductSpace MatrixOrder
open Set Filter MeasureTheory
open MeasureTheory Filter Set Metric
open scoped Topology Pointwise NNReal
open Set MeasureTheory Measure Filter Module
open Set Filter MeasureTheory Measure ContinuousLinearMap
open scoped Topology Convolution NNReal
open Set Filter MeasureTheory Measure Metric
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology NNReal
open Set MeasureTheory Filter
open scoped Topology ENNReal NNReal

namespace CAT0Fillings
open Set MeasureTheory Filter
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] {k : ℕ}
lemma IsMetricCurrent.control_bound_uniform {T : Functional X k} (hT : IsMetricCurrent T)
    {μ : Measure X} [IsFiniteMeasure μ] (hμ : Controls T μ)
    {b : X → ℝ} (hb : BoundedLip b) {π : Fin k → X → ℝ}
    (K : Fin k → ℝ≥0) (hK : ∀ i, LipschitzWith (K i) (π i))
    {M : ℝ} (hM : ∀ x, |b x| ≤ M) :
    |T b π| ≤ ((∏ i, (K i : ℝ))*M)*μ.real univ := by
  have hi : Integrable (fun x => |b x|) μ := (hb.toBoundedContinuous.integrable μ).abs
  have hbound : (∫ x, |b x| ∂μ) ≤ μ.real univ * M := by
    simpa using integral_mono hi (integrable_const M) hM
  calc
    _ ≤ (∏ i, (K i : ℝ)) * ∫ x, |b x| ∂μ := hT.mass_bound hμ hb K hK
    _ ≤ (∏ i, (K i : ℝ)) * (μ.real univ*M) :=
      mul_le_mul_of_nonneg_left hbound (Finset.prod_nonneg fun i _ => (K i).coe_nonneg)
    _ = _ := by ring

lemma summable_controlled_actions {T : ℕ → Functional X k}
    (hT : ∀ i, IsMetricCurrent (T i)) {μ : ℕ → Measure X}
    [∀ i, IsFiniteMeasure (μ i)] (hμ : ∀ i, Controls (T i) (μ i))
    (hS : Summable (fun i => (μ i).real univ))
    (b : X → ℝ) (π : Fin k → X → ℝ) : Summable (fun i => T i b π) := by
  by_cases h : Admissible b π
  · choose K hK using h.2
    obtain ⟨M,hM⟩ := h.1.2
    exact (hS.mul_left ((∏ j, (K j : ℝ))*M)).of_norm_bounded
      (fun i => by simpa only [Real.norm_eq_abs] using
        (hT i).control_bound_uniform (hμ i) h.1 K hK hM)
  · simp only [fun i => (hT i).offDomain b π h,summable_zero]

lemma isMetricCurrent_tsum_controlled {T : ℕ → Functional X k}
    (hT : ∀ i, IsMetricCurrent (T i)) {μ : ℕ → Measure X}
    [∀ i, IsFiniteMeasure (μ i)] (hμ : ∀ i, Controls (T i) (μ i))
    (hS : Summable (fun i => (μ i).real univ)) :
    IsMetricCurrent (fun b π => ∑' i, T i b π) := by
  have hs := summable_controlled_actions hT hμ hS
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
      (hS.mul_left ((∏ j, (K j : ℝ))*M))
      (fun i => (hT i).sequentialContinuity b π πs hb (fun j => ⟨K j,hK j⟩) hlim)
    exact Eventually.of_forall (fun j i =>
      (hT i).control_bound_uniform (hμ i) hb K (fun l => hK l j) hM)
  · intro b π hab hloc
    simp only [fun i => (hT i).locality b π hab hloc,tsum_zero]
  · let := finite_sum_measure_of_summable_total μ hS
    exact ⟨Measure.sum μ,inferInstance,controls_sum_general hμ (fun _ _ => rfl)⟩

end CAT0Fillings

end
end

end OAI
