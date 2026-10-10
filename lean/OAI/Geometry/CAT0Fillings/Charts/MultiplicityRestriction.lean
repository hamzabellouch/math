import Mathlib
import OAI.Geometry.CAT0Fillings.Currents.Restriction
import OAI.Geometry.CAT0Fillings.Currents.ActionLimits

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
attribute [local instance] Classical.propDecidable
namespace IntegerChart
open BorelCoefficients

variable {X : Type*} [MetricSpace X] [CompactSpace X]
variable [MeasurableSpace X] [BorelSpace X] [Nonempty X]
variable {k : ℕ} (C : IntegerChart X k)
lemma borelAction_eq_integral (hC : IsMetricCurrent C.action)
    {μ : Measure X} [IsFiniteMeasure μ] (hμ : Controls C.action μ)
    {b : X → ℝ} (hb : Measurable b) (hB : ∃ M : ℝ, ∀ x, |b x| ≤ M)
    (π : Fin k → X → ℝ) (hπ : ∀ i, ∃ K : ℝ≥0, LipschitzWith K (π i)) :
    borelAction μ hC b π =
      ∫ z, (C.multiplicity z : ℝ)*C.jacobian π z*b (C.paramExtended z)
        ∂volume.restrict C.domain := by
  choose K hK using hπ
  let w : Euc k → ℝ := fun z => (C.multiplicity z : ℝ)*C.jacobian π z
  have hw := C.integrable_weighted_jacobian (fun i => ⟨K i,hK i⟩)
  change Integrable w (volume.restrict C.domain) at hw
  have heq (f : X → ℝ) (hf : BoundedLip f) :
      C.action f π = ∫ z, w z*f (C.paramExtended z) ∂volume.restrict C.domain := by
    rw [action,ite_eq_left ⟨hf,fun i => ⟨K i,hK i⟩⟩]
    apply integral_congr_ae
    filter_upwards [C.scalar_ae_paramExtended f] with z hz
    change C.scalar f z = f (C.paramExtended z) at hz
    rw [hz]
    dsimp [w]
    ring
  have hcontrol (f : X → ℝ) (hf : BoundedLip f) :
      |∫ z, w z*f (C.paramExtended z) ∂volume.restrict C.domain| ≤
        ∫ x, |f x| ∂((∏ i,K i) • μ) := by
    rw [←heq f hf,integral_smul_nnreal_measure]
    simpa only [NNReal.smul_def,NNReal.coe_prod,smul_eq_mul] using hC.mass_bound hμ hf K hK
  have hbi : Integrable b μ := by
    obtain ⟨M,hM⟩ := hB
    exact Integrable.of_bound hb.aestronglyMeasurable M
      (Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hM x)
  obtain ⟨f,hf⟩ := exists_lipschitz_approximation μ hbi
  have hfi (j) := integrable_boundedLip μ (f j).property
  have hblim := borelAction_tendsto μ hC hμ hbi hfi hf π (fun i => ⟨K i,hK i⟩)
  have hwbi := integrable_weighted_comp (volume.restrict C.domain)
    C.measurable_paramExtended hw hb hB
  have hwfi (j) := integrable_weighted_comp (volume.restrict C.domain)
    C.measurable_paramExtended hw (f j).val.continuous.measurable (f j).property.2
  have hilim : Tendsto (fun j => ∫ z, w z*(f j).val (C.paramExtended z)
      ∂volume.restrict C.domain) atTop
      (𝓝 (∫ z, w z*b (C.paramExtended z) ∂volume.restrict C.domain)) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    apply squeeze_zero (fun _ => dist_nonneg) (fun j => ?_)
      (by simpa only [mul_zero] using hf.const_mul (∏ i, (K i : ℝ)))
    rw [Real.dist_eq,←integral_sub (hwfi j) hwbi]
    have hsub : (fun z => w z*(f j).val (C.paramExtended z)-w z*b (C.paramExtended z)) =
        (fun z => w z*((f j).val (C.paramExtended z)-b (C.paramExtended z))) := by
      ext z; ring
    rw [hsub]
    have hbnd : ∃ M : ℝ, ∀ x, |(f j).val x-b x| ≤ M := by
      obtain ⟨M,hM⟩ := (f j).property.2
      obtain ⟨N,hN⟩ := hB
      exact ⟨M+N,fun x => (abs_sub _ _).trans (add_le_add (hM x) (hN x))⟩
    have hh := signed_chart_control_borel (volume.restrict C.domain) ((∏ i,K i) • μ)
      C.measurable_paramExtended hw hcontrol
      ((f j).val.continuous.measurable.sub hb) hbnd
    rw [integral_smul_nnreal_measure] at hh
    simpa only [NNReal.smul_def,NNReal.coe_prod,smul_eq_mul,Pi.sub_apply] using hh
  have hseq : (fun j => borelAction μ hC (f j).val π) =
      (fun j => ∫ z, w z*(f j).val (C.paramExtended z) ∂volume.restrict C.domain) := by
    ext j
    rw [borelAction_eq μ hC hμ ⟨(f j).property,fun i => ⟨K i,hK i⟩⟩,heq]
    exact (f j).property
  rw [hseq] at hblim
  exact tendsto_nhds_unique hblim hilim

end IntegerChart
end CAT0Fillings

namespace CAT0Fillings
attribute [local instance] Classical.propDecidable
namespace IntegerChart
open BorelCoefficients BorelRestriction MassMeasure

variable {X : Type*} [MetricSpace X] [CompactSpace X]
variable [MeasurableSpace X] [BorelSpace X] [Nonempty X]
variable {k : ℕ} (C : IntegerChart X k)

noncomputable def restrictMultiplicity (E : Set X) (hE : MeasurableSet E) : IntegerChart X k :=
  { C with
    multiplicity := (C.paramExtended ⁻¹' E).indicator C.multiplicity
    integrable := by
      have heq : (fun z => (↑((C.paramExtended ⁻¹' E).indicator C.multiplicity z) : ℝ)) =
          (C.paramExtended ⁻¹' E).indicator (fun z => (C.multiplicity z : ℝ)) := by
        funext z
        by_cases hz : C.paramExtended z ∈ E <;> simp [hz]
      rw [heq]
      exact C.integrable.indicator (hE.preimage C.measurable_paramExtended) }

lemma restrictMultiplicity_action (hC : IsMetricCurrent C.action)
    {E : Set X} (hE : MeasurableSet E) :
    (C.restrictMultiplicity E hE).action = restrictCurrent hC E := by
  funext b π
  by_cases hadm : Admissible b π
  · rw [restrictCurrent_apply hC E hadm,
      C.borelAction_eq_integral hC (currentMassMeasure_controls hC)
        (hadm.1.continuous.measurable.indicator hE) ?_ π hadm.2]
    · rw [action,ite_eq_left hadm]
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem C.borel] with z hz
      change (↑((C.paramExtended ⁻¹' E).indicator C.multiplicity z) : ℝ) * C.scalar b z *
        C.jacobian π z = (C.multiplicity z : ℝ)*C.jacobian π z*E.indicator b (C.paramExtended z)
      have hz' : z ∈ C.domain := hz
      have hs : C.scalar b z = b (C.paramExtended z) := by
        simp only [scalar,paramExtended,dite_eq_left hz']
      rw [hs]
      by_cases he : C.paramExtended z ∈ E <;> simp [he,mul_comm,mul_left_comm]
    · obtain ⟨M,hM⟩ := hadm.1.2
      refine ⟨max M 0,fun x => ?_⟩
      by_cases hx : x ∈ E
      · simpa only [indicator_of_mem hx] using (hM x).trans (le_max_left M 0)
      · simp only [indicator_of_notMem hx,abs_zero,le_max_iff,le_refl,or_true]
  · rw [action,ite_eq_right hadm]
    exact (restrictCurrent_isMetricCurrent hC hE).offDomain b π hadm |>.symm

lemma restrictMultiplicity_isMetricCurrent (hC : IsMetricCurrent C.action)
    {E : Set X} (hE : MeasurableSet E) :
    IsMetricCurrent (C.restrictMultiplicity E hE).action := by
  rw [C.restrictMultiplicity_action hC hE]
  exact restrictCurrent_isMetricCurrent hC hE

lemma restrictMultiplicity_mass_le (hC : IsMetricCurrent C.action)
    {E : Set X} (hE : MeasurableSet E) :
    mass (C.restrictMultiplicity E hE).action ≤ mass C.action := by
  rw [C.restrictMultiplicity_action hC hE,restriction_mass hC hE,
    ←currentMassMeasure_total hC]
  exact measureReal_mono (subset_univ E)

end IntegerChart
end CAT0Fillings

end

end OAI
