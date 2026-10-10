import OAI.Dynamics.StandardMap.BandGeometry

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter MeasureTheory Topology
open scoped ENNReal Classical
namespace StandardMapEntropy
noncomputable def bandCap (α:ℝ) (t:DyadicTime) (d:NonAffineArray) : ℝ := entropyCap α (arrayShortfall 0 t d.val)
lemma measurable_bandCap (α:ℝ) (t:DyadicTime) : Measurable (bandCap α t) :=
  ((entropyCap_contDiff α).continuous.comp ((continuous_arrayShortfall 0 t).comp continuous_subtype_val)).measurable
lemma bandCap_nonneg {μ:Measure NonAffineArray} {α:ℝ} (ha:0≤α) (ha1:α≤1) (t:DyadicTime) (ht:0<(t:ℝ)) :
    0≤ᵐ[bandLaw μ] bandCap α t := by
  filter_upwards [ae_restrict_mem (measurableSet_lengthBand 0)] with d hd
  exact (entropyCap_bounds ha ha1 (shortfall_unit_mem d.val hd.1 0 t (by simpa only [ZeroMemClass.coe_zero]))).1
lemma bandCap_integrable (μ:Measure NonAffineArray) [IsFiniteMeasureOnCompacts μ]
    (hs:∀ᵐd ∂μ,SlowShape (realArray d.val) (999/1000))
    (hT:∀r:DyadicTime,μ.map (nonaffineTranslation r)=μ) {α:ℝ} (ha:0≤α) (ha1:α≤1)
    (t:DyadicTime) (ht:0<(t:ℝ)) : Integrable (bandCap α t) (bandLaw μ) := by
  let E:Set NonAffineArray := {d | endpointLeft d.val∈Icc (-2) (t:ℝ)}
  have hE : MeasurableSet E := (measurable_endpointLeft.comp measurable_subtype_coe) measurableSet_Icc
  have hf : bandLaw μ E<∞ := bandLaw_endpoint_finite μ hs hT _ _
  have : IsFiniteMeasure ((bandLaw μ).restrict E) := ⟨by simpa only [Measure.restrict_apply_univ] using hf⟩
  have hi : Integrable (E.indicator (fun _ => (1:ℝ))) (bandLaw μ) := IntegrableOn.integrable_indicator (integrable_const (μ:=(bandLaw μ).restrict E) (1:ℝ)) hE
  apply hi.mono' (measurable_bandCap α t).aestronglyMeasurable
  filter_upwards [ae_restrict_mem (measurableSet_lengthBand 0),ae_restrict_of_ae hs] with d hd hsd
  rw [Real.norm_eq_abs,bandCap,abs_of_nonneg ((entropyCap_bounds ha ha1 (shortfall_unit_mem d.val hd.1 0 t (by simpa only [ZeroMemClass.coe_zero]))).1)]
  by_cases he:d∈E
  · rw [indicator_of_mem he]; exact (entropyCap_bounds ha ha1 (shortfall_unit_mem d.val hd.1 0 t (by simpa only [ZeroMemClass.coe_zero]))).2
  · rw [indicator_of_notMem he]
    exact le_of_eq (band_cap_support α d hd hsd t ht he)
lemma bandCap_one_fine {α:ℝ} (d:NonAffineArray) (hd:d∈lengthBand 0)
    (hs:SlowShape (realArray d.val) (999/1000)) (he:endpointLeft d.val∈Ico (-1/2) 0)
    (t:DyadicTime) (ht:0<(t:ℝ)) (ht1:(t:ℝ)≤1/2) : bandCap α t d=1 := by
  obtain ⟨hab,hl,hr,hslow⟩ := twoRay_properties hd.1 (by norm_num) hs hd.2.1
  have hlen : 1≤endpointRight d.val-endpointLeft d.val := by simpa only [lengthBand,zpow_zero,coreLength] using hd.2.2.1
  have hb := hslow 0 t (by change (0:ℝ)∈Icc (endpointLeft d.val) (endpointRight d.val); constructor <;> linarith [he.1,he.2])
    (by constructor <;> linarith [he.1,he.2])
  rw [ZeroMemClass.coe_zero,sub_zero,abs_of_pos ht] at hb
  have hr := (div_le_iff₀ ht).mpr hb
  apply entropyCap_one
  change 3/10000≤1-d.val.val 0 t/((t:ℝ)-(0:DyadicTime))
  rw [ZeroMemClass.coe_zero,sub_zero]
  linarith
end StandardMapEntropy

end OAI
