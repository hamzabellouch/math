import OAI.Dynamics.StandardMap.WeightBridge

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter
open scoped ENNReal Topology CompactlySupported Classical
namespace StandardMapEntropy
namespace CriticalScaleSequence
variable (S:CriticalScaleSequence) (L:S.LimitLaws)
lemma cap_dominated_integrable {α:ℝ} (f:DistanceArray→ℝ) (hf:Continuous f) (hb:∀d,|f d|≤|capG α d|) :
    Integrable (fun d:NonAffineArray => f d.val) L.multi :=
  (S.capG_integrable_multi L α).abs.mono' (hf.comp continuous_subtype_val).aestronglyMeasurable
    (Eventually.of_forall (fun d => by simpa only [Real.norm_eq_abs] using hb d.val))
lemma identify_weight {α:ℝ} (f:DistanceArray→ℝ) (hf:Continuous f) (h0:∀d,0≤f d)
    (hb:∀d,f d≤|capG α d|) (Q:CompactWeightLimit (L.filter:Filter ℕ) S.multiLaw f) :
    nonaffinePart Q.law=realWeight L.multi (fun d:NonAffineArray => f d.val) := by
  have:=Q.finite
  have hif:=S.cap_dominated_integrable L f hf (fun d => by simpa only [abs_of_nonneg (h0 d)] using hb d)
  have:=realWeight_finite L.multi (fun d:NonAffineArray => f d.val) hif
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro g
  let gf:C_c(NonAffineArray,ℝ):=⟨⟨fun d => g d*f d.val,g.continuous.mul (hf.comp continuous_subtype_val)⟩,g.hasCompactSupport.mul_right⟩
  have he:∀d:DistanceArray,arrayTestExtend gf d=arrayTestExtend g d*f d := by
    intro d
    by_cases hd:d∈affineLocus
    · rw [arrayTestExtend_affine gf d hd,arrayTestExtend_affine g d hd,zero_mul]
    · rw [arrayTestExtend_apply gf ⟨d,hd⟩,arrayTestExtend_apply g ⟨d,hd⟩]; rfl
  have hc:=Q.converges (arrayTestExtend g).toContinuousMap
  have hl:=L.multi_converges gf
  have heq (i:ℕ):(∫d,arrayTestExtend g d*f d ∂S.multiLaw i)=(∫d,gf d ∂nonaffinePart (S.multiLaw i)) := by
    simp_rw [←he]; exact integral_arrayTestExtend _ gf
  simp only [CompactlySupportedContinuousMap.coe_toContinuousMap] at hc
  simp_rw [heq] at hc
  rw [integral_arrayTestExtend] at hc
  have h:=tendsto_nhds_unique hc hl
  rw [integral_realWeight L.multi (fun d:NonAffineArray => f d.val) (hf.measurable.comp measurable_subtype_coe) (fun d => h0 d.val)]
  exact h
lemma weight_tendsto_integral {α:ℝ} (f:DistanceArray→ℝ) (hf:Continuous f) (h0:∀d,0≤f d)
    (hb:∀d,f d≤|capG α d|) (Q:CompactWeightLimit (L.filter:Filter ℕ) S.multiLaw f)
    (ha:Q.law affineLocus=0) :
    Tendsto (fun i => ∫d,f d ∂S.multiLaw i) (L.filter:Filter ℕ) (𝓝 (∫d:NonAffineArray,f d.val ∂L.multi)) := by
  have:=Q.finite
  have hc:=Q.converges (ContinuousMap.const DistanceArray (1:ℝ))
  simp only [ContinuousMap.const_apply,one_mul] at hc
  have he:(∫d:DistanceArray,(1:ℝ) ∂Q.law)=(∫d:NonAffineArray,(1:ℝ) ∂nonaffinePart Q.law) := by
    have he := integral_subtype_comap (μ:=Q.law) isClosed_affineLocus.isOpen_compl.measurableSet (fun _ : DistanceArray => (1:ℝ))
    change (∫d:NonAffineArray,(1:ℝ) ∂nonaffinePart Q.law)=_ at he
    rw [he]
    have hres:Q.law.restrict affineLocusᶜ=Q.law := by
      have hzero:Q.law.restrict affineLocus=0 := Measure.restrict_eq_zero.mpr ha
      have hh:=Q.law.restrict_compl_add_restrict isClosed_affineLocus.measurableSet
      rwa [hzero,add_zero] at hh
    rw [hres]
  rw [he,S.identify_weight L f hf h0 hb Q,integral_realWeight L.multi (fun d:NonAffineArray => f d.val) (hf.measurable.comp measurable_subtype_coe) (fun d => h0 d.val)] at hc
  simpa only [one_mul] using hc
end CriticalScaleSequence
end StandardMapEntropy

end OAI
