import OAI.Dynamics.StandardMap.WeightSlow

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter
open scoped ENNReal Topology CompactlySupported Classical
namespace StandardMapEntropy
noncomputable def unitCapOpen (b:ℕ) : Set DistanceArray := {d | unitDefect d<1/(2:ℝ)^b}
lemma isOpen_unitCapOpen (b:ℕ) : IsOpen (unitCapOpen b) :=
  isOpen_lt continuous_unitDefect continuous_const
noncomputable def unitAffine : DistanceArray := affineArray ⟨1,by norm_num⟩
lemma unitAffine_mem_unitCapOpen (b:ℕ) : unitAffine∈unitCapOpen b := by
  change unitDefect (affineArray _) < _
  simp only [unitDefect,arrayJ,dyadicMid_zero_two]
  rw [affine_shortfall _ _ _ (by norm_num),affine_shortfall _ _ _ (by norm_num),affine_shortfall _ _ _ (by norm_num)]
  norm_num
namespace CriticalScaleSequence
variable (S:CriticalScaleSequence) (L:S.LimitLaws)
lemma weight_unit_integral_bound {α:ℝ} (hα:0≤α) (f:DistanceArray→ℝ) (hf:Continuous f)
    (h0:∀d,0≤f d) (hb:∀d,f d≤|capG α d|) (Q:CompactWeightLimit (L.filter:Filter ℕ) S.multiLaw f)
    (b:ℕ) (hsmall:1/(2:ℝ)^b≤1/10000) (g:C_c(DistanceArray,ℝ))
    (_hg:∀d,0≤g d) (hg1:∀d,g d≤1) (hz:∀d∉unitCapOpen b,g d=0) :
    (∫d,g d ∂Q.law)≤9*α/(2:ℝ)^b := by
  let F:DistanceArray→ℝ:=fun d=>g d*f d
  have hFB:∀d,F d≤|capG α d| := fun d => (mul_le_of_le_one_left (h0 d) (hg1 d)).trans (hb d)
  have hFz:∀d,¬unitDefect d<1/(2:ℝ)^b → F d=0 := by
    intro d hd; dsimp only [F]; rw [hz d hd,zero_mul]
  have hu:∀ᶠi in atTop,(∫d,F d ∂S.multiLaw i)≤α*((1/(2:ℝ)^b)*9+6*criticalTheta S.offset i) := by
    filter_upwards [S.lowerExponent_tendsto.eventually_ge_atTop b] with i hi
    have h:=weight_unit_scale_bound (S.parameter i) (S.positive i).le
      (criticalLowerExponent S.offset i) b (S.exponent i-criticalLowerExponent S.offset i) hi
      (S.epsilon i) (S.epsilon_pos i) hα hsmall F (g.continuous.mul hf) hFB hFz
    apply h.trans
    have hm:meanDeficit (S.parameter i) (2^(criticalLowerExponent S.offset i-b+(S.exponent i-criticalLowerExponent S.offset i)))≤S.epsilon i := by
      exact meanDeficit_pow_mono _ (S.positive i).le (by have := S.lower_lt i; omega)
    have hr:9*meanDeficit (S.parameter i) (2^(criticalLowerExponent S.offset i-b+(S.exponent i-criticalLowerExponent S.offset i)))/S.epsilon i≤9 := by
      apply (div_le_iff₀ (S.epsilon_pos i)).mpr; linarith
    have hE:=mul_le_mul_of_nonneg_left (S.inverse_scale_epsilon_bound i _ le_rfl) (by norm_num : (0:ℝ)≤6)
    apply mul_le_mul_of_nonneg_left _ hα
    apply add_le_add (mul_le_mul_of_nonneg_left hr (by positivity))
    convert hE using 1 ; ring
  have ht:Tendsto (fun i => α*((1/(2:ℝ)^b)*9+6*criticalTheta S.offset i)) (L.filter:Filter ℕ) (𝓝 (9*α/(2:ℝ)^b)) := by
    convert! (((criticalTheta_tendsto S.offset).const_mul 6).const_add ((1/(2:ℝ)^b)*9)).const_mul α |>.mono_left L.refines using 1 ; ring_nf
  exact le_of_tendsto_of_tendsto (Q.converges g.toContinuousMap) ht (hu.filter_mono L.refines)
lemma weight_unit_open_bound {α:ℝ} (hα:0≤α) (f:DistanceArray→ℝ) (hf:Continuous f)
    (h0:∀d,0≤f d) (hb:∀d,f d≤|capG α d|) (Q:CompactWeightLimit (L.filter:Filter ℕ) S.multiLaw f)
    (b:ℕ) (hsmall:1/(2:ℝ)^b≤1/10000) : Q.law (unitCapOpen b)≤ENNReal.ofReal (9*α/(2:ℝ)^b) := by
  have:=Q.regular
  have:=Q.finite
  apply open_measure_le_of_integral_bound Q.law (isOpen_unitCapOpen b) _
  exact S.weight_unit_integral_bound L hα f hf h0 hb Q b hsmall
lemma weight_unit_null {α:ℝ} (hα:0≤α) (f:DistanceArray→ℝ) (hf:Continuous f)
    (h0:∀d,0≤f d) (hb:∀d,f d≤|capG α d|) (Q:CompactWeightLimit (L.filter:Filter ℕ) S.multiLaw f) :
    Q.law {unitAffine}=0 := by
  have ht:Tendsto (fun b:ℕ => 1/(2:ℝ)^b) atTop (𝓝 0) := by
    simpa only [div_pow,one_pow] using tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ)≤1/2) (by norm_num : (1/2:ℝ)<1)
  have hh:∀ᶠb:ℕ in atTop,Q.law {unitAffine}≤ENNReal.ofReal (9*α/(2:ℝ)^b) := by
    filter_upwards [ht.eventually_le_const (by norm_num : (0:ℝ)<1/10000)] with b hb'
    exact (measure_mono (singleton_subset_iff.mpr (unitAffine_mem_unitCapOpen b))).trans (S.weight_unit_open_bound L hα f hf h0 hb Q b hb')
  have he:Tendsto (fun b:ℕ => ENNReal.ofReal (9*α/(2:ℝ)^b)) atTop (𝓝 0) := by
    have h:=ENNReal.continuous_ofReal.continuousAt.tendsto.comp (ht.const_mul (9*α))
    convert! h using 1 <;> simp [div_eq_mul_inv,Function.comp_def]
  exact le_antisymm (le_of_tendsto_of_tendsto tendsto_const_nhds he hh) bot_le
end CriticalScaleSequence
end StandardMapEntropy

end OAI
