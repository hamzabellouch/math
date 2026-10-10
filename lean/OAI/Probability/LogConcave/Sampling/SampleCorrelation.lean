import Mathlib
import OAI.Probability.LogConcave.Sampling.Correlation
import OAI.Probability.LogConcave.Numerics.Forward
import OAI.Probability.LogConcave.Analysis.GaussianPairSumLaw
import OAI.Probability.LogConcave.Complexity.EventuallySequences

namespace OAI

section
noncomputable section
namespace LogConcaveSampling
open Filter MeasureTheory ProbabilityTheory
open scoped Classical NNReal

lemma samplingEnvelope_rate (k n N : ℕ) (C : ℝ) {q : ℕ → ℝ} {κ J b w : ℝ}
    (hκ : 0<κ) (hJ : 1≤J) (hb : 1/2≤b) (hw : 0<w)
    (hn : J+10<w*((n:ℝ)-3)) (hN : 10*(J+2)≤(N:ℝ))
    (hq : LogPowerRate q (κ*b)) :
    LogPowerRate (fun d => samplingEnvelope d k n N C (q d) ((d:ℝ)^(-(κ*w)))) (2*κ*(J+9)) := by
  have hn' : κ*(J+9)≤(n+1:ℕ)*(κ*w) := by
    push_cast
    nlinarith
  have hNb : (N:ℝ)/2≤N*b := by nlinarith [mul_nonneg (Nat.cast_nonneg (α:=ℝ) N) (sub_nonneg.mpr hb)]
  have hN' : κ*(J+9)≤N*(κ*b) := by nlinarith
  have hp := (((LogPowerRate.log.pow k).const_mul (2*C)).mul
    (((LogPowerRate.power (κ*w)).const_mul 2).pow (n+1)))
  have hp' : LogPowerRate (fun d => 2*C*dimensionLog d^k*(2*(d:ℝ)^(-(κ*w)))^(n+1)) (κ*(J+9)) := by
    have hp₀ : LogPowerRate (fun d => 2*C*dimensionLog d^k*(2*(d:ℝ)^(-(κ*w)))^(n+1)) ((n+1:ℕ)*(κ*w)) := by
      simpa only [mul_zero,zero_add] using hp
    exact hp₀.mono hn'
  have hq' := ((hq.pow N).const_mul circuitGrowthConstant).mono hN'
  have he := ((hp'.add hq').pow 2).const_mul 4
  convert he using 1 <;> first | rfl | (norm_num; ring)

theorem sampleScalarCalibration_uniform (k n N ksize : ℕ) (A : ℝ≥0) (C : ℝ)
    {S κ J b w : ℝ} (hS : 0≤S) (hκ : 0<κ) (hJ : 1≤J) (hb : 1/2≤b) (hw : 0<w)
    (hn : J+10<w*((n:ℝ)-3)) (hN : 10*(J+2)≤(N:ℝ)) :
    ∀ᶠ d : ℕ in atTop,∀lam : ℝ≥0,∀r : ℝ,0<r →
      (lam:ℝ)*r^2≤S*dimensionLog d^ksize*(d:ℝ)^(-(κ*b)) →
      (lam:ℝ)*r^2≤1/2 ∧ A*probabilityMeanLipschitz lam r≤1/2 ∧
      samplingEnvelope d k n N C (A*probabilityMeanLipschitz lam r) ((d:ℝ)^(-(κ*w)))≤
        (d:ℝ)^(-(2*κ*J)) := by
  have hseq : ∀ᶠ d : ℕ in atTop,∀v : ℝ≥0 × ℝ,
      (0<v.2 ∧ (v.1:ℝ)*v.2^2≤S*dimensionLog d^ksize*(d:ℝ)^(-(κ*b))) →
      (v.1:ℝ)*v.2^2≤1/2 ∧ A*probabilityMeanLipschitz v.1 v.2≤1/2 ∧
      samplingEnvelope d k n N C (A*probabilityMeanLipschitz v.1 v.2) ((d:ℝ)^(-(κ*w)))≤
        (d:ℝ)^(-(2*κ*J)) := by
    apply eventually_forall_of_sequences
    · exact Eventually.of_forall (fun d => ⟨(0,1),by
        refine ⟨by norm_num,?_⟩
        simp only [NNReal.coe_zero,zero_mul]
        positivity [dimensionLog_nonneg d]⟩)
    · intro f hf
      have hl : LogPowerRate (fun d => ((f d).1:ℝ)*(f d).2^2) (κ*b) :=
        logPowerRate_of_envelope (Eventually.of_forall (fun d => by positivity)) (hf.mono (fun _ h => h.2))
      have hq := probabilityMeanLipschitz_rate hl A
      have he := (samplingEnvelope_rate k n N C hκ hJ hb hw hn hN hq).eventually_small
        (show 2*κ*J<2*κ*(J+9) by nlinarith)
      have hkb : 0<κ*b := mul_pos hκ (by linarith)
      have hl' := hl.eventually_lt_const hkb (by norm_num : (0:ℝ)<1/2)
      have hq' := hq.eventually_lt_const hkb (by norm_num : (0:ℝ)<1/2)
      filter_upwards [he,hl',hq'] with d hd hld hqd
      refine ⟨(le_abs_self _).trans hld.le,?_,(le_abs_self _).trans hd⟩
      exact_mod_cast (le_abs_self _).trans hqd.le
  filter_upwards [hseq] with d hd lam r hr hl
  exact hd (lam,r) ⟨hr,hl⟩

theorem exists_calibrated_sample_circuit {κ J b t : ℝ} (hκ : 0<κ) (hJ : 1≤J)
    (hb : 1/2≤b) (ht : 0<t) :
    ∀{w : ℝ},0<w → ∃n : ℕ,0<n ∧ J+10<w*((n:ℝ)-3) ∧
      ∀{S : ℝ},0≤S → ∀ksize : ℕ,∀ᶠ d : ℕ in atTop,
      let h := (d:ℝ)^(-(κ*w))
      ∃_ : 0<h,∀{F : Point d → ℝ} {lam : ℝ≥0},∀hF : Primitive F lam,∀x : Point d,
      ∀{r : ℝ},∀hr : 0<r,r≤1 → 0<lam → (lam:ℝ)*r≤1 →
      (lam:ℝ)*r^2≤S*dimensionLog d^ksize*(d:ℝ)^(-(κ*b)) →
      ∃hl : (lam:ℝ)*r^2≤1/2,∀{T : ℝ},1/2≤T → T<1 → ∀e : ProbabilityNode T h n,
      Integrable (fun z => ‖sampleMeanCircuit F x r T h n (numericalLayerCount J) e z-
        T⁻¹ • fullProbabilityFlow hF x hr.le hl (probabilityNodeTime T h n e) z‖^2)
        (stdGaussian (Point d)) ∧
      (∫z,‖sampleMeanCircuit F x r T h n (numericalLayerCount J) e z-
        T⁻¹ • fullProbabilityFlow hF x hr.le hl (probabilityNodeTime T h n e) z‖^2 ∂stdGaussian (Point d))≤
        (circuitD F x)^2*(d:ℝ)^(-(2*κ*J)) := by
  intro w hw
  obtain ⟨n,hnw,hnt,hnn⟩ := exists_numerical_order (J:=J) ht hw
  have hn : 0<n := by
    have hn' : (0:ℝ)<n := by linarith
    exact_mod_cast hn'
  obtain ⟨A,C,hC,k,hproducer⟩ := sampleMeanCircuit_rms n hn
  refine ⟨n,hn,hnw,?_⟩
  intro S hS ksize
  have hc := sampleScalarCalibration_uniform k n (numericalLayerCount J) ksize A C hS hκ hJ hb hw hnw
    (numericalLayerCount_bound J)
  have hhsmall := (LogPowerRate.power (κ*w)).eventually_lt_const (mul_pos hκ hw)
    (Real.log_pos (by norm_num : (1:ℝ)<2))
  filter_upwards [hc,hhsmall,eventually_ge_atTop (1:ℕ)] with d hd hdh hdim
  intro h
  have hdpos : (0:ℝ)<d := by exact_mod_cast hdim
  have hh : 0<h := Real.rpow_pos_of_pos hdpos _
  refine ⟨hh,?_⟩
  intro F lam hF x r hr hr1 hlam hL hl₀
  obtain ⟨hl,hq,he⟩ := hd lam r hr hl₀
  refine ⟨hl,?_⟩
  intro T hT hT1 e
  have hp := hproducer hF x hr hr1 hlam hl hL hdim hT hT1 hh
    ((le_abs_self _).trans hdh.le) hq (numericalLayerCount J) e
  exact ⟨hp.1,hp.2.trans (mul_le_mul_of_nonneg_left he (sq_nonneg _))⟩
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open MeasureTheory ProbabilityTheory Function
open scoped Classical NNReal

variable {d : ℕ}

lemma probability_endpoint_divided_law {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r T a : ℝ} (hr : 0≤r)
    (hl : (lam:ℝ)*r^2≤1/2) (hT : 0<T) (hT1 : T<1)
    (ha : T⁻¹*Real.sqrt (1-T^2)=a) :
    (stdGaussian (Point d)).map (fun z => T⁻¹ • fullProbabilityFlow hF x hr hl T z)=
      ((gibbs (primitivePotential F x r)).prod (stdGaussian (Point d))).map
        (fun z => z.1+a • z.2) := by
  have hf := (fullProbabilityFlow_lipschitz hF x hr hl ⟨hT.le,hT1.le⟩).continuous.measurable
  have hp := congrArg (Measure.map (fun z : Point d => T⁻¹ • z))
    (fullProbabilityFlow_interpolation hF x hr hl hT hT1)
  rw [Measure.map_map (by fun_prop) hf] at hp
  unfold interpolationLaw at hp
  rw [Measure.map_map (by fun_prop) (by fun_prop)] at hp
  simpa only [comp_def,smul_add,smul_smul,inv_mul_cancel₀ hT.ne',one_smul,ha] using hp

lemma probability_endpoint_noisy_law {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r T a b s : ℝ} (hr : 0≤r)
    (hl : (lam:ℝ)*r^2≤1/2) (hT : 0<T) (hT1 : T<1)
    (ha : T⁻¹*Real.sqrt (1-T^2)=a) (hs : a^2+b^2=s^2) :
    ((stdGaussian (Point d)).prod (stdGaussian (Point d))).map
      (fun z => T⁻¹ • fullProbabilityFlow hF x hr hl T z.1+b • z.2)=
      ((gibbs (primitivePotential F x r)).prod (stdGaussian (Point d))).map
        (fun z => z.1+s • z.2) := by
  let := probability_gibbs_of_partition
    (partition_pos_of_continuous (hF.continuous_potential x r)).ne'
    (partition_ne_top_of_integrable (hF.integrable_exp_neg_potential x hr (by linarith)))
  have hf := (fullProbabilityFlow_lipschitz hF x hr hl ⟨hT.le,hT1.le⟩).continuous.measurable
  exact smoothing_add_gaussian (stdGaussian (Point d)) (gibbs (primitivePotential F x r))
    (fun z => T⁻¹ • fullProbabilityFlow hF x hr hl T z) id (by fun_prop) measurable_id a b s hs
    (probability_endpoint_divided_law hF x hr hl hT hT1 ha)

def sampleCorrelation (η : ℝ) : ℝ := (Real.sqrt (1+η^2/4))⁻¹

lemma sampleCorrelation_properties {η : ℝ} (hη : 0<η) (hη1 : η≤1) :
    1/2 ≤ sampleCorrelation η ∧ sampleCorrelation η<1 ∧
      (sampleCorrelation η)⁻¹*Real.sqrt (1-(sampleCorrelation η)^2)=η/2 := by
  let q := Real.sqrt (1+η^2/4)
  have hq : 0<q := Real.sqrt_pos.mpr (by positivity)
  have hq2 : q^2=1+η^2/4 := Real.sq_sqrt (by positivity)
  have hq1 : 1<q := by nlinarith [sq_pos_of_pos hη]
  have hqle : q≤2 := by nlinarith [sq_nonneg (η-1)]
  have ht : sampleCorrelation η=q⁻¹ := rfl
  rw [ht]
  refine ⟨(le_inv_comm₀ (by norm_num) hq).mpr (by simpa using hqle),
    (inv_lt_one₀ hq).mpr hq1,?_⟩
  rw [inv_inv]
  have hinside : 0≤1-(q⁻¹)^2 := by
    have hu : q⁻¹≤1 := (inv_le_one₀ hq).mpr hq1.le
    nlinarith [inv_nonneg.mpr hq.le]
  have hc : (q*Real.sqrt (1-(q⁻¹)^2))^2=(η/2)^2 := by
    rw [mul_pow,Real.sq_sqrt hinside]
    field_simp
    nlinarith [hq2]
  nlinarith [mul_nonneg hq.le (Real.sqrt_nonneg (1-(q⁻¹)^2))]

lemma sample_noise_variance (η : ℝ) :
    (η/2)^2+(η/Real.sqrt 2)^2=(Real.sqrt 3*η/2)^2 := by
  have h2 := Real.sq_sqrt (by norm_num : (0:ℝ)≤2)
  have h3 := Real.sq_sqrt (by norm_num : (0:ℝ)≤3)
  rw [div_pow,div_pow,div_pow,mul_pow,h2,h3]
  ring
end LogConcaveSampling

end

end

end OAI
