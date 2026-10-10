import Mathlib
import OAI.Probability.Perceptron.Variational.QuadraticContactRemainders
import OAI.Probability.Perceptron.Variational.IntegrableGibbs

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators

lemma nonnegative_limit_integral_bound {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {F : ℕ → Ω → ℝ} {f : Ω → ℝ} {C : ℝ} (hm : AEStronglyMeasurable f P)
    (hF : ∀ n, Integrable (F n) P) (hF0 : ∀ n, 0 ≤ᵐ[P] F n) (hf0 : 0 ≤ᵐ[P] f)
    (ht : ∀ᵐ ω ∂P, Tendsto (fun n => F n ω) atTop (nhds (f ω)))
    (hb : ∀ᶠ n in atTop, (∫ ω, F n ω ∂P) ≤ C) :
    Integrable f P ∧ (∫ ω, f ω ∂P) ≤ C := by
  have hle : (∫⁻ ω, ENNReal.ofReal (f ω) ∂P) ≤ ENNReal.ofReal C := by
    calc
      _ = ∫⁻ ω, liminf (fun n => ENNReal.ofReal (F n ω)) atTop ∂P := by
        apply lintegral_congr_ae
        filter_upwards [ht] with ω hω
        exact (ENNReal.continuous_ofReal.continuousAt.tendsto.comp hω).liminf_eq.symm
      _ ≤ liminf (fun n => ∫⁻ ω, ENNReal.ofReal (F n ω) ∂P) atTop :=
        lintegral_liminf_le' (fun n => (hF n).aestronglyMeasurable.aemeasurable.ennreal_ofReal)
      _ ≤ ENNReal.ofReal C := by
        apply liminf_le_of_frequently_le'
        apply Eventually.frequently
        filter_upwards [hb] with n hn
        rw [← ofReal_integral_eq_lintegral_ofReal (hF n) (hF0 n)]
        exact ENNReal.ofReal_le_ofReal hn
  have hi : Integrable f P := ⟨hm,(hasFiniteIntegral_iff_ofReal hf0).mpr (hle.trans_lt ENNReal.ofReal_lt_top)⟩
  refine ⟨hi,?_⟩
  have hC : 0 ≤ C := by
    obtain ⟨n,hn⟩ := hb.exists
    exact (integral_nonneg_of_ae (hF0 n)).trans hn
  rw [← ofReal_integral_eq_lintegral_ofReal hi hf0] at hle
  exact (ENNReal.ofReal_le_ofReal_iff hC).mp hle

lemma taylor_two_explicit (F : ℝ → ℝ) (u v : ℝ) :
    taylorWithinEval F 2 univ u v = F u+(v-u)*deriv F u+(v-u)^2/2*iteratedDeriv 2 F u := by
  rw [taylorWithinEval_succ F 1,taylorWithinEval_succ F 0,taylor_within_zero_eval]
  simp only [iteratedDerivWithin_univ,iteratedDeriv_one,Nat.cast_zero,Nat.factorial_zero,
    Nat.cast_one,zero_add,one_mul,inv_one,pow_one,smul_eq_mul,Nat.factorial_one]
  ring

lemma second_symmetric_quotient_tendsto {F : ℝ → ℝ} (hc : ContDiff ℝ 2 F) (u : ℝ)
    {s : ℕ → ℝ} (hs : ∀ n, s n ≠ 0) (hst : Tendsto s atTop (nhds 0)) :
    Tendsto (fun n => (F (u+s n)+F (u-s n)-2*F u)/(s n)^2)
      atTop (nhds (iteratedDeriv 2 F u)) := by
  have he := (taylor_isLittleO_univ (x₀ := u) hc).tendsto_div_nhds_zero
  have hup : Tendsto (fun n => u+s n) atTop (nhds u) := by simpa using tendsto_const_nhds.add hst
  have hum : Tendsto (fun n => u-s n) atTop (nhds u) := by simpa using tendsto_const_nhds.sub hst
  have hp := he.comp hup
  have hm := he.comp hum
  have hp' : Tendsto (fun n =>
      (F (u+s n)-(F u+s n*deriv F u+(s n)^2/2*iteratedDeriv 2 F u))/(s n)^2)
      atTop (nhds (0:ℝ)) := by
    simpa only [Function.comp_def,taylor_two_explicit,add_sub_cancel_left,add_zero] using hp
  have hm' : Tendsto (fun n =>
      (F (u-s n)-(F u-s n*deriv F u+(s n)^2/2*iteratedDeriv 2 F u))/(s n)^2)
      atTop (nhds (0:ℝ)) := by
    convert hm using 1
    funext n
    simp only [Function.comp_def,taylor_two_explicit,sub_sub_cancel_left,neg_sq,neg_mul]
    ring
  have h := (hp'.add hm').add_const (iteratedDeriv 2 F u)
  simp only [zero_add] at h
  apply h.congr
  intro n
  field_simp [hs n]
  ring

lemma convex_symmetric_quotient_nonneg {F : ℝ → ℝ} (hc : ConvexOn ℝ univ F) (u s : ℝ) :
    0 ≤ (F (u+s)+F (u-s)-2*F u)/s^2 := by
  have hh := hc.2 (mem_univ (u+s)) (mem_univ (u-s))
    (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1:ℝ)/2+1/2=1)
  simp only [smul_eq_mul] at hh
  have he : (1:ℝ)/2*(u+s)+1/2*(u-s)=u := by ring
  rw [he] at hh
  exact div_nonneg (by linarith) (sq_nonneg _)

lemma quadratic_contact_curvature_bound {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {F : ℝ → Ω → ℝ} {J : Ω → ℝ} (hJ : AEStronglyMeasurable J P)
    (hi : ∀ t, Integrable (F t) P)
    (hc : ∀ᵐ ω ∂P, ContDiff ℝ 2 (fun t => F t ω) ∧ ConvexOn ℝ univ (fun t => F t ω))
    {u a c : ℝ} (he : ∀ᵐ ω ∂P, iteratedDeriv 2 (fun t => F t ω) u = J ω)
    (hmin : IsLocalMin (fun t => c*(t-a)^2-∫ ω, F t ω ∂P) u) :
    Integrable J P ∧ (∫ ω, J ω ∂P) ≤ 2*c := by
  let s : ℕ → ℝ := fun n => 1/(n+1:ℝ)
  have hs (n) : 0 < s n := by dsimp [s]; positivity
  have hst : Tendsto s atTop (nhds 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let Q : ℕ → Ω → ℝ := fun n ω => (F (u+s n) ω+F (u-s n) ω-2*F u ω)/(s n)^2
  have hQi (n) : Integrable (Q n) P :=
    (((hi (u+s n)).add (hi (u-s n))).sub ((hi u).const_mul 2)).div_const _
  have hQ0 (n) : 0 ≤ᵐ[P] Q n := hc.mono fun ω hω => convex_symmetric_quotient_nonneg hω.2 u (s n)
  have hQt : ∀ᵐ ω ∂P, Tendsto (fun n => Q n ω) atTop (nhds (J ω)) := by
    filter_upwards [hc,he] with ω hω heω
    rw [← heω]
    exact second_symmetric_quotient_tendsto hω.1 u (fun n => (hs n).ne') hst
  have hJ0 : 0 ≤ᵐ[P] J := by
    filter_upwards [hQt,ae_all_iff.mpr hQ0] with ω hω h0
    exact ge_of_tendsto hω (Eventually.of_forall h0)
  apply nonnegative_limit_integral_bound P hJ hQi hQ0 hJ0 hQt
  have hup : Tendsto (fun n => u+s n) atTop (nhds u) := by simpa using tendsto_const_nhds.add hst
  have hum : Tendsto (fun n => u-s n) atTop (nhds u) := by simpa using tendsto_const_nhds.sub hst
  have hp := hup.eventually hmin
  have hm := hum.eventually hmin
  filter_upwards [hp,hm] with n hpn hmn
  have hsum : Integrable (fun ω => F (u+s n) ω+F (u-s n) ω) P := (hi _).add (hi _)
  have hmul : Integrable (fun ω => 2*F u ω) P := (hi u).const_mul 2
  rw [integral_div,integral_sub hsum hmul,integral_add (hi (u+s n)) (hi (u-s n)),integral_const_mul]
  apply (div_le_iff₀ (sq_pos_of_pos (hs n))).mpr
  nlinarith

variable {S : Type*} [MeasurableSpace S] (μ : Measure S)

lemma coupling_weighted_power_integrable {H Y : S → ℝ} (hH : Measurable H) (hY : Measurable Y)
    (he : ∀ a : ℝ, Integrable (fun x => Real.exp (H x+a*Y x)) μ) (a : ℝ) (k : ℕ) :
    Integrable (fun x => Real.exp (H x+a*Y x)*(Y x)^k) μ := by
  have hi := ((he (a+1)).add (he (a-1))).const_mul (k.factorial:ℝ)
  apply hi.mono' (((hH.add (hY.const_mul a)).exp).mul (hY.pow_const k)).aestronglyMeasurable
  filter_upwards [] with x
  change ‖Real.exp (H x+a*Y x)*(Y x)^k‖ ≤ (k.factorial:ℝ)*(Real.exp (H x+(a+1)*Y x)+Real.exp (H x+(a-1)*Y x))
  rw [Real.norm_eq_abs,abs_mul,abs_of_pos (Real.exp_pos _),abs_pow,mul_comm]
  convert abs_pow_mul_exp_le (H x+a*Y x) (Y x) k using 1
  congr 2 <;> ring_nf

variable [IsProbabilityMeasure μ]

lemma coupling_tilt_memLp_two {H Y : S → ℝ} (hH : Measurable H) (hY : Measurable Y)
    (he : ∀ a : ℝ, Integrable (fun x => Real.exp (H x+a*Y x)) μ) (a : ℝ) :
    MemLp Y 2 (tiltLaw μ (fun x => H x+a*Y x) 1) := by
  apply (memLp_two_iff_integrable_sq hY.aestronglyMeasurable).mpr
  have hp : 0 < tiltPartition μ (fun x => H x+a*Y x) 1 :=
    tilt_partition_pos_of_integrable μ (by simpa only [one_mul] using he a)
  unfold tiltLaw
  apply Integrable.smul_measure _ (ENNReal.inv_ne_top.mpr (ENNReal.ofReal_ne_zero_iff.mpr hp))
  apply (integrable_withDensity_iff_integrable_smul'
    ((hH.add (hY.const_mul a)).const_mul 1 |>.exp.ennreal_ofReal)
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)).mpr
  simpa only [ENNReal.toReal_ofReal (Real.exp_pos _).le,smul_eq_mul,one_mul,Pi.add_apply] using
    coupling_weighted_power_integrable μ hH hY he a 2

lemma coupling_thermal_abs_sq_le {H Y : S → ℝ} (hH : Measurable H) (hY : Measurable Y)
    (he : ∀ a : ℝ, Integrable (fun x => Real.exp (H x+a*Y x)) μ) (a : ℝ) :
    (tiltMean μ (fun x => H x+a*Y x)
      (fun x => |Y x-tiltMean μ (fun x => H x+a*Y x) Y 1|) 1)^2 ≤
    tiltMean μ (fun x => H x+a*Y x)
      (fun x => (Y x-tiltMean μ (fun x => H x+a*Y x) Y 1)^2) 1 := by
  let T := fun x => H x+a*Y x
  have hT : Measurable T := hH.add (hY.const_mul a)
  have hi : Integrable (fun x => Real.exp (1*T x)) μ := by simpa only [one_mul] using he a
  let := tilt_law_probability_of_integrable μ hi
  have hY2 := coupling_tilt_memLp_two μ hH hY he a
  have hh := integral_centered_abs_le_sqrt_variance (tiltLaw μ T 1) hY2
  have hs := pow_le_pow_left₀ (integral_nonneg (fun x => abs_nonneg _)) hh 2
  rw [Real.sq_sqrt (variance_nonneg _ _),variance_eq_integral hY.aemeasurable] at hs
  simpa only [tilt_law_integral_of_integrable μ hT hi] using hs

lemma coupling_tilt_center_triangle {H Y : S → ℝ} (hH : Measurable H) (hY : Measurable Y)
    (he : ∀ a : ℝ, Integrable (fun x => Real.exp (H x+a*Y x)) μ) (a b c : ℝ) :
    tiltMean μ (fun x => H x+a*Y x) (fun x => |Y x-c|) 1 ≤
    tiltMean μ (fun x => H x+a*Y x) (fun x => |Y x-b|) 1+|b-c| := by
  let T := fun x => H x+a*Y x
  have hT : Measurable T := hH.add (hY.const_mul a)
  have hi : Integrable (fun x => Real.exp (1*T x)) μ := by simpa only [one_mul] using he a
  let := tilt_law_probability_of_integrable μ hi
  have hYi := (coupling_tilt_memLp_two μ hH hY he a).integrable (by norm_num)
  change tiltMean μ T (fun x => |Y x-c|) 1 ≤ tiltMean μ T (fun x => |Y x-b|) 1+|b-c|
  simp_rw [← tilt_law_integral_of_integrable μ hT hi]
  have hc : (∫ _ : S, |b-c| ∂tiltLaw μ T 1)=|b-c| := by simp
  have hib : Integrable (fun x => |Y x-b|) (tiltLaw μ T 1) := (hYi.sub (integrable_const b)).abs
  rw [← hc,← integral_add hib (integrable_const _)]
  apply integral_mono ((hYi.sub (integrable_const c)).abs)
    (((hYi.sub (integrable_const b)).abs).add (integrable_const _))
  intro x
  change |Y x-c| ≤ |Y x-b|+|b-c|
  calc
    _ = |(Y x-b)+(b-c)| := by congr 1; ring
    _ ≤ _ := abs_add_le _ _

end SphericalPerceptronFreeEnergy

end

end OAI
