import Mathlib
import OAI.Probability.SKValue.GroundState.CascadePassage
import OAI.Probability.SKValue.Equations.StrictProfile

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators
namespace SKValueG

lemma profile_penalty_mono (ε : ℝ≥0) (k : ℕ) {l : SKValue.HeatProfile}
    (hT : SKValue.profileTime l=1) :
    (∫ t in (0 : ℝ)..1,t*SKValue.profileCoeff l t) ≤
      ∫ t in (0 : ℝ)..1,t*SKValue.profileCoeff (SKValue.liftProfile ε k l) t := by
  have h1 := profile_weighted_integrable 0 l
  have h2 := profile_weighted_integrable 0 (SKValue.liftProfile ε k l)
  simp only [zero_add,SKValue.liftProfile_time,hT] at h1 h2
  apply intervalIntegral.integral_mono_on (by norm_num) h1 h2
  intro t ht
  exact mul_le_mul_of_nonneg_left (SKValue.liftProfile_coeff_lower ε k l t) ht.1

lemma weak_profile_guerra_upper (W : SKValue.BrownianSpace) {n : ℕ} (hn : 0<n)
    {ψ : ℝ → ℝ} (hψ : SKValue.SmoothTerminal ψ) (hb : ∀ x,|x|≤ψ x)
    {l : SKValue.HeatProfile} (hl : l.Pairwise (fun p r ↦ p.2≤r.2)) (hT : SKValue.profileTime l=1) :
    expectedMaximum n ≤ (n : ℝ)*(SKValue.profileValue ψ l 0 0-
      (1/2 : ℝ)*(∫ t in (0 : ℝ)..1,t*SKValue.profileCoeff l t)) := by
  have he : ∀ ε : ℝ,0<ε → expectedMaximum n ≤ (n : ℝ)*(SKValue.profileValue ψ l 0 0-
      (1/2 : ℝ)*(∫ t in (0 : ℝ)..1,t*SKValue.profileCoeff l t)+(3/2 : ℝ)*ε*(1+l.length)) := by
    intro ε hε
    let e : ℝ≥0 := ⟨ε,hε.le⟩
    have hepos : 0<e := hε
    have hs := profileTree_scale (q := 0) (by norm_num : (0 : ℝ)≤0)
      (SKValue.liftProfile_strict hepos 1 hl) (SKValue.liftProfile_positive hepos (by norm_num : 0<1) l)
    have hg := profileTree_valid (q := 0) (l := SKValue.liftProfile e 1 l)
      (by rw [zero_add,SKValue.liftProfile_time,hT])
    have hu := finite_step_guerra_upper hn _ hg hs
    have hv := profileTree_le_smooth hψ hb hs 0
    have hvb := abs_le.mp (hψ.liftProfile_bound W hl hT hepos 1 0)
    have hc := profile_penalty_mono e 1 hT
    rw [profileTree_correction] at hu
    simp only [SKValue.liftProfile_time,hT,zero_add] at hu
    have hnn : (0 : ℝ)≤n := by positivity
    have hvb' : SKValue.profileValue ψ (SKValue.liftProfile e 1 l) 0 0-SKValue.profileValue ψ l 0 0 ≤
        (3/2 : ℝ)*ε*(1+l.length) := by
      have h := hvb.2
      have hcoe : (e : ℝ)=ε := rfl
      rw [Nat.cast_one,hcoe] at h
      exact h
    apply hu.trans
    apply mul_le_mul_of_nonneg_left _ hnn
    linarith
  have hh : Tendsto (fun j : ℕ ↦ (n : ℝ)*(SKValue.profileValue ψ l 0 0-
      (1/2 : ℝ)*(∫ t in (0 : ℝ)..1,t*SKValue.profileCoeff l t)+
        (3/2 : ℝ)*(1/(j+1 : ℝ))*(1+l.length))) atTop
      (𝓝 ((n : ℝ)*(SKValue.profileValue ψ l 0 0-
        (1/2 : ℝ)*(∫ t in (0 : ℝ)..1,t*SKValue.profileCoeff l t)))) := by
    have hr : Tendsto (fun j : ℕ ↦ (3/2 : ℝ)*(1/(j+1 : ℝ))*(1+l.length)) atTop (𝓝 0) := by
      simpa only [mul_zero,zero_mul] using
        (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (3/2 : ℝ)).mul_const (1+(l.length : ℝ))
    simpa only [add_zero] using (hr.const_add (SKValue.profileValue ψ l 0 0-
      (1/2 : ℝ)*(∫ t in (0 : ℝ)..1,t*SKValue.profileCoeff l t))).const_mul (n : ℝ)
  exact ge_of_tendsto hh (Eventually.of_forall (fun (j : ℕ) ↦ he (1/(j+1 : ℝ)) (one_div_pos.mpr (by exact_mod_cast Nat.succ_pos j))))

end SKValueG

end

section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators
namespace SKValue

lemma logCoshTerminal_ge_abs {M : ℝ} (hM : 0<M) (x : ℝ) :
    |x|≤logCoshTerminal M x := by
  have hh := (log_two_cosh_bounds (M*x)).1
  rw [abs_mul,abs_of_pos hM] at hh
  exact (le_div_iff₀ hM).mpr (by simpa only [mul_comm] using hh)

lemma OrderParameter.weighted_cutoff_integral (γ : OrderParameter) :
    (∫ t in (0 : ℝ)..1,t*γ.cutoff t)=∫ t in (0 : ℝ)..1,t*γ.coeff t := by
  apply intervalIntegral.integral_congr_ae
  filter_upwards [Measure.ae_ne volume (1 : ℝ)] with t hne ht
  rw [uIoc_of_le (by norm_num : (0 : ℝ)≤1)] at ht
  have ht' : t∈Ico (0 : ℝ) 1 := ⟨ht.1.le,lt_of_le_of_ne ht.2 hne⟩
  simp only [OrderParameter.cutoff,indicator_of_mem ht']

lemma OrderParameter.weighted_grid_error (γ : OrderParameter) (j : ℕ) :
    |(∫ t in (0 : ℝ)..1,t*profileCoeff (γ.grid j) t)-(∫ t in (0 : ℝ)..1,t*γ.cutoff t)|≤γ.gridError j := by
  have hi : IntervalIntegrable (profileCoeff (γ.grid j)) volume 0 1 :=
    γ.grid_time j ▸ profileCoeff_integrable (γ.grid j)
  have hj : IntervalIntegrable γ.cutoff volume 0 1 := γ.cutoff_integrable.intervalIntegrable
  have hiw := hi.continuousOn_mul (continuous_id : Continuous (fun t : ℝ ↦ t)).continuousOn
  have hjw := hj.continuousOn_mul (continuous_id : Continuous (fun t : ℝ ↦ t)).continuousOn
  simp only [id_eq] at hiw hjw
  rw [←intervalIntegral.integral_sub hiw hjw]
  calc
    _ ≤ ∫ t in (0 : ℝ)..1,|t*profileCoeff (γ.grid j) t-t*γ.cutoff t| :=
      intervalIntegral.abs_integral_le_integral_abs (by norm_num)
    _ ≤ ∫ t in (0 : ℝ)..1,|profileCoeff (γ.grid j) t-γ.cutoff t| := by
      apply intervalIntegral.integral_mono_on (by norm_num) (hiw.sub hjw).abs (hi.sub hj).abs
      intro t ht
      rw [←mul_sub,abs_mul,abs_of_nonneg ht.1]
      exact mul_le_of_le_one_left (abs_nonneg _) ht.2
    _ = γ.gridError j := rfl

lemma OrderParameter.weighted_grid_tendsto (γ : OrderParameter) :
    Tendsto (fun j ↦ ∫ t in (0 : ℝ)..1,t*profileCoeff (γ.grid j) t) atTop
      (𝓝 (∫ t in (0 : ℝ)..1,t*γ.coeff t)) := by
  rw [←γ.weighted_cutoff_integral]
  apply (tendsto_iff_dist_tendsto_zero).mpr
  simp only [Real.dist_eq]
  exact squeeze_zero (fun _ ↦ abs_nonneg _) γ.weighted_grid_error γ.gridError_tendsto

theorem expectedMaximum_le_parisi (W : BrownianSpace) (γ : OrderParameter) {n : ℕ} (hn : 0<n) :
    SKValueG.expectedMaximum n≤(n : ℝ)*parisi W γ := by
  have ht := (smoothApprox_tendsto W γ).tendsto_at ((⟨0,by norm_num⟩ : Ico (0 : ℝ) 1),0)
  have hp := γ.weighted_grid_tendsto
  have hf : Tendsto (fun j ↦ (n : ℝ)*(smoothApprox γ j 0 0-
      (1/2 : ℝ)*(∫ t in (0 : ℝ)..1,t*profileCoeff (γ.grid j) t))) atTop (𝓝 ((n : ℝ)*parisi W γ)) := by
    simpa only [parisi] using tendsto_const_nhds.mul (ht.sub (tendsto_const_nhds.mul hp))
  apply ge_of_tendsto hf
  exact Eventually.of_forall (fun j ↦ SKValueG.weak_profile_guerra_upper W hn
    (logCoshTerminal_smoothTerminal (by positivity : (0 : ℝ)<j+1))
    (logCoshTerminal_ge_abs (by positivity)) (γ.grid_mono j) (γ.grid_time j))

theorem groundStateValue_le_parisi (W : BrownianSpace) (γ : OrderParameter) :
    groundStateValue≤parisi W γ := by
  have he : SKValueG.groundStateSequence=groundStateSequence := rfl
  have hev : SKValueG.groundStateValue=groundStateValue := rfl
  have ht := SKValueG.groundStateSequence_tendsto
  rw [he,hev] at ht
  apply le_of_tendsto ht
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  change SKValueG.groundStateSequence n≤_
  rw [SKValueG.groundStateSequence_eq]
  have hn' : (0 : ℝ)<n := by exact_mod_cast hn
  have hh := mul_le_mul_of_nonneg_left (expectedMaximum_le_parisi W γ hn) (inv_nonneg.mpr hn'.le)
  simpa only [←mul_assoc,inv_mul_cancel₀ hn'.ne',one_mul] using hh

end SKValue

end

end OAI
