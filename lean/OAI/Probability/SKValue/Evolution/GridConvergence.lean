import Mathlib
import OAI.Probability.SKValue.Control.ControlPayoffConvex
import OAI.Probability.SKValue.Evolution.LogCoshTerminal
import OAI.Probability.SKValue.Gaussian.EvenEvolution
import OAI.Probability.SKValue.Control.FiniteStepControl
import OAI.Probability.SKValue.Evolution.GridProfile
import OAI.Probability.SKValue.Control.SupStability

namespace OAI

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators
namespace SKValue

lemma OrderParameter.grid_tendsto (γ : OrderParameter) {t : ℝ} (ht : t∈Ico (0 : ℝ) 1)
    (hc : ContinuousWithinAt γ.coeff (Ico (0 : ℝ) 1) t) :
    Tendsto (fun n ↦ profileCoeff (γ.grid n) t) atTop (𝓝 (γ.coeff t)) := by
  have hp (n : ℕ) := γ.grid_sample n ⟨ht.1,ht.2.le⟩
  choose r hr he hrt hdist using hp
  have hrd : Tendsto (fun n ↦ dist (r n) t) atTop (𝓝 0) := by
    apply squeeze_zero (fun n ↦ dist_nonneg) _ tendsto_one_div_add_atTop_nhds_zero_nat
    intro n
    rw [Real.dist_eq,abs_sub_comm,abs_of_nonneg (sub_nonneg.mpr (hrt n))]
    exact hdist n
  have hrl : Tendsto r atTop (𝓝 t) := (tendsto_iff_dist_tendsto_zero).mpr hrd
  have hl := hc.tendsto.comp (tendsto_nhdsWithin_iff.mpr ⟨hrl,Eventually.of_forall hr⟩)
  exact hl.congr (fun n ↦ (he n).symm)

lemma OrderParameter.grid_ae_tendsto (γ : OrderParameter) :
    ∀ᵐ t ∂volume, t∈Ioc (0 : ℝ) 1 →
      Tendsto (fun n ↦ profileCoeff (γ.grid n) t) atTop (𝓝 (γ.cutoff t)) := by
  filter_upwards [γ.monotone.countable_not_continuousWithinAt.ae_notMem volume,Measure.ae_ne volume (1 : ℝ)] with t hc hne ht
  have ht' : t∈Ico (0 : ℝ) 1 := ⟨ht.1.le,lt_of_le_of_ne ht.2 hne⟩
  have hc' : ContinuousWithinAt γ.coeff (Ico (0 : ℝ) 1) t := by
    by_contra hh
    exact hc ⟨ht',hh⟩
  simpa only [OrderParameter.cutoff,indicator_of_mem ht'] using γ.grid_tendsto ht' hc'

lemma OrderParameter.grid_ae_error_bound (γ : OrderParameter) (n : ℕ) :
    ∀ᵐ t ∂volume, t∈Ioc (0 : ℝ) 1 → |profileCoeff (γ.grid n) t-γ.cutoff t| ≤ γ.cutoff t := by
  filter_upwards [Measure.ae_ne volume (1 : ℝ)] with t hne ht
  have ht' : t∈Ico (0 : ℝ) 1 := ⟨ht.1.le,lt_of_le_of_ne ht.2 hne⟩
  rw [OrderParameter.cutoff,indicator_of_mem ht',abs_sub_comm,abs_of_nonneg (sub_nonneg.mpr (γ.grid_le n ht'))]
  linarith [profileCoeff_nonneg (γ.grid n) t]

noncomputable def OrderParameter.gridError (γ : OrderParameter) (n : ℕ) : ℝ :=
  ∫ t in (0 : ℝ)..1, |profileCoeff (γ.grid n) t-γ.cutoff t|

lemma OrderParameter.gridError_nonneg (γ : OrderParameter) (n : ℕ) : 0 ≤ γ.gridError n :=
  intervalIntegral.integral_nonneg (by norm_num) (fun _ _ ↦ abs_nonneg _)

lemma OrderParameter.gridError_tendsto (γ : OrderParameter) :
    Tendsto γ.gridError atTop (𝓝 0) := by
  have hl := intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (a := 0) (b := 1) (μ := volume) (l := atTop) (f := fun _ : ℝ ↦ (0 : ℝ))
    (F := fun n t ↦ |profileCoeff (γ.grid n) t-γ.cutoff t|) γ.cutoff
    (Eventually.of_forall (fun n ↦ ((profileCoeff_measurable (γ.grid n)).sub γ.cutoff_measurable).abs.aestronglyMeasurable))
    (Eventually.of_forall (fun n ↦ by
      filter_upwards [γ.grid_ae_error_bound n] with t ht ht'
      rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht'
      simpa only [Real.norm_eq_abs,abs_abs] using ht ht'))
    γ.cutoff_integrable.intervalIntegrable (by
      filter_upwards [γ.grid_ae_tendsto] with t ht ht'
      have hl := ((ht (by simpa only [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using ht')).sub_const (γ.cutoff t)).abs
      simpa only [sub_self,abs_zero] using hl)
  change Tendsto (fun n ↦ ∫ t in (0 : ℝ)..1, |profileCoeff (γ.grid n) t-γ.cutoff t|) atTop (𝓝 0)
  simpa only [intervalIntegral.integral_zero] using hl

lemma OrderParameter.grid_shift_error_le (γ : OrderParameter) (n : ℕ) {t : ℝ}
    (ht : t∈Icc (0 : ℝ) 1) :
    (∫ s in (0 : ℝ)..(1-t), |profileCoeff (γ.grid n) (t+s)-γ.cutoff (t+s)|) ≤ γ.gridError n := by
  have hg : IntervalIntegrable (profileCoeff (γ.grid n)) volume 0 1 := by
    simpa only [γ.grid_time] using profileCoeff_integrable (γ.grid n)
  have hi := (hg.sub γ.cutoff_integrable.intervalIntegrable).abs
  have hisub := hi.mono_set (show uIcc t 1⊆uIcc (0 : ℝ) 1 by
    rw [uIcc_of_le ht.2,uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact Icc_subset_Icc ht.1 le_rfl)
  have he : (∫ s in (0 : ℝ)..(1-t), |profileCoeff (γ.grid n) (t+s)-γ.cutoff (t+s)|)=
      ∫ s in t..1, |profileCoeff (γ.grid n) s-γ.cutoff s| := by
    simpa only [add_zero,add_sub_cancel] using intervalIntegral.integral_comp_add_left
      (f := fun s ↦ |profileCoeff (γ.grid n) s-γ.cutoff s|) (a := 0) (b := 1-t) t
  rw [he]
  exact intervalIntegral.integral_mono_interval ht.1 ht.2 le_rfl
    (Eventually.of_forall (fun s ↦ abs_nonneg _)) hi

end SKValue

end

section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators
namespace SKValue

lemma controlIntegral_eq_accum (W : BrownianSpace) (γ : OrderParameter) {t : ℝ}
    (ht : t∈Icc (0 : ℝ) 1) (α : ℝ≥0 → W.Ω → ℝ) (k : ℕ) (ω : W.Ω) :
    controlIntegral γ t α k ω=controlAccum (fun s ↦ γ.cutoff (t+s)) α k (1-t) ω := by
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le (sub_nonneg.mpr ht.2)] at hs
  dsimp only
  rw [limitedControl_eq α (by linarith [hs.2,ht.1])]

lemma phi_eq_elapsedValue (W : BrownianSpace) (γ : OrderParameter) {t : ℝ}
    (ht : t∈Icc (0 : ℝ) 1) (x : ℝ) :
    phi W γ t x=elapsedValue W.μ (shiftedFiltration W t)
      (fun ω ↦ W.B 1 ω-W.B t.toNNReal ω) abs (fun s ↦ γ.cutoff (t+s)) (1-t) x := by
  unfold phi elapsedValue
  congr 1
  ext r
  simp only [Admissible,and_assoc,controlPayoff_eq W γ ht,
    controlIntegral_eq_accum W γ ht,elapsedPayoff]

lemma SmoothTerminal.profile_elapsedValue (W : BrownianSpace)
    {ψ : ℝ → ℝ} (hψ : SmoothTerminal ψ) {l : HeatProfile}
    (hl : l.Pairwise (fun p q ↦ p.2 ≤ q.2)) (hT : profileTime l=1)
    {t : ℝ} (ht : t∈Ico (0 : ℝ) 1) (x : ℝ) :
    elapsedValue W.μ (shiftedFiltration W t) (fun ω ↦ W.B 1 ω-W.B t.toNNReal ω)
      ψ (fun s ↦ profileCoeff l (t+s)) (1-t) x=profileValue ψ l t x := by
  rw [← hψ.profile_control_from W hl hT ht x]
  unfold elapsedValue
  congr 1
  ext r
  simp only [elapsedPayoff,Admissible,controlAccum,pow_one,and_assoc,
    sub_eq_add_neg,add_assoc]

noncomputable def smoothApprox (γ : OrderParameter) (n : ℕ) : ℝ → ℝ → ℝ :=
  profileValue (logCoshTerminal (n+1 : ℝ)) (γ.grid n)

lemma smoothApprox_evolution (γ : OrderParameter) (n : ℕ) :
    SmoothEvolution 1 (profileCoeff (γ.grid n)) (smoothApprox γ n) := by
  unfold smoothApprox
  convert (logCoshTerminal_smoothTerminal (by positivity : (0 : ℝ)<n+1)).profile_evolution (γ.grid n) using 1
  exact (γ.grid_time n).symm

lemma smoothApprox_even (γ : OrderParameter) (n : ℕ) (t x : ℝ) :
    smoothApprox γ n t (-x)=smoothApprox γ n t x :=
  profileValue_even (logCoshTerminal_even (n+1 : ℝ)) (γ.grid n) t x

lemma smoothApprox_value_bound (W : BrownianSpace) (γ : OrderParameter) (n : ℕ)
    {t : ℝ} (ht : t∈Ico (0 : ℝ) 1) (x : ℝ) :
    |smoothApprox γ n t x-phi W γ t x| ≤ Real.log 2/(n+1 : ℝ)+(3/2 : ℝ)*γ.gridError n := by
  have hZ := brownian_increment_memLp W t
  have hψ := logCoshTerminal_smoothTerminal (by positivity : (0 : ℝ)<n+1)
  have hm : Measurable (fun s : ℝ ↦ profileCoeff (γ.grid n) (t+s)) := (profileCoeff_measurable (γ.grid n)).comp (measurable_const.add measurable_id)
  have hi : IntervalIntegrable (fun s ↦ profileCoeff (γ.grid n) (t+s)) volume 0 (1-t) := by
    have hgi : IntervalIntegrable (profileCoeff (γ.grid n)) volume t 1 := by
      apply (profileCoeff_integrable (γ.grid n)).mono_set
      rw [γ.grid_time,uIcc_of_le ht.2.le,uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
      exact Icc_subset_Icc ht.1 le_rfl
    simpa only [sub_self] using hgi.comp_add_left t
  have hic : IntervalIntegrable (fun s ↦ γ.cutoff (t+s)) volume 0 (1-t) := by
    simpa only [sub_self] using (γ.cutoff_integrable.intervalIntegrable (a := t) (b := 1)).comp_add_left t
  have he := elapsedValue_difference_bound (f := shiftedFiltration W t) hZ hψ.lipschitz
    (by
      apply LipschitzWith.of_dist_le_mul
      intro a b
      simpa only [Real.dist_eq,NNReal.coe_one,one_mul] using abs_abs_sub_abs_le_abs_sub a b)
    (logCoshTerminal_uniform_error (by positivity : (0 : ℝ)<n+1))
    hm (γ.cutoff_measurable.comp (measurable_const.add measurable_id)) hi hic
    (sub_nonneg.mpr ht.2.le) (x := x)
  dsimp only [Function.comp_def,Pi.add_apply,id_eq] at he
  rw [hψ.profile_elapsedValue W (γ.grid_mono n) (γ.grid_time n) ht x,
    ← phi_eq_elapsedValue W γ ⟨ht.1,ht.2.le⟩ x] at he
  change |smoothApprox γ n t x-phi W γ t x| ≤ _ at he
  have hb := γ.grid_shift_error_le n ⟨ht.1,ht.2.le⟩
  linarith

lemma smoothApprox_tendsto (W : BrownianSpace) (γ : OrderParameter) :
    TendstoUniformly (fun n (p : Ico (0 : ℝ) 1×ℝ) ↦ smoothApprox γ n p.1 p.2)
      (fun p ↦ phi W γ p.1 p.2) atTop := by
  have hlim : Tendsto (fun (n : ℕ) ↦ Real.log 2/(n+1 : ℝ)+(3/2 : ℝ)*γ.gridError n) atTop (𝓝 0) := by
    have h1 := tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (Real.log 2)
    have h2 := γ.gridError_tendsto.const_mul (3/2 : ℝ)
    simpa only [mul_one_div,mul_zero,add_zero] using h1.add h2
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  filter_upwards [hlim.eventually (gt_mem_nhds hε)] with n hn p
  rw [Real.dist_eq,abs_sub_comm]
  exact (smoothApprox_value_bound W γ n p.1.property p.2).trans_lt hn

end SKValue

end

end OAI
