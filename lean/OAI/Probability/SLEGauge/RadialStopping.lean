import Mathlib
import OAI.Probability.SLE.MomentGauge
import OAI.Probability.SLEGauge.TiltedMeasures

namespace OAI

/-! Hausdorff gauges, Loewner evolution and trace measures. -/

section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
open scoped Topology
open Set
open MeasureTheory Filter
open scoped NNReal Topology
open MeasureTheory Filter Set Metric Function ODE
open MeasureTheory ProbabilityTheory Filter Set
open Filter
namespace ExactSLEGreen
open ExactSLEGenerator ExactSLEMain
open scoped Classical
lemma capTime_eq (S : ExactSLEGenerator.Driver → ℝ≥0∞) (n : ℝ≥0) (b : ExactSLEGenerator.Driver)
    (h : S b ≤ n) : capTime S n b = (S b).toNNReal := by simp only [capTime,min_eq_left h]
lemma stopped_before_cap (S : ExactSLEGenerator.Driver → ℝ≥0∞) (hS : IsStoppingTime rawFiltration S)
    (n : ℝ≥0) (U : Set ExactSLEGenerator.Driver) (hU : MeasurableSet[hS.measurableSpace] U) :
    MeasurableSet[(capTime_stopping S hS n).measurableSpace] (U ∩ {b | S b < n}) := by
  have hc : IsStoppingTime rawFiltration (fun _ : ExactSLEGenerator.Driver => (n : WithTop ℝ≥0)) := isStoppingTime_const _ _
  have he : U ∩ {b | S b < n} = (U ∩ {b | S b ≤ n}) \ {b | S b = n} := by
    ext b
    simp only [Set.mem_inter_iff,Set.mem_ofPred_eq,Set.mem_sdiff]
    exact ⟨fun h => ⟨⟨h.1,h.2.le⟩,h.2.ne⟩,fun h => ⟨h.1.1,lt_of_le_of_ne h.1.2 h.2⟩⟩
  have hm := (hS.measurableSet_inter_le hc U hU).diff (hS.measurableSet_eq_stopping_time_min hc)
  have heq : (fun b => (capTime S n b : WithTop ℝ≥0)) = fun b => min (S b) (n : ℝ≥0∞) := funext (capTime_coe S n)
  rw [he]
  exact ((hS.min hc).measurableSpace_mono (capTime_stopping S hS n) (fun b => by
    change min (S b) (n : ℝ≥0∞) ≤ (capTime S n b : ℝ≥0∞)
    rw [capTime_coe])) _ hm

lemma stopped_cap_measurable (S : ExactSLEGenerator.Driver → ℝ≥0∞) (hS : IsStoppingTime rawFiltration S)
    (n : ℝ≥0) : (capTime_stopping S hS n).measurableSpace ≤ hS.measurableSpace :=
  (capTime_stopping S hS n).measurableSpace_mono hS (fun b => by
    change (capTime S n b : ℝ≥0∞) ≤ S b
    rw [capTime_coe]
    exact min_le_left _ _)
lemma stopping_before_measurable (S : ExactSLEGenerator.Driver → ℝ≥0∞) (hS : IsStoppingTime rawFiltration S)
    (n : ℝ≥0) : MeasurableSet {b | S b < n} :=
  hS.measurableSpace_le _ (hS.measurableSet_lt' n)

lemma eventually_before_nat {v : ℝ≥0∞} (hv : v ≠ ∞) : ∀ᶠ n : ℕ in atTop, v < ((n : ℝ≥0) : ℝ≥0∞) := by
  obtain ⟨N,hN⟩ := exists_nat_gt v.toNNReal
  filter_upwards [eventually_ge_atTop N] with n hn
  rw [← ENNReal.coe_toNNReal hv,ENNReal.coe_lt_coe]
  exact hN.trans_le (Nat.cast_le.mpr hn)

 

theorem radial_conditional_weight_all (W : Measure ExactSLEGenerator.Driver) [IsProbabilityMeasure W]
    (hW : IsBrownianReal (fun t (b : ExactSLEGenerator.Driver) => b.1 t) W)
    (a : ℝ) (ha : 1/4 < a) (z : ℂ) (hz : 0 < z.im)
    (ρ : ℝ) (hρ : 0 < ρ) (hr : ρ ≤ z.im)
    (S : ExactSLEGenerator.Driver → ℝ≥0∞) (hS : IsStoppingTime rawFiltration S)
    (U : Set ExactSLEGenerator.Driver) (hU : MeasurableSet[hS.measurableSpace] U) :
    Integrable (fun b => stoppedRadialRemaining a b.1 z ρ (S b)) W ∧
    (∫ b in U, (if S b < radialTime a b.1 z ρ then radialWeight a b.1 z ρ else 0) ∂W) =
      ∫ b in U, stoppedRadialRemaining a b.1 z ρ (S b) ∂W := by
  let C : ℕ → Set ExactSLEGenerator.Driver := fun n => {b | S b < (n : ℝ≥0)}
  let F := fun n => (C n).indicator (fun b => radialRemaining a b.1 z ρ (capTime S n b))
  let H := fun n => (C n).indicator (fun b => if (capTime S n b : ℝ≥0∞) < radialTime a b.1 z ρ then radialWeight a b.1 z ρ else 0)
  let G := fun b : ExactSLEGenerator.Driver => stoppedRadialRemaining a b.1 z ρ (S b)
  let K := fun b : ExactSLEGenerator.Driver => if S b < radialTime a b.1 z ρ then radialWeight a b.1 z ρ else 0
  let c := Real.exp (-alpha a*Real.log ρ)
  have hFi (n : ℕ) : Integrable (F n) W :=
    (radial_conditional_weight W hW a ha z hz ρ hρ hr (capTime S n) (capTime_stopping S hS n)
      Set.univ MeasurableSet.univ).1.indicator (stopping_before_measurable S hS n)
  have hHi (n : ℕ) : Integrable (H n) W :=
    (radial_terminal_integrable W hW a ha z hz ρ hρ hr (capTime S n) (capTime_stopping S hS n)).indicator
      (stopping_before_measurable S hS n)
  have hFc (b : ExactSLEGenerator.Driver) : Tendsto (fun n => F n b) atTop (𝓝 (G b)) := by
    by_cases hb : S b = ∞
    · have he : (fun n => F n b) = fun _ : ℕ => 0 := by
        funext n
        apply Set.indicator_of_notMem
        simp [C,hb]
      have hg : G b = 0 := by simp [G,stoppedRadialRemaining,hb]
      rw [he,hg]
      exact tendsto_const_nhds
    · apply Filter.Tendsto.congr' _ tendsto_const_nhds
      filter_upwards [eventually_before_nat hb] with n hn
      dsimp only [G,F,stoppedRadialRemaining]
      rw [ite_eq_right hb,Set.indicator_of_mem (show b ∈ C n from hn),capTime_eq S n b hn.le]
  have hHc (b : ExactSLEGenerator.Driver) : Tendsto (fun n => H n b) atTop (𝓝 (K b)) := by
    by_cases hb : S b = ∞
    · have he : (fun n => H n b) = fun _ : ℕ => 0 := by
        funext n
        apply Set.indicator_of_notMem
        simp [C,hb]
      have hk : K b = 0 := by simp [K,hb]
      rw [he,hk]
      exact tendsto_const_nhds
    · apply Filter.Tendsto.congr' _ tendsto_const_nhds
      filter_upwards [eventually_before_nat hb] with n hn
      dsimp only [K,H]
      rw [Set.indicator_of_mem (show b ∈ C n from hn),capTime_coe,min_eq_left hn.le]
  have hFb (n : ℕ) (b : ExactSLEGenerator.Driver) : ‖F n b‖ ≤ c := by
    by_cases hb : b ∈ C n
    · dsimp only [F]
      rw [Set.indicator_of_mem hb]
      exact radialRemaining_bound a ha z hz ρ hρ hr b (capTime S n b)
    · simpa only [F,Set.indicator_of_notMem hb,norm_zero] using (Real.exp_pos (-alpha a*Real.log ρ)).le
  have hHb (n : ℕ) (b : ExactSLEGenerator.Driver) : ‖H n b‖ ≤ c := by
    by_cases hb : b ∈ C n
    · dsimp only [H]
      rw [Set.indicator_of_mem hb]
      split_ifs
      · have h := radialWeight_bound a ha z hz ρ hρ hr b
        simpa only [Real.norm_eq_abs,abs_of_nonneg h.1] using h.2
      · simpa only [norm_zero] using (Real.exp_pos (-alpha a*Real.log ρ)).le
    · simpa only [H,Set.indicator_of_notMem hb,norm_zero] using (Real.exp_pos (-alpha a*Real.log ρ)).le
  have hGi : Integrable G W := Integrable.of_bound
    (aestronglyMeasurable_of_tendsto_ae atTop (fun n => (hFi n).aestronglyMeasurable) (Eventually.of_forall hFc)) c
    (Eventually.of_forall fun b => le_of_tendsto (hFc b).norm (Eventually.of_forall fun n => hFb n b))
  refine ⟨hGi,?_⟩
  have he (n : ℕ) : (∫ b in U, F n b ∂W) = ∫ b in U, H n b ∂W := by
    have hC := stopping_before_measurable S hS n
    dsimp only [F,H]
    rw [integral_indicator hC,integral_indicator hC,Measure.restrict_restrict hC,Set.inter_comm (C n) U]
    exact (radial_conditional_weight W hW a ha z hz ρ hρ hr (capTime S n) (capTime_stopping S hS n)
      (U ∩ C n) (stopped_before_cap S hS n U hU)).2.symm
  have hFl := tendsto_integral_of_dominated_convergence (μ := W.restrict U) (fun _ => c)
    (fun n => (hFi n).aestronglyMeasurable.restrict) (integrable_const c)
    (fun n => Eventually.of_forall (hFb n)) (Eventually.of_forall hFc)
  have hHl := tendsto_integral_of_dominated_convergence (μ := W.restrict U) (fun _ => c)
    (fun n => (hHi n).aestronglyMeasurable.restrict) (integrable_const c)
    (fun n => Eventually.of_forall (hHb n)) (Eventually.of_forall hHc)
  have heq : (fun n => ∫ b in U, F n b ∂W) = fun n => ∫ b in U, H n b ∂W := funext he
  rw [heq] at hFl
  exact tendsto_nhds_unique hHl hFl

end ExactSLEGreen

namespace ExactSLEGreen
open ExactSLEGenerator ExactSLEMain
open scoped Classical

noncomputable def radialLaw (W : Measure ExactSLEGenerator.Driver) (a : ℝ) (z : ℂ)
    (ρ : ℝ) : Measure ExactSLEGenerator.Driver :=
  W.withDensity (fun b => ENNReal.ofReal (radialWeight a b.1 z ρ / physicalGreen a (z,0)))

lemma radialTime_stopping (a : ℝ) (ha : 0 < a) (z : ℂ) (hz : 0 < z.im)
    (ρ : ℝ) (hρ : 0 < ρ) (hr : ρ ≤ z.im) :
    IsStoppingTime rawFiltration (fun b : ExactSLEGenerator.Driver => radialTime a b.1 z ρ) := by
  intro t
  let T := radialStop a ha z hz ρ hρ hr
  let L := fun n => radialLocalization a ha z hz ρ (angleThreshold z n) hρ hr
    (angleThreshold_pos z hz n) (angleThreshold_initial z hz n)
  let F := fun n (b : ExactSLEGenerator.Driver) =>
    physicalRadius (localState a (L n).ε (L n).hε z (min (T n b) t) b)
  have hFm (n : ℕ) : Measurable[rawFiltration t] (F n) := by
    have hT := radialStop_stopping a ha z hz ρ hρ hr n
    have hmin : IsStoppingTime rawFiltration (fun b => (min (T n b) t : WithTop ℝ≥0)) := by
      simpa only [WithTop.coe_min] using hT.min (isStoppingTime_const rawFiltration t)
    have hle : hmin.measurableSpace ≤ rawFiltration t :=
      hmin.measurableSpace_le_of_le_const (fun b => WithTop.coe_le_coe.mpr (min_le_right _ _))
    have hA : StronglyAdapted rawFiltration (localState a (L n).ε (L n).hε z) :=
      fun u => (localState_adapted a (L n).ε (L n).hε z u).stronglyMeasurable
    exact physicalRadius_continuous.measurable.comp
      ((measurable_stoppedValue (hA.isStronglyProgressive_of_continuous
        (localState_continuous a (L n).ε (L n).hε z)) hmin).mono hle le_rfl)
  have he : {b : ExactSLEGenerator.Driver | radialTime a b.1 z ρ ≤ (t : ℝ≥0∞)} =
      ⋃ n : ℕ, {b | T n b ≤ t} ∩ {b | F n b = ρ} := by
    ext b
    simp only [Set.mem_ofPred_eq,Set.mem_iUnion,Set.mem_inter_iff]
    constructor
    · intro hb
      have hfin : radialTime a b.1 z ρ ≠ ∞ := ne_top_of_le_ne_top ENNReal.coe_ne_top hb
      obtain ⟨n,hn⟩ := (radialStop_eventually_eq a ha z hz ρ hρ hr b hfin).exists
      have hnt : T n b ≤ t := by
        apply ENNReal.coe_le_coe.mp
        exact hn.trans_le hb
      refine ⟨n,hnt,?_⟩
      dsimp only [F]
      rw [min_eq_left hnt]
      have hr' := (radialTime_attained a ha z hz ρ hρ hr b hfin).2
      rw [← hn,ENNReal.toNNReal_coe] at hr'
      have hact := (regionStop_actualState a (L n).ε (L n).hε z (L n).N ρ
        (angleThreshold z n) (L n).B (L n).initial b (T n b) le_rfl).2
      rw [hact] at hr'
      exact hr'
    · rintro ⟨n,hnt,hR⟩
      dsimp only [F] at hR
      rw [min_eq_left hnt] at hR
      have htime := regionStop_eq_radialTime a (L n).ε (L n).hε z (L n).N ρ
        (angleThreshold z n) (L n).B (L n).initial b hR
      rw [htime]
      exact ENNReal.coe_le_coe.mpr hnt
  change MeasurableSet[rawFiltration t] {b : ExactSLEGenerator.Driver | radialTime a b.1 z ρ ≤ (t : ℝ≥0∞)}
  rw [he]
  apply MeasurableSet.iUnion
  intro n
  have hT := radialStop_stopping a ha z hz ρ hρ hr n
  have htm : MeasurableSet[rawFiltration t] {b | T n b ≤ t} := by
    simpa only [WithTop.coe_le_coe] using hT t
  exact htm.inter (measurableSet_eq_fun (hFm n) measurable_const)

lemma radialTime_le_of_hit (a : ℝ) (z : ℂ) (ρ : ℝ) (b : ExactSLEGenerator.Driver)
    (t : ℝ≥0) (ht : alive a b.1 t z) (hR : physicalRadius (actualState a b.1 t z) = ρ) :
    radialTime a b.1 z ρ ≤ (t : ℝ≥0∞) :=
  sInf_le ⟨t,rfl,ht,hR⟩

lemma radialTime_strict_of_finite (a : ℝ) (ha : 0 < a) (z : ℂ) (hz : 0 < z.im)
    (ρ σ : ℝ) (hρ : 0 < ρ) (hρσ : ρ < σ) (hσ : σ ≤ z.im)
    (b : ExactSLEGenerator.Driver) (hfin : radialTime a b.1 z ρ ≠ ∞) :
    radialTime a b.1 z σ < radialTime a b.1 z ρ := by
  have hr : ρ ≤ z.im := hρσ.le.trans hσ
  obtain ⟨n,hn⟩ := (radialStop_eventually_eq a ha z hz ρ hρ hr b hfin).exists
  let L := radialLocalization a ha z hz ρ (angleThreshold z n) hρ hr
    (angleThreshold_pos z hz n) (angleThreshold_initial z hz n)
  let T := radialStop a ha z hz ρ hρ hr n b
  let f := fun t : ℝ≥0 => physicalRadius (localState a L.ε L.hε z t b)
  have hfc : Continuous f := physicalRadius_continuous.comp (localState_continuous a L.ε L.hε z b)
  have hR : f T = ρ := by
    have h := (radialTime_attained a ha z hz ρ hρ hr b hfin).2
    rw [← hn,ENNReal.toNNReal_coe] at h
    rw [(regionStop_actualState a L.ε L.hε z L.N ρ (angleThreshold z n) L.B L.initial b T le_rfl).2] at h
    exact h
  have h0 : f 0 = z.im := by simp [f,localState_zero,physicalRadius,Y,J]
  obtain ⟨u,hu,huR⟩ := intermediate_value_Icc' (show (0 : ℝ≥0) ≤ T from bot_le) hfc.continuousOn
    (show σ ∈ Icc (f T) (f 0) by rw [hR,h0]; exact ⟨hρσ.le,hσ⟩)
  have huT : u < T := hu.2.lt_of_ne (by intro he; rw [he,hR] at huR; exact hρσ.ne huR)
  have hact := regionStop_actualState a L.ε L.hε z L.N ρ (angleThreshold z n) L.B L.initial b u hu.2
  have hle : radialTime a b.1 z σ ≤ (u : ℝ≥0∞) :=
    radialTime_le_of_hit a z σ b u hact.1 (by rw [hact.2]; exact huR)
  exact hle.trans_lt ((ENNReal.coe_lt_coe.mpr huT).trans_eq hn)

lemma radialTime_strict_of_first_finite (a : ℝ) (ha : 0 < a) (z : ℂ) (hz : 0 < z.im)
    (ρ σ : ℝ) (hρ : 0 < ρ) (hρσ : ρ < σ) (hσ : σ ≤ z.im)
    (b : ExactSLEGenerator.Driver) (hfin : radialTime a b.1 z σ ≠ ∞) :
    radialTime a b.1 z σ < radialTime a b.1 z ρ := by
  by_cases h : radialTime a b.1 z ρ = ∞
  · rw [h]
    exact lt_top_iff_ne_top.mpr hfin
  · exact radialTime_strict_of_finite a ha z hz ρ σ hρ hρσ hσ b h

lemma radialWeight_consistency
    (W : Measure ExactSLEGenerator.Driver) [IsProbabilityMeasure W]
    (hW : IsBrownianReal (fun t (b : ExactSLEGenerator.Driver) => b.1 t) W)
    (a : ℝ) (ha : 1/4 < a) (z : ℂ) (hz : 0 < z.im)
    (ρ σ : ℝ) (hρ : 0 < ρ) (hρσ : ρ < σ) (hσ : σ ≤ z.im)
    (hS : IsStoppingTime rawFiltration (fun b : ExactSLEGenerator.Driver => radialTime a b.1 z σ))
    (U : Set ExactSLEGenerator.Driver) (hU : MeasurableSet[hS.measurableSpace] U) :
    (∫ b in U, radialWeight a b.1 z ρ ∂W) = ∫ b in U, radialWeight a b.1 z σ ∂W := by
  have ha0 : 0 < a := by linarith
  have hsmall (b : ExactSLEGenerator.Driver) :
      (if radialTime a b.1 z σ < radialTime a b.1 z ρ then radialWeight a b.1 z ρ else 0) = radialWeight a b.1 z ρ := by
    by_cases hf : radialTime a b.1 z ρ = ∞
    · simp [radialWeight,hf]
    · rw [ite_eq_left (radialTime_strict_of_finite a ha0 z hz ρ σ hρ hρσ hσ b hf)]
  have hlarge (b : ExactSLEGenerator.Driver) :
      stoppedRadialRemaining a b.1 z ρ (radialTime a b.1 z σ) = radialWeight a b.1 z σ := by
    by_cases hf : radialTime a b.1 z σ = ∞
    · simp [stoppedRadialRemaining,radialWeight,hf]
    · have hat := (radialTime_attained a ha0 z hz σ (hρ.trans hρσ) hσ b hf).1
      have hlt := radialTime_strict_of_first_finite a ha0 z hz ρ σ hρ hρσ hσ b hf
      rw [stoppedRadialRemaining,ite_eq_right hf,radialRemaining,radialWeight,ite_eq_right hf]
      rw [ite_eq_left ⟨hat,by simpa only [ENNReal.coe_toNNReal hf] using hlt⟩]
  have hc := (radial_conditional_weight_all W hW a ha z hz ρ hρ (hρσ.le.trans hσ)
    (fun b => radialTime a b.1 z σ) hS U hU).2
  simpa only [hsmall,hlarge] using hc

lemma radialLaw_apply
    (W : Measure ExactSLEGenerator.Driver) [IsProbabilityMeasure W]
    (hW : IsBrownianReal (fun t (b : ExactSLEGenerator.Driver) => b.1 t) W)
    (a : ℝ) (ha : 1/4 < a) (z : ℂ) (hz : 0 < z.im)
    (ρ : ℝ) (hρ : 0 < ρ) (hr : ρ ≤ z.im)
    (U : Set ExactSLEGenerator.Driver) (hU : MeasurableSet U) :
    radialLaw W a z ρ U = ENNReal.ofReal ((∫ b in U, radialWeight a b.1 z ρ ∂W) / physicalGreen a (z,0)) := by
  rw [radialLaw,MeasureTheory.withDensity_apply _ hU]
  have hi := ((radialWeight_mean W hW a ha z hz ρ hρ hr).1.restrict (s := U)).div_const (physicalGreen a (z,0))
  have hn : 0 ≤ᵐ[W.restrict U] (fun b : ExactSLEGenerator.Driver => radialWeight a b.1 z ρ / physicalGreen a (z,0)) :=
    Eventually.of_forall (fun b => div_nonneg (radialWeight_bound a ha z hz ρ hρ hr b).1 (Real.exp_pos _).le)
  rw [← ofReal_integral_eq_lintegral_ofReal hi hn,integral_div]

lemma radialLaw_probability
    (W : Measure ExactSLEGenerator.Driver) [IsProbabilityMeasure W]
    (hW : IsBrownianReal (fun t (b : ExactSLEGenerator.Driver) => b.1 t) W)
    (a : ℝ) (ha : 1/4 < a) (z : ℂ) (hz : 0 < z.im)
    (ρ : ℝ) (hρ : 0 < ρ) (hr : ρ ≤ z.im) :
    IsProbabilityMeasure (radialLaw W a z ρ) := by
  rw [isProbabilityMeasure_iff,radialLaw_apply W hW a ha z hz ρ hρ hr Set.univ MeasurableSet.univ,
    Measure.restrict_univ,(radialWeight_mean W hW a ha z hz ρ hρ hr).2,
    div_self (show physicalGreen a (z,0) ≠ 0 from (Real.exp_pos _).ne'),ENNReal.ofReal_one]

theorem finite_radial_laws_consistent
    (W : Measure ExactSLEGenerator.Driver) [IsProbabilityMeasure W]
    (hW : IsBrownianReal (fun t (b : ExactSLEGenerator.Driver) => b.1 t) W)
    (a : ℝ) (ha : 1/4 < a) (z : ℂ) (hz : 0 < z.im)
    (ρ σ : ℝ) (hρ : 0 < ρ) (hρσ : ρ < σ) (hσ : σ ≤ z.im) :
    IsProbabilityMeasure (radialLaw W a z ρ) ∧ IsProbabilityMeasure (radialLaw W a z σ) ∧
    ∃ hS : IsStoppingTime rawFiltration (fun b : ExactSLEGenerator.Driver => radialTime a b.1 z σ),
      ∀ U, MeasurableSet[hS.measurableSpace] U → radialLaw W a z ρ U = radialLaw W a z σ U := by
  have hσ0 : 0 < σ := hρ.trans hρσ
  have hr : ρ ≤ z.im := hρσ.le.trans hσ
  have ha0 : 0 < a := by linarith
  have hS := radialTime_stopping a ha0 z hz σ hσ0 hσ
  refine ⟨radialLaw_probability W hW a ha z hz ρ hρ hr,
    radialLaw_probability W hW a ha z hz σ hσ0 hσ,hS,?_⟩
  intro U hU
  have hU' : MeasurableSet U := hS.measurableSpace_le _ hU
  rw [radialLaw_apply W hW a ha z hz ρ hρ hr U hU',
    radialLaw_apply W hW a ha z hz σ hσ0 hσ U hU',
    radialWeight_consistency W hW a ha z hz ρ σ hρ hρσ hσ hS U hU]

end ExactSLEGreen

namespace ExactSLEGenerator
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

 

theorem compact_test_optional_inequality
    (W : Measure Driver) [IsProbabilityMeasure W]
    (hW : IsBrownianReal (fun t (b : Driver) => b.1 t) W)
    (X : ℝ≥0 → Driver → E) (hXc : ∀ b, Continuous (fun t => X t b))
    (hXm : ∀ t, Measurable[rawFiltration t] (X t))
    (A : E → E) (hAc : Continuous A) (K : ℝ) (hK : 0 ≤ K) (hAb : ∀ x, ‖A x‖ ≤ K)
    (e : E) (he : ‖e‖ ≤ 1)
    (hXeq : ∀ (s h : ℝ≥0) b, X (s+h) b = X s b + increment s h b • e +
      ∫ t in (s : ℝ)..((s+h : ℝ≥0) : ℝ), A (X t.toNNReal b))
    (f : E → ℝ) (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (hfc : HasCompactSupport f)
    (S T : Driver → ℝ≥0) (B : ℝ≥0)
    (hS : IsStoppingTime rawFiltration (fun b => (S b : WithTop ℝ≥0)))
    (hT : IsStoppingTime rawFiltration (fun b => (T b : WithTop ℝ≥0)))
    (hST : ∀ b, S b ≤ T b) (hTB : ∀ b, T b ≤ B)
    (hneg : ∀ b t, S b ≤ t → t ≤ T b → generator f A e (X t b) ≤ 0)
    (U : Set Driver) (hU : MeasurableSet[hS.measurableSpace] U) :
    ∫ b in U, f (X (T b) b) ∂W ≤ ∫ b in U, f (X (S b) b) ∂W := by
  let M : ℝ≥0 → Driver → ℝ := fun t b => f (X t b) -
    ∫ u in (0 : ℝ)..(t : ℝ), generator f A e (X u.toNNReal b)
  have hM : Martingale M rawFiltration W :=
    compact_smooth_brownian_martingale W hW X hXc hXm A hAc K hK hAb e he hXeq f hf hfc
  have hgc (b : Driver) : Continuous (fun u : ℝ => generator f A e (X u.toNNReal b)) :=
    (generator_continuous f hf A hAc e).comp ((hXc b).comp continuous_real_toNNReal)
  have hmc (b : Driver) : Continuous (fun t => M t b) :=
    (hf.continuous.comp (hXc b)).sub
      ((intervalIntegral.continuous_primitive (fun s t => (hgc b).intervalIntegrable s t) 0).comp NNReal.continuous_coe)
  obtain ⟨C,D,hC,hD,hfb,hgb⟩ := compact_generator_bounds f hf hfc A K hK hAb e
  have hmb (t : ℝ≥0) (ht : t ≤ B+1) (b : Driver) : ‖M t b‖ ≤ C+D*(B+1) := by
    calc
      _ ≤ ‖f (X t b)‖ + ‖∫ u in (0 : ℝ)..(t : ℝ), generator f A e (X u.toNNReal b)‖ := norm_sub_le _ _
      _ ≤ C+D*(t : ℝ) := add_le_add (hfb _) (by
        simpa only [sub_zero,abs_of_nonneg t.coe_nonneg] using
          intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := (t : ℝ))
            (fun u _ => hgb (X u.toNNReal b)))
      _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_left (by exact_mod_cast ht) hD)
  have hFa : StronglyAdapted rawFiltration (fun t b => f (X t b)) := fun t =>
    (hf.continuous.measurable.comp (hXm t)).stronglyMeasurable
  have hFm (R : Driver → ℝ≥0)
      (hR : IsStoppingTime rawFiltration (fun b => (R b : WithTop ℝ≥0))) :
      Measurable (fun b => f (X (R b) b)) :=
    (measurable_stoppedValue (hFa.isStronglyProgressive_of_continuous
      (fun b => hf.continuous.comp (hXc b))) hR).mono hR.measurableSpace_le le_rfl
  have hFi (R : Driver → ℝ≥0)
      (hR : IsStoppingTime rawFiltration (fun b => (R b : WithTop ℝ≥0))) :
      Integrable (fun b => f (X (R b) b)) (W.restrict U) :=
    Integrable.of_bound (hFm R hR).aestronglyMeasurable C (Filter.Eventually.of_forall fun b => hfb _)
  have hMi (R : Driver → ℝ≥0)
      (hR : IsStoppingTime rawFiltration (fun b => (R b : WithTop ℝ≥0))) (hRB : ∀ b, R b≤B) :
      Integrable (fun b => M (R b) b) (W.restrict U) :=
    Integrable.of_bound (ExactSLEOptional.stopped_measurable rawFiltration hM hmc R hR).aestronglyMeasurable
      (C+D*(B+1)) (Filter.Eventually.of_forall fun b => hmb _ ((hRB b).trans (le_add_of_nonneg_right zero_le_one)) b)
  have hpw (b : Driver) : f (X (T b) b) - f (X (S b) b) ≤ M (T b) b - M (S b) b := by
    have hi := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
      ((hgc b).intervalIntegrable 0 (S b)) ((hgc b).intervalIntegrable (S b) (T b))
    have hn : (∫ u in (S b : ℝ)..(T b : ℝ), generator f A e (X u.toNNReal b)) ≤ 0 := by
      rw [intervalIntegral.integral_of_le (by exact_mod_cast hST b)]
      apply setIntegral_nonpos measurableSet_Ioc
      intro u hu
      apply hneg b u.toNNReal
      · exact_mod_cast (show (S b : ℝ) ≤ (u.toNNReal : ℝ) by rw [Real.coe_toNNReal _ ((S b).coe_nonneg.trans hu.1.le)]; exact hu.1.le)
      · exact (Real.toNNReal_le_toNNReal hu.2).trans_eq (by simp)
    dsimp only [M]
    linarith
  have hcomp := integral_mono ((hFi T hT).sub (hFi S hS))
    ((hMi T hT hTB).sub (hMi S hS (fun b => (hST b).trans (hTB b)))) hpw
  simp only [Pi.sub_apply] at hcomp
  rw [integral_sub (hFi T hT) (hFi S hS),
    integral_sub (hMi T hT hTB) (hMi S hS (fun b => (hST b).trans (hTB b)))] at hcomp
  have heq := ExactSLEOptional.setIntegral_optional_sampling rawFiltration hM hmc B
    (C+D*(B+1)) hmb S T hS hT hST hTB U hU
  linarith
end ExactSLEGenerator

namespace ExactSLEGreen
noncomputable def physicalTheta (v : State) : ℝ := Real.pi/2-Real.arctan (X v/Y v)
noncomputable def thetaDeriv (v : State) : State →L[ℝ] ℝ :=
  -(Y v/Q v) • X + (X v/Q v) • Y
noncomputable def physicalV (v : State) : ℝ := Y v/Q v
noncomputable def velocityDeriv (v : State) : State →L[ℝ] ℝ :=
  (1/Q v) • Y - (Y v/(Q v)^2) • ((2*X v) • X+(2*Y v) • Y)

lemma physicalTheta_mem (v : State) : physicalTheta v ∈ Ioo 0 Real.pi := by
  have h := Real.arctan_mem_Ioo (X v/Y v)
  dsimp only [physicalTheta]
  constructor <;> linarith [h.1,h.2]

lemma physicalTheta_cot (v : State) : Real.cot (physicalTheta v) = X v/Y v := by
  rw [physicalTheta,Real.cot_eq_cos_div_sin,Real.cos_pi_div_two_sub,Real.sin_pi_div_two_sub,
    ← Real.tan_eq_sin_div_cos,Real.tan_arctan]

lemma hasFDerivAt_physicalTheta (v : State) (hv : 0<Y v) :
    HasFDerivAt physicalTheta (thetaDeriv v) v := by
  have hy := hv.ne'
  have hq := (Q_pos hv).ne'
  have ht : 1+(X v/Y v)^2≠0 := ne_of_gt (by positivity)
  have hYinv := (hasDerivAt_inv hy).comp_hasFDerivAt v Y.hasFDerivAt
  have hd := ((X.hasFDerivAt.mul hYinv).arctan).const_sub (Real.pi/2)
  convert hd using 1 <;> try rfl
  apply ContinuousLinearMap.ext
  intro w
  simp only [thetaDeriv,add_apply,smul_apply,
    neg_apply,smul_eq_mul,Pi.mul_apply,Function.comp_apply]
  field_simp
  dsimp only [Q]
  ring

lemma thetaDeriv_noise (v : State) : thetaDeriv v noise = physicalV v := by
  simp [thetaDeriv,noise,physicalV,X,Y]

end ExactSLEGreen
end

end OAI
