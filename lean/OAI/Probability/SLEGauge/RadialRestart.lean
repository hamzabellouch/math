import Mathlib
import OAI.Probability.SLE.MomentGauge
import OAI.Probability.SLEGauge.AngleLyapunov

namespace OAI

/-! Hausdorff gauges, Loewner evolution and trace measures. -/

section
 

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology
namespace SLEExactGauge.LoewnerRestart
open FlowIdentification ExactSLEMain ExactSLEGreen ExactSLEGenerator

lemma physicalRadius_actual_eq_inv_deriv (a : ℝ) (b : GDriver) (s : ℝ≥0)
    (z : ℂ) (hs : alive a b.1 s z) :
    physicalRadius (actualState a b.1 s z) =
      ‖deriv (loewnerMap a b.1 s) z‖⁻¹ * (actualState a b.1 s z).1.im := by
  unfold physicalRadius actualState
  simp only [Y_apply, J_apply, Real.exp_neg]
  rw [Real.exp_log (norm_pos_iff.mpr (deriv_loewnerMap_ne_zero b.1.continuous hs))]
  ring

lemma radialTime_restart (a : ℝ) (ha : 0<a) (z : ℂ) (hz : 0<z.im)
    (σ ρ : ℝ) (hρ : 0<ρ) (hρσ : ρ≤σ) (hσ : σ≤z.im)
    (b : GDriver) (hb : radialTime a b.1 z σ≠∞) :
    let s := (radialTime a b.1 z σ).toNNReal
    let w := (actualState a b.1 s z).1
    (s : ℝ≥0∞) + radialTime a (restart s b).1 w (w.im*(ρ/σ)) =
      radialTime a b.1 z ρ := by
  let s := (radialTime a b.1 z σ).toNNReal
  let w := (actualState a b.1 s z).1
  let c := ‖deriv (loewnerMap a b.1 s) z‖
  have hσ0 := hρ.trans_le hρσ
  have hs := radialTime_attained a ha z hz σ hσ0 hσ b hb
  have hc : 0<c := norm_pos_iff.mpr (deriv_loewnerMap_ne_zero b.1.continuous hs.1)
  have hrel : c⁻¹*w.im=σ :=
    (physicalRadius_actual_eq_inv_deriv a b s z hs.1).symm.trans hs.2
  have hr : c⁻¹*(w.im*(ρ/σ))=ρ := by rw [←mul_assoc,hrel]; field_simp
  have hle (t : ℝ≥0) (ht : alive a b.1 t z)
      (hR : physicalRadius (actualState a b.1 t z)=ρ) : s≤t := by
    apply ENNReal.coe_le_coe.mp
    rw [show (s:ℝ≥0∞)=radialTime a b.1 z σ from ENNReal.coe_toNNReal hb]
    exact (radialTime_antitone a ha z hz ρ σ hρ hρσ hσ b).trans
      (radialTime_le_of_hit a z ρ b t ht hR)
  have he : (fun u : ℝ≥0∞ => (s:ℝ≥0∞)+u) ''
      {u : ℝ≥0∞ | ∃t : ℝ≥0, u=t ∧ alive a (restart s b).1 t w ∧
        physicalRadius (actualState a (restart s b).1 t w)=w.im*(ρ/σ)} =
      {u : ℝ≥0∞ | ∃t : ℝ≥0, u=t ∧ alive a b.1 t z ∧
        physicalRadius (actualState a b.1 t z)=ρ} := by
    ext u
    constructor
    · rintro ⟨u,⟨t,rfl,ht,hR⟩,rfl⟩
      have ht' : alive a b.1 (s+t) z := (alive_restart_iff a b.1 z s t).mpr ⟨hs.1,ht⟩
      refine ⟨s+t,by simp,ht',?_⟩
      rw [physicalRadius_restart b.1.continuous ht']
      change c⁻¹*physicalRadius (actualState a (restart s b).1 t w)=ρ
      rw [hR,hr]
    · rintro ⟨t,rfl,ht,hR⟩
      have hst := hle t ht hR
      let v := t-s
      have heq : s+v=t := add_tsub_cancel_of_le hst
      have ht' : alive a (restart s b).1 v w :=
        ((alive_restart_iff a b.1 z s v).mp (heq ▸ ht)).2
      refine ⟨v,⟨v,rfl,ht',?_⟩,by simp [←ENNReal.coe_add,heq]⟩
      apply (mul_left_cancel₀ (inv_ne_zero hc.ne'))
      rw [hr]
      calc
        c⁻¹*physicalRadius (actualState a (restart s b).1 v w) =
            physicalRadius (actualState a b.1 (s+v) z) :=
          (physicalRadius_restart b.1.continuous (heq ▸ ht)).symm
        _ = ρ := by rw [heq,hR]
  change (s:ℝ≥0∞)+sInf _=sInf _
  rw [ENNReal.add_sInf,←sInf_image,he]

lemma radialTime_restart_top_iff (a : ℝ) (ha : 0<a) (z : ℂ) (hz : 0<z.im)
    (σ ρ : ℝ) (hρ : 0<ρ) (hρσ : ρ≤σ) (hσ : σ≤z.im)
    (b : GDriver) (hb : radialTime a b.1 z σ≠∞) :
    let s := (radialTime a b.1 z σ).toNNReal
    let w := (actualState a b.1 s z).1
    radialTime a (restart s b).1 w (w.im*(ρ/σ))=∞ ↔ radialTime a b.1 z ρ=∞ := by
  rw [←radialTime_restart a ha z hz σ ρ hρ hρσ hσ b hb]
  simp

 

lemma radialWeight_restart (a : ℝ) (ha : 0<a) (z : ℂ) (hz : 0<z.im)
    (σ ρ : ℝ) (hρ : 0<ρ) (hρσ : ρ≤σ) (hσ : σ≤z.im)
    (b : GDriver) (hb : radialTime a b.1 z σ≠∞) :
    let s := (radialTime a b.1 z σ).toNNReal
    let w := (actualState a b.1 s z).1
    radialWeight a b.1 z ρ = radialWeight a b.1 z σ *
      (radialWeight a (restart s b).1 w (w.im*(ρ/σ)) / physicalGreen a (w,0)) := by
  let s := (radialTime a b.1 z σ).toNNReal
  let w := (actualState a b.1 s z).1
  let τ := radialTime a (restart s b).1 w (w.im*(ρ/σ))
  change radialWeight a b.1 z ρ = radialWeight a b.1 z σ *
    (radialWeight a (restart s b).1 w (w.im*(ρ/σ)) / physicalGreen a (w,0))
  have htop := radialTime_restart_top_iff a ha z hz σ ρ hρ hρσ hσ b hb
  have hs := radialTime_attained a ha z hz σ (hρ.trans_le hρσ) hσ b hb
  by_cases hf : radialTime a b.1 z ρ=∞
  · rw [show radialWeight a b.1 z ρ = 0 from ite_eq_left hf,
      show radialWeight a (restart s b).1 w (w.im*(ρ/σ)) = 0 from ite_eq_left (htop.mpr hf)]
    simp
  · have hτ : τ≠∞ := fun h => hf (htop.mp h)
    have ht : s+τ.toNNReal=(radialTime a b.1 z ρ).toNNReal := by
      have hh := congrArg ENNReal.toNNReal (radialTime_restart a ha z hz σ ρ hρ hρσ hσ b hb)
      change ((s:ℝ≥0∞)+τ).toNNReal=(radialTime a b.1 z ρ).toNNReal at hh
      simpa only [ENNReal.toNNReal_add ENNReal.coe_ne_top hτ,ENNReal.toNNReal_coe] using hh
    have hfull := (radialTime_attained a ha z hz ρ hρ (hρσ.trans hσ) b hf).1
    rw [show radialWeight a b.1 z ρ = _ from ite_eq_right hf,
      show radialWeight a b.1 z σ = _ from ite_eq_right hb,
      show radialWeight a (restart s b).1 w (w.im*(ρ/σ)) = _ from ite_eq_right hτ]
    rw [←ht,actualState_restart b.1.continuous (ht ▸ hfull),physicalGreen_add_log]
    have hi : physicalGreen a (actualState a b.1 s z) =
        Real.exp (alpha a*(actualState a b.1 s z).2)*physicalGreen a (w,0) := by
      convert physicalGreen_add_log a (w,0) (actualState a b.1 s z).2 using 1
      simp [w]
    change Real.exp (alpha a*(actualState a b.1 s z).2)*
      physicalGreen a (actualState a (restart s b).1 τ.toNNReal w) = _
    rw [hi]
    have hG : physicalGreen a (w,0) ≠ 0 := (Real.exp_pos _).ne'
    field_simp [hG]
    simp only [τ,mul_div_assoc]

end SLEExactGauge.LoewnerRestart
end
end
 

 
section
 

open MeasureTheory ProbabilityTheory Filter Set
open scoped Classical NNReal ENNReal Topology

namespace ExactSLEGreen
open ExactSLEGenerator ExactSLEMain

lemma actualState_continuousOn {a : ℝ} {b : ℝ≥0 → ℝ} (hb : Continuous b)
    {z : ℂ} {T : ℝ≥0} (hT : alive a b T z) :
    ContinuousOn (fun u : ℝ => actualState a b u.toNNReal z) (Icc 0 (T : ℝ)) := by
  obtain ⟨f,hf⟩ := hT
  let Z : ℝ → ℂ := fun u => f u - (b u.toNNReal : ℂ)
  let A : ℝ → ℝ := fun u => (-(a : ℂ) / (Z u)^2).re
  have hZ : ContinuousOn Z (Icc 0 (T : ℝ)) := odeUntil_center_continuousOn hb hf
  have hA : ContinuousOn A (Icc 0 (T : ℝ)) :=
    Complex.continuous_re.comp_continuousOn (continuousOn_const.div (hZ.pow 2)
      (fun u hu => pow_ne_zero _ (odeUntil_center_ne_zero hf hu)))
  have hAi : IntervalIntegrable A volume 0 T := hA.intervalIntegrable_of_Icc T.coe_nonneg
  have hprim : ContinuousOn (fun u : ℝ => ∫ v in (0 : ℝ)..u, A v)
      (Icc 0 (T : ℝ)) := by
    simpa only [uIcc_of_le T.coe_nonneg] using
      intervalIntegral.continuousOn_primitive_interval' hAi
        (show (0 : ℝ) ∈ uIcc 0 (T : ℝ) from left_mem_uIcc)
  have hC := hZ.prodMk hprim
  apply hC.congr
  intro u hu
  have huT : u.toNNReal ≤ T := by simpa using Real.toNNReal_le_toNNReal hu.2
  apply Prod.ext
  · simp only [actualState,Z,loewnerMap_eq_solution_time hf hu]
  · change Real.log ‖deriv (loewnerMap a b u.toNNReal) z‖ = _
    rw [log_norm_deriv_loewnerMap hb ⟨f,odeUntil_mono hf huT⟩,
      Real.coe_toNNReal _ hu.1]
    apply intervalIntegral.integral_congr
    intro v hv
    have hv' : v ∈ Icc 0 (T : ℝ) :=
      (Icc_subset_Icc_right hu.2) (by simpa only [uIcc_of_le hu.1] using hv)
    simp only [Z,loewnerMap_eq_solution_time hf hv']

lemma actualState_bounded_until {a : ℝ} {b : ℝ≥0 → ℝ} (hb : Continuous b)
    {z : ℂ} {T : ℝ≥0} (hT : alive a b T z) :
    ∃ η C : ℝ, 0 < η ∧ ∀ t : ℝ≥0, t ≤ T →
      η ≤ Y (actualState a b t z) ∧ ‖actualState a b t z‖ ≤ C := by
  obtain ⟨f,hf⟩ := hT
  obtain ⟨η,hη,hmin⟩ := odeUntil_height_lower hf
  obtain ⟨C,hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (actualState_continuousOn hb ⟨f,hf⟩)
  refine ⟨η,C,hη,?_⟩
  intro t ht
  have hmem : (t : ℝ) ∈ Icc 0 (T : ℝ) := ⟨t.coe_nonneg,ht⟩
  constructor
  · have he : loewnerMap a b t z = f t := by
      simpa only [Real.toNNReal_coe] using loewnerMap_eq_solution_time hf hmem
    simpa only [actualState,Y_apply,he,Complex.sub_im,Complex.ofReal_im,sub_zero]
      using hmin (t : ℝ) hmem
  · simpa only [Real.toNNReal_coe] using hC (t : ℝ) hmem

noncomputable def exhaustionHeight (z : UpperPlane) (n : ℕ) : ℝ :=
  z.1.im / ((n : ℝ) + 2)

lemma exhaustionHeight_pos (z : UpperPlane) (n : ℕ) : 0 < exhaustionHeight z n :=
  div_pos z.2 (by positivity)

lemma exhaustionHeight_le (z : UpperPlane) (n : ℕ) : exhaustionHeight z n ≤ z.1.im := by
  exact div_le_self z.2.le (by linarith [Nat.cast_nonneg (α := ℝ) n])

lemma exhaustionHeight_tendsto (z : UpperPlane) :
    Tendsto (exhaustionHeight z) atTop (𝓝 0) := by
  have h : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 2)) atTop (𝓝 0) :=
    by simpa only [Function.comp_def, Nat.cast_add,Nat.cast_ofNat] using
      (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).comp (tendsto_add_atTop_nat 2)
  change Tendsto (fun n : ℕ => z.1.im / ((n : ℝ) + 2)) atTop (𝓝 0)
  simpa only [mul_one_div,mul_zero] using h.const_mul z.1.im

noncomputable def exhaustionNorm (z : UpperPlane) (n : ℕ) : ℝ≥0 :=
  ⟨‖z.1‖ + n + 1, by positivity⟩

noncomputable def exhaustionStop (a : ℝ) (z : UpperPlane) (n : ℕ) : ExactSLEGenerator.Driver → ℝ≥0 :=
  regionStop a (exhaustionHeight z n) (exhaustionHeight_pos z n) z.1
    (exhaustionNorm z n) 0 0 n

lemma exhaustionRegion_initial (z : UpperPlane) (n : ℕ) :
    0 ≤ regionMonitor (exhaustionHeight z n) (exhaustionNorm z n) 0 0 (z.1,0) := by
  apply (regionMonitor_nonneg_iff _ _ _ _ _).mpr
  refine ⟨exhaustionHeight_le z n, ?_, ?_, ?_⟩
  · simp only [Prod.norm_def,norm_zero,max_eq_left (norm_nonneg z.1)]
    change ‖z.1‖ ≤ ‖z.1‖ + (n : ℝ) + 1
    linarith [Nat.cast_nonneg (α := ℝ) n]
  · simp only [physicalRadius,Y_apply,J_apply,neg_zero,Real.exp_zero,mul_one]
    exact z.2.le
  · simp only [zero_mul,Y_apply]
    exact z.2.le

lemma exhaustionStop_stopping (a : ℝ) (z : UpperPlane) (n : ℕ) :
    IsStoppingTime rawFiltration (fun b => (exhaustionStop a z n b : WithTop ℝ≥0)) :=
  regionStop_stopping a _ _ z.1 _ 0 0 n

lemma exhaustionStop_le (a : ℝ) (z : UpperPlane) (n : ℕ) (b : ExactSLEGenerator.Driver) :
    exhaustionStop a z n b ≤ n := regionStop_le a _ _ z.1 _ 0 0 n b

lemma exhaustionStop_agrees (a : ℝ) (z : UpperPlane) (n : ℕ)
    (b : ExactSLEGenerator.Driver) (t : ℝ≥0) (ht : t ≤ exhaustionStop a z n b) :
    alive a b.1 t z.1 ∧ actualState a b.1 t z.1 =
      localState a (exhaustionHeight z n) (exhaustionHeight_pos z n) z.1 t b :=
  regionStop_actualState a _ _ z.1 _ 0 0 n (exhaustionRegion_initial z n) b t ht

 

lemma exhaustionStop_eventually (a : ℝ) (z : UpperPlane) (b : ExactSLEGenerator.Driver) (t : ℝ≥0)
    (ht : alive a b.1 t z.1) :
    ∀ᶠ n in atTop, t ≤ exhaustionStop a z n b := by
  obtain ⟨η,C,hη,hbound⟩ := actualState_bounded_until b.1.continuous ht
  have hheight : ∀ᶠ n in atTop, exhaustionHeight z n < η :=
    (exhaustionHeight_tendsto z).eventually (gt_mem_nhds hη)
  have hlarge : ∀ᶠ n : ℕ in atTop, max (t : ℝ) C < n :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually (eventually_gt_atTop _)
  filter_upwards [hheight,hlarge] with n hn hlarge
  by_contra hnot
  have hs : exhaustionStop a z n b < t := lt_of_not_ge hnot
  have hsn : exhaustionStop a z n b < n :=
    hs.trans (by exact_mod_cast (lt_of_le_of_lt (le_max_left _ _) hlarge))
  have he := (exhaustionStop_agrees a z n b _ le_rfl).2
  have hb := hbound (exhaustionStop a z n b) hs.le
  have hcontact := regionStop_contact a _ (exhaustionHeight_pos z n) z.1
    (exhaustionNorm z n) 0 0 n (exhaustionRegion_initial z n) b hsn
  simp only [exhaustionStop] at he hb
  rw [← he] at hcontact
  rcases hcontact with h | h | h | h
  · linarith only [hb.1, h, hn]
  · have hCN : C < (exhaustionNorm z n : ℝ) := by
      change C < ‖z.1‖ + (n : ℝ) + 1
      have hCn := lt_of_le_of_lt (le_max_right (t : ℝ) C) hlarge
      linarith [norm_nonneg z.1]
    linarith only [hb.2,h,hCN]
  · have hp := physicalRadius_actual_pos a b z.1 _ (exhaustionStop_agrees a z n b _ le_rfl).1
    simp only [exhaustionStop] at hp
    rw [h] at hp
    exact lt_irrefl _ hp
  · simp only [zero_mul] at h
    linarith only [hb.1,h,hη]

lemma exhaustionStop_measurable (a : ℝ) (z : UpperPlane) (n : ℕ) :
    Measurable (exhaustionStop a z n) := by
  apply measurable_of_Iic
  intro t
  simpa only [preimage, mem_Iic, WithTop.coe_le_coe] using
    rawFiltration.le t _ ((exhaustionStop_stopping a z n).measurableSet_le t)

 

noncomputable def killedObservable (a : ℝ) (z : UpperPlane) (F : State → ℝ)
    (t : ℝ≥0) (b : ExactSLEGenerator.Driver) : ℝ :=
  if alive a b.1 t z.1 then F (actualState a b.1 t z.1) else 0

noncomputable def localizedObservable (a : ℝ) (z : UpperPlane) (F : State → ℝ)
    (n : ℕ) (t : ℝ≥0) (b : ExactSLEGenerator.Driver) : ℝ :=
  if t ≤ exhaustionStop a z n b then
    F (localState a (exhaustionHeight z n) (exhaustionHeight_pos z n) z.1 t b) else 0

lemma localizedObservable_joint_measurable (a : ℝ) (z : UpperPlane)
    (F : State → ℝ) (hF : Measurable F) (n : ℕ) :
    Measurable (fun p : ℝ≥0 × ExactSLEGenerator.Driver => localizedObservable a z F n p.1 p.2) := by
  exact Measurable.ite
    (measurableSet_le measurable_fst ((exhaustionStop_measurable a z n).comp measurable_snd))
    (hF.comp (localState_parameter_joint_measurable a (fun _ => exhaustionHeight z n)
      (fun _ => exhaustionHeight_pos z n) (fun _ => z.1) id
      measurable_const measurable_const measurable_id)) measurable_const

lemma localizedObservable_tendsto (a : ℝ) (z : UpperPlane) (F : State → ℝ)
    (t : ℝ≥0) (b : ExactSLEGenerator.Driver) :
    Tendsto (fun n => localizedObservable a z F n t b) atTop (𝓝 (killedObservable a z F t b)) := by
  by_cases ht : alive a b.1 t z.1
  · apply tendsto_const_nhds.congr'
    filter_upwards [exhaustionStop_eventually a z b t ht] with n hn
    simp only [localizedObservable,ite_eq_left hn,killedObservable,ite_eq_left ht,
      (exhaustionStop_agrees a z n b t hn).2]
  · have hn (n : ℕ) : ¬t ≤ exhaustionStop a z n b :=
      fun hn => ht (exhaustionStop_agrees a z n b t hn).1
    simpa only [localizedObservable,ite_eq_right (hn _),killedObservable,ite_eq_right ht] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))

lemma killedObservable_joint_measurable (a : ℝ) (z : UpperPlane)
    (F : State → ℝ) (hF : Measurable F) :
    Measurable (fun p : ℝ≥0 × ExactSLEGenerator.Driver => killedObservable a z F p.1 p.2) :=
  measurable_of_tendsto_metrizable (localizedObservable_joint_measurable a z F hF)
    (tendsto_pi_nhds.mpr (fun p => localizedObservable_tendsto a z F p.1 p.2))

lemma killedObservable_nonneg (a : ℝ) (z : UpperPlane)
    (F : State → ℝ) (hF : ∀ v, 0 < Y v → 0 ≤ F v)
    (t : ℝ≥0) (b : ExactSLEGenerator.Driver) : 0 ≤ killedObservable a z F t b := by
  unfold killedObservable
  split_ifs with ht
  · obtain ⟨f,hf⟩ := ht
    apply hF
    have he : loewnerMap a b.1 t z.1 = f t := by
      simpa only [Real.toNNReal_coe] using
        loewnerMap_eq_solution_time hf (right_mem_Icc.mpr t.coe_nonneg)
    simpa only [actualState,Y_apply,he,Complex.sub_im,Complex.ofReal_im,
      sub_zero] using (hf.2 (t : ℝ) (right_mem_Icc.mpr t.coe_nonneg)).1
  · exact le_rfl

lemma greenLifetime_measurable (a : ℝ) :
    Measurable (fun v => physicalGreen a v * lifetimeTest (lifetimeExponent a) v) := by
  unfold physicalGreen logGreen lifetimeTest Q X Y J
  fun_prop

lemma lifetimeCost_measurable (a : ℝ) : Measurable (lifetimeCost a) := by
  unfold lifetimeCost physicalGreen logGreen Q X Y J
  fun_prop

 

theorem global_lifetime_test_budget (a : ℝ) (ha : 1/4 < a)
    (W : Measure ExactSLEGenerator.Driver) [IsProbabilityMeasure W]
    (hW : IsBrownianReal (fun t (b : ExactSLEGenerator.Driver) => b.1 t) W)
    (z : UpperPlane) (t : ℝ≥0) :
    (∫⁻ b, ENNReal.ofReal (killedObservable a z
      (fun v => physicalGreen a v * lifetimeTest (lifetimeExponent a) v) t b) ∂W) ≤
      ENNReal.ofReal (physicalGreen a (z.1,0) * lifetimeTest (lifetimeExponent a) (z.1,0)) := by
  let F : State → ℝ := fun v => physicalGreen a v * lifetimeTest (lifetimeExponent a) v
  have hpos (v : State) (hv : 0 < Y v) : 0 ≤ F v :=
    mul_nonneg (Real.exp_pos _).le (lifetimeTest_nonneg _ _ hv.le)
  have hbound (n : ℕ) : (∫⁻ b, ENNReal.ofReal (localizedObservable a z F n t b) ∂W) ≤
      ENNReal.ofReal (F (z.1,0)) := by
    let ε := exhaustionHeight z n
    let V := localState a ε (exhaustionHeight_pos z n) z.1
    let S : ExactSLEGenerator.Driver → ℝ≥0 := fun b => min (exhaustionStop a z n b) t
    have hS : IsStoppingTime rawFiltration (fun b => (S b : WithTop ℝ≥0)) := by
      simpa only [S, WithTop.coe_min] using (exhaustionStop_stopping a z n).min_const t
    have hsafe (b : ExactSLEGenerator.Driver) (u : ℝ≥0) (hu : u ≤ S b) :
        ε ≤ Y (V u b) ∧ ‖V u b‖ ≤ exhaustionNorm z n := by
      have h := regionStop_safe a ε (exhaustionHeight_pos z n) z.1
        (exhaustionNorm z n) 0 0 n (exhaustionRegion_initial z n) b u
        (hu.trans (min_le_left _ _))
      exact ⟨h.1,h.2.1⟩
    have hb := local_lifetime_budget W hW a ε ha (exhaustionHeight_pos z n)
      z.1 (exhaustionNorm z n) n S hS
      (fun b => (min_le_left _ _).trans (exhaustionStop_le a z n b)) hsafe
    calc
      _ ≤ ∫⁻ b, ENNReal.ofReal (F (V (S b) b)) ∂W := by
        apply lintegral_mono
        intro b
        apply ENNReal.ofReal_le_ofReal
        by_cases ht : t ≤ exhaustionStop a z n b
        · simp only [localizedObservable,ite_eq_left ht,S,min_eq_right ht,F,V,ε,le_refl]
        · rw [localizedObservable,ite_eq_right ht]
          exact hpos _ ((exhaustionHeight_pos z n).trans_le (hsafe b (S b) le_rfl).1)
      _ = ENNReal.ofReal (∫ b, F (V (S b) b) ∂W) :=
        (ofReal_integral_eq_lintegral_ofReal hb.1 (Eventually.of_forall (fun b =>
          hpos _ ((exhaustionHeight_pos z n).trans_le (hsafe b (S b) le_rfl).1)))).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal hb.2.1
  have hlim (b : ExactSLEGenerator.Driver) :
      liminf (fun n => ENNReal.ofReal (localizedObservable a z F n t b)) atTop =
        ENNReal.ofReal (killedObservable a z F t b) :=
    (ENNReal.tendsto_ofReal (localizedObservable_tendsto a z F t b)).liminf_eq
  change (∫⁻ b, ENNReal.ofReal (killedObservable a z F t b) ∂W) ≤ _
  simp_rw [← hlim]
  exact (lintegral_liminf_le (fun n =>
    ((localizedObservable_joint_measurable a z F (greenLifetime_measurable a) n).comp
      (measurable_const.prodMk measurable_id)).ennreal_ofReal)).trans
    (liminf_le_of_frequently_le (Eventually.of_forall hbound).frequently)

lemma localizedObservable_occupation (a : ℝ) (z : UpperPlane) (F : State → ℝ)
    (n : ℕ) (b : ExactSLEGenerator.Driver) :
    (∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal (localizedObservable a z F n u.toNNReal b)) =
      ∫⁻ u in Ioc (0 : ℝ) (exhaustionStop a z n b : ℝ),
        ENNReal.ofReal (F (localState a (exhaustionHeight z n)
          (exhaustionHeight_pos z n) z.1 u.toNNReal b)) := by
  have he (u : ℝ) : ENNReal.ofReal (localizedObservable a z F n u.toNNReal b) =
      (Iic (exhaustionStop a z n b : ℝ)).indicator
        (fun u : ℝ => ENNReal.ofReal (F (localState a (exhaustionHeight z n)
          (exhaustionHeight_pos z n) z.1 u.toNNReal b))) u := by
    by_cases hu : u ≤ (exhaustionStop a z n b : ℝ)
    · simp only [localizedObservable,Real.toNNReal_le_iff_le_coe,indicator,mem_Iic,hu,ite_true]
    · simp only [localizedObservable,Real.toNNReal_le_iff_le_coe,indicator,mem_Iic,hu,ite_false,
        ENNReal.ofReal_zero]
  simp_rw [he]
  rw [setLIntegral_indicator measurableSet_Iic, inter_comm, Ioi_inter_Iic]

 

theorem global_lifetime_occupation_budget (a : ℝ) (ha : 1/4 < a)
    (W : Measure ExactSLEGenerator.Driver) [IsProbabilityMeasure W]
    (hW : IsBrownianReal (fun t (b : ExactSLEGenerator.Driver) => b.1 t) W)
    (z : UpperPlane) :
    (∫⁻ b, ∫⁻ u in Ioi (0 : ℝ),
      ENNReal.ofReal (killedObservable a z (lifetimeCost a) u.toNNReal b) ∂volume ∂W) ≤
      ENNReal.ofReal (physicalGreen a (z.1,0) * lifetimeTest (lifetimeExponent a) (z.1,0)) := by
  let G : ℕ → ExactSLEGenerator.Driver × ℝ → ℝ≥0∞ := fun n p =>
    ENNReal.ofReal (localizedObservable a z (lifetimeCost a) n p.2.toNNReal p.1)
  let H : ExactSLEGenerator.Driver × ℝ → ℝ≥0∞ := fun p =>
    ENNReal.ofReal (killedObservable a z (lifetimeCost a) p.2.toNNReal p.1)
  have hG (n : ℕ) : Measurable (G n) :=
    ((localizedObservable_joint_measurable a z (lifetimeCost a) (lifetimeCost_measurable a) n).comp
      ((measurable_real_toNNReal.comp measurable_snd).prodMk measurable_fst)).ennreal_ofReal
  have hH : Measurable H :=
    ((killedObservable_joint_measurable a z (lifetimeCost a) (lifetimeCost_measurable a)).comp
      ((measurable_real_toNNReal.comp measurable_snd).prodMk measurable_fst)).ennreal_ofReal
  have hbound (n : ℕ) :
      (∫⁻ p, G n p ∂W.prod (volume.restrict (Ioi (0 : ℝ)))) ≤
        ENNReal.ofReal (physicalGreen a (z.1,0) * lifetimeTest (lifetimeExponent a) (z.1,0)) := by
    rw [lintegral_prod _ (hG n).aemeasurable]
    change (∫⁻ b, ∫⁻ u in Ioi (0 : ℝ),
      ENNReal.ofReal (localizedObservable a z (lifetimeCost a) n u.toNNReal b) ∂volume ∂W) ≤ _
    simp_rw [localizedObservable_occupation]
    apply (local_lifetime_budget W hW a (exhaustionHeight z n) ha (exhaustionHeight_pos z n)
      z.1 (exhaustionNorm z n) n (exhaustionStop a z n) (exhaustionStop_stopping a z n)
      (exhaustionStop_le a z n) ?_).2.2
    intro b u hu
    have h := regionStop_safe a (exhaustionHeight z n) (exhaustionHeight_pos z n) z.1
      (exhaustionNorm z n) 0 0 n (exhaustionRegion_initial z n) b u hu
    exact ⟨h.1,h.2.1⟩
  have hlim (p : ExactSLEGenerator.Driver × ℝ) :
      liminf (fun n => G n p) atTop = H p :=
    (ENNReal.tendsto_ofReal (localizedObservable_tendsto a z (lifetimeCost a) p.2.toNNReal p.1)).liminf_eq
  rw [← lintegral_prod H hH.aemeasurable]
  simp_rw [← hlim]
  exact (lintegral_liminf_le hG).trans
    (liminf_le_of_frequently_le (Eventually.of_forall hbound).frequently)

end ExactSLEGreen
end

end OAI
