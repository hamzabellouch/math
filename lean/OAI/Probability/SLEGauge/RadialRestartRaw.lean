import Mathlib
import OAI.Probability.SLE.MomentGauge
import OAI.Probability.SLEGauge.RawRestartTests
import OAI.Probability.SLEGauge.FiniteAngleEigen

namespace OAI

/-! Hausdorff gauges, Loewner evolution and trace measures. -/

section
 

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical NNReal ENNReal Topology
namespace SLEExactGauge.LoewnerRestart
open FlowIdentification ExactSLEMain ExactSLEGreen ExactSLEGenerator

lemma radialState_raw_measurable (a : ℝ) (ha : 1/4<a) (z : ℂ) (hz : 0<z.im)
    (σ : ℝ) (hσ : 0<σ) (hσz : σ≤z.im) :
    Measurable[(radialTime_stopping a (by linarith) z hz σ hσ hσz).measurableSpace]
      (fun b : GDriver => radialState a b.1 z σ) := by
  let S := fun b : GDriver => radialTime a b.1 z σ
  have hS := radialTime_stopping a (by linarith) z hz σ hσ hσz
  have hD := stoppedData_raw_measurable hS
  have hm : Measurable[hS.measurableSpace] (fun b : GDriver =>
      killedState a (stoppedData S b).1 (stoppedData S b).2 z) :=
    (killedState_time_joint_measurable a ha).comp
      (hD.fst.prodMk (hD.snd.prodMk (measurable_const (a := (⟨z,hz⟩ : UpperPlane)))))
  have he (b : GDriver) : radialState a b.1 z σ =
      if S b=∞ then 0 else killedState a (stoppedData S b).1 (stoppedData S b).2 z := by
    by_cases hb : S b=∞
    · exact (ite_eq_left hb).trans (ite_eq_left hb).symm
    · have hs := (radialTime_attained a (by linarith) z hz σ hσ hσz b hb).1
      have hc := pastDriver_eq (S b).toNNReal b
      have hp := (alive_driver_congr hc).mpr hs
      rw [radialState,ite_eq_right hb,ite_eq_right hb]
      change actualState a b.1 (S b).toNNReal z =
        if alive a (pastDriver (S b).toNNReal b).1 (S b).toNNReal z then
          actualState a (pastDriver (S b).toNNReal b).1 (S b).toNNReal z else 0
      rw [ite_eq_left hp,actualState_driver_congr hc]
  simp_rw [he]
  exact Measurable.ite (hS.measurable (measurableSet_singleton ∞)) measurable_const hm

 

def radialPoint (a : ℝ) (z : ℂ) (σ : ℝ) (b : GDriver) : UpperPlane :=
  if h : 0<(radialState a b.1 z σ).1.im then ⟨(radialState a b.1 z σ).1,h⟩
  else ⟨Complex.I,by simp⟩

lemma radialPoint_raw_measurable (a : ℝ) (ha : 1/4<a) (z : ℂ) (hz : 0<z.im)
    (σ : ℝ) (hσ : 0<σ) (hσz : σ≤z.im) :
    Measurable[(radialTime_stopping a (by linarith) z hz σ hσ hσz).measurableSpace]
      (radialPoint a z σ) := by
  have hm := radialState_raw_measurable a ha z hz σ hσ hσz
  suffices Measurable[(radialTime_stopping a (by linarith) z hz σ hσ hσz).measurableSpace]
      (fun b : GDriver => (radialPoint a z σ b : ℂ)) from this.subtype_mk
  simp only [radialPoint,apply_dite,dite_eq_ite]
  exact hm.fst.ite (measurableSet_lt measurable_const hm.fst.im) measurable_const

lemma radialPoint_eq (a : ℝ) (ha : 0<a) (z : ℂ) (hz : 0<z.im)
    (σ : ℝ) (hσ : 0<σ) (hσz : σ≤z.im) (b : GDriver)
    (hb : radialTime a b.1 z σ≠∞) :
    (radialPoint a z σ b).1=(actualState a b.1 (radialTime a b.1 z σ).toNNReal z).1 := by
  have hs := (radialTime_attained a ha z hz σ hσ hσz b hb).1
  have hp : 0<(radialState a b.1 z σ).1.im := by
    simpa only [radialState,ite_eq_right hb,Y_apply] using LoewnerScaling.Y_actual_pos hs
  rw [radialPoint,dite_eq_left hp]
  simp only [radialState,ite_eq_right hb]

 
def radiusDensity (a : ℝ) (z : ℂ) (σ : ℝ) (b : GDriver) : ℝ≥0∞ :=
  ENNReal.ofReal (radialWeight a b.1 z σ / physicalGreen a (z,0))

lemma radiusDensity_raw_measurable (a : ℝ) (ha : 1/4<a) (z : ℂ) (hz : 0<z.im)
    (σ : ℝ) (hσ : 0<σ) (hσz : σ≤z.im) :
    Measurable[(radialTime_stopping a (by linarith) z hz σ hσ hσz).measurableSpace]
      (radiusDensity a z σ) := by
  have hS := radialTime_stopping a (by linarith) z hz σ hσ hσz
  have hm : Measurable[hS.measurableSpace] (fun b : GDriver => radialWeight a b.1 z σ) := by
    have he (b : GDriver) : radialWeight a b.1 z σ =
        if radialTime a b.1 z σ=∞ then 0 else physicalGreen a (radialState a b.1 z σ) := by
      unfold radialWeight radialState
      split_ifs <;> rfl
    simp_rw [he]
    apply Measurable.ite (hS.measurable (measurableSet_singleton ∞)) measurable_const
    exact (show Measurable (physicalGreen a) by unfold physicalGreen logGreen Q; fun_prop).comp
      (radialState_raw_measurable a ha z hz σ hσ hσz)
  exact (hm.div_const _).ennreal_ofReal

lemma radiusDensity_measurable (a : ℝ) (ha : 1/4<a) (z : ℂ) (hz : 0<z.im)
    (σ : ℝ) (hσ : 0<σ) (hσz : σ≤z.im) : Measurable (radiusDensity a z σ) :=
  (radiusDensity_raw_measurable a ha z hz σ hσ hσz).mono
    (radialTime_stopping a (by linarith) z hz σ hσ hσz).measurableSpace_le le_rfl

lemma joint_radiusDensity_measurable (a : ℝ) (ha : 1/4<a) (q : ℝ)
    (hq : 0<q) (hq1 : q≤1) :
    Measurable (fun p : GDriver×UpperPlane => radiusDensity a p.2.1 (p.2.1.im*q) p.1) := by
  apply Measurable.ennreal_ofReal
  apply (joint_radialWeight_measurable a ha q hq hq1).div
  unfold physicalGreen logGreen Q
  fun_prop

lemma radiusDensity_eq_zero (a : ℝ) (z : ℂ) (σ : ℝ) (b : GDriver)
    (hb : radialTime a b.1 z σ=∞) : radiusDensity a z σ b=0 := by
  simp only [radiusDensity,radialWeight,ite_eq_left hb,zero_div,ENNReal.ofReal_zero]

lemma radiusDensity_restart (a : ℝ) (ha : 1/4<a) (z : ℂ) (hz : 0<z.im)
    (σ ρ : ℝ) (hρ : 0<ρ) (hρσ : ρ≤σ) (hσ : σ≤z.im) (b : GDriver) :
    radiusDensity a z ρ b = radiusDensity a z σ b *
      radiusDensity a (radialPoint a z σ b).1 ((radialPoint a z σ b).1.im*(ρ/σ))
        (restartAt (fun c => radialTime a c.1 z σ) b) := by
  have ha0 : 0<a := by linarith
  by_cases hb : radialTime a b.1 z σ=∞
  · have hf : radialTime a b.1 z ρ=∞ := top_le_iff.mp
      (hb ▸ radialTime_antitone a ha0 z hz ρ σ hρ hρσ hσ b)
    rw [radiusDensity_eq_zero a z σ b hb,radiusDensity_eq_zero a z ρ b hf,zero_mul]
  · rw [radialPoint_eq a ha0 z hz σ (hρ.trans_le hρσ) hσ b hb]
    unfold radiusDensity restartAt
    rw [radialWeight_restart a ha0 z hz σ ρ hρ hρσ hσ b hb]
    have hp : 0≤radialWeight a b.1 z σ / physicalGreen a (z,0) :=
      div_nonneg (radialWeight_bound a ha z hz σ (hρ.trans_le hρσ) hσ b).1 (Real.exp_pos _).le
    rw [←ENNReal.ofReal_mul hp]
    congr 1
    ring

lemma finiteAngle_restart (a : ℝ) (ha : 0<a) (z : ℂ) (hz : 0<z.im)
    (σ ρ : ℝ) (hρ : 0<ρ) (hρσ : ρ≤σ) (hσ : σ≤z.im) (b : GDriver)
    (hf : radialTime a b.1 z ρ≠∞) :
    Jacobi.finiteAngle a z ρ b =
      Jacobi.finiteAngle a (radialPoint a z σ b).1 ((radialPoint a z σ b).1.im*(ρ/σ))
        (restartAt (fun c => radialTime a c.1 z σ) b) := by
  have hb := ne_top_of_le_ne_top hf (radialTime_antitone a ha z hz ρ σ hρ hρσ hσ b)
  let s := (radialTime a b.1 z σ).toNNReal
  let w := (actualState a b.1 s z).1
  let τ := radialTime a (restart s b).1 w (w.im*(ρ/σ))
  have hτ : τ≠∞ := (radialTime_restart_top_iff a ha z hz σ ρ hρ hρσ hσ b hb).not.mpr hf
  have ht : s+τ.toNNReal=(radialTime a b.1 z ρ).toNNReal := by
    have hh := congrArg ENNReal.toNNReal (radialTime_restart a ha z hz σ ρ hρ hρσ hσ b hb)
    change ((s:ℝ≥0∞)+τ).toNNReal=(radialTime a b.1 z ρ).toNNReal at hh
    simpa only [ENNReal.toNNReal_add ENNReal.coe_ne_top hτ,ENNReal.toNNReal_coe] using hh
  have hs := (radialTime_attained a ha z hz ρ hρ (hρσ.trans hσ) b hf).1
  rw [radialPoint_eq a ha z hz σ (hρ.trans_le hρσ) hσ b hb]
  apply Subtype.ext
  change physicalTheta (radialState a b.1 z ρ) =
    physicalTheta (radialState a (restart s b).1 w (w.im*(ρ/σ)))
  rw [radialState,ite_eq_right hf,radialState,ite_eq_right hτ,←ht,
    actualState_restart b.1.continuous (ht ▸ hs)]
  rfl

end SLEExactGauge.LoewnerRestart
end
end
 

 
section
 

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology
namespace SLEExactGauge.LoewnerRestart
open FlowIdentification ExactSLEMain ExactSLEGreen ExactSLEGenerator

lemma setLIntegral_eq_inter_of_zero {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (A B : Set Ω) (hB : MeasurableSet B) (f : Ω→ℝ≥0∞)
    (hf : ∀ b, b∉B → f b=0) : (∫⁻b in A,f b∂μ)=∫⁻b in A∩B,f b∂μ := by
  have he : f=B.indicator f := by
    funext b
    by_cases hb : b∈B
    · simp only [indicator_of_mem hb]
    · simp only [indicator_of_notMem hb,hf b hb]
  calc
    _ = ∫⁻b in A,B.indicator f b∂μ := by rw [←he]
    _ = ∫⁻b in A∩B,f b∂μ := by
      rw [lintegral_indicator hB,Measure.restrict_restrict hB,inter_comm]

lemma radial_hit_ae (W : Measure GDriver) (a : ℝ) (ha : 1/4<a) (z : ℂ) (hz : 0<z.im)
    (ρ : ℝ) (hρ : 0<ρ) (hr : ρ≤z.im) :
    ∀ᵐ b∂radialLaw W a z ρ,radialTime a b.1 z ρ≠∞ := by
  rw [radialLaw]
  apply (ae_withDensity_iff (radiusDensity_measurable a ha z hz ρ hρ hr)).mpr
  exact Eventually.of_forall (fun b hb hf => hb (radiusDensity_eq_zero a z ρ b hf))

 

theorem radialLaw_restart (W : Measure GDriver)
    (hW : IsBrownianReal (fun t (b : GDriver) => b.1 t) W)
    (a : ℝ) (ha : 1/4<a) (z : ℂ) (hz : 0<z.im)
    (σ ρ : ℝ) (hρ : 0<ρ) (hρσ : ρ≤σ) (hσ : σ≤z.im)
    (A : Set GDriver)
    (hA : MeasurableSet[(radialTime_stopping a (by linarith) z hz σ (hρ.trans_le hρσ) hσ).measurableSpace] A)
    (F : UpperPlane×GDriver→ℝ≥0∞) (hF : Measurable F) :
    (∫⁻b in A,F (radialPoint a z σ b,restartAt (fun c => radialTime a c.1 z σ) b)
      ∂radialLaw W a z ρ) =
    ∫⁻b in A,∫⁻c,F (radialPoint a z σ b,c)
      ∂radialLaw W a (radialPoint a z σ b).1 ((radialPoint a z σ b).1.im*(ρ/σ))
      ∂radialLaw W a z σ := by
  let := hW.isGaussianProcess.isProbabilityMeasure
  have hσ0 := hρ.trans_le hρσ
  have hS := radialTime_stopping a (by linarith) z hz σ hσ0 hσ
  let S : GDriver→ℝ≥0∞ := fun b => radialTime a b.1 z σ
  let Z := radialPoint a z σ
  let D : GDriver→ℝ≥0∞×UpperPlane := fun b => (radiusDensity a z σ b,Z b)
  have hD : Measurable[hS.measurableSpace] D :=
    (radiusDensity_raw_measurable a ha z hz σ hσ0 hσ).prodMk
      (radialPoint_raw_measurable a ha z hz σ hσ0 hσ)
  have hZ : Measurable Z := (radialPoint_raw_measurable a ha z hz σ hσ0 hσ).mono
    hS.measurableSpace_le le_rfl
  have hY := measurable_restartAt hS
  have hA' : MeasurableSet A := hS.measurableSpace_le _ hA
  have hhit : MeasurableSet {b : GDriver | S b≠∞} :=
    (hS.measurable' (measurableSet_singleton ∞)).compl
  have hq : 0<ρ/σ := div_pos hρ hσ0
  have hq1 : ρ/σ≤1 := (div_le_one hσ0).mpr hρσ
  let K : UpperPlane×GDriver→ℝ≥0∞ := fun p =>
    radiusDensity a p.1.1 (p.1.1.im*(ρ/σ)) p.2 * F p
  have hK : Measurable K :=
    ((joint_radiusDensity_measurable a ha (ρ/σ) hq hq1).comp measurable_swap).mul hF
  let H : (ℝ≥0∞×UpperPlane)×GDriver→ℝ≥0∞ := fun p => p.1.1*K (p.1.2,p.2)
  have hH : Measurable H := measurable_fst.fst.mul
    (hK.comp (measurable_fst.snd.prodMk measurable_snd))
  have he (b : GDriver) : radiusDensity a z ρ b * F (Z b,restartAt S b)=H (D b,restartAt S b) := by
    rw [radiusDensity_restart a ha z hz σ ρ hρ hρσ hσ]
    exact mul_assoc _ _ _
  have hi (b : GDriver) : (∫⁻c,H (D b,c)∂W)=radiusDensity a z σ b *
      ∫⁻c,F (Z b,c)∂radialLaw W a (Z b).1 ((Z b).1.im*(ρ/σ)) := by
    have hm : Measurable (fun c : GDriver => F (Z b,c)) :=
      hF.comp (measurable_const.prodMk measurable_id)
    have he' : (∫⁻c,F (Z b,c)∂radialLaw W a (Z b).1 ((Z b).1.im*(ρ/σ)))=
        ∫⁻c,K (Z b,c)∂W :=
      lintegral_withDensity_eq_lintegral_mul W
        (radiusDensity_measurable a ha (Z b).1 (Z b).2 _ (mul_pos (Z b).2 hq)
          (mul_le_of_le_one_right (Z b).2.le hq1)) hm
    rw [he']
    exact lintegral_const_mul _ (hK.comp (measurable_const.prodMk measurable_id))
  have hkm : Measurable (fun b => ∫⁻c,F (Z b,c)
      ∂radialLaw W a (Z b).1 ((Z b).1.im*(ρ/σ))) := by
    have he' (b : GDriver) : (∫⁻c,F (Z b,c)
        ∂radialLaw W a (Z b).1 ((Z b).1.im*(ρ/σ)))=∫⁻c,K (Z b,c)∂W := by
      exact lintegral_withDensity_eq_lintegral_mul W
        (radiusDensity_measurable a ha (Z b).1 (Z b).2 _ (mul_pos (Z b).2 hq)
          (mul_le_of_le_one_right (Z b).2.le hq1)) (hF.comp (measurable_const.prodMk measurable_id))
    simp_rw [he']
    exact hK.lintegral_prod_right'.comp hZ
  change (∫⁻b in A,F (Z b,restartAt S b)∂W.withDensity (radiusDensity a z ρ)) =
    ∫⁻b in A,∫⁻c,F (Z b,c)∂radialLaw W a (Z b).1 ((Z b).1.im*(ρ/σ))
      ∂W.withDensity (radiusDensity a z σ)
  have hfm : Measurable (fun b : GDriver => F (Z b,restartAt S b)) := hF.comp (hZ.prodMk hY)
  rw [setLIntegral_withDensity_eq_setLIntegral_mul W (radiusDensity_measurable a ha z hz ρ hρ (hρσ.trans hσ))
      hfm hA',
    setLIntegral_withDensity_eq_setLIntegral_mul W (radiusDensity_measurable a ha z hz σ hσ0 hσ) hkm hA']
  simp only [Pi.mul_apply,he,←hi]
  calc
    _ = ∫⁻b in A∩{b | S b≠∞},H (D b,restartAt S b)∂W :=
      setLIntegral_eq_inter_of_zero W A _ hhit _ (fun b hb => by
        have hb' : S b=∞ := not_not.mp hb
        simp only [H,D,radiusDensity_eq_zero a z σ b hb',zero_mul])
    _ = ∫⁻b in A∩{b | S b≠∞},∫⁻c,H (D b,c)∂W ∂W :=
      lintegral_data_restartAt_on hW hS hD hA hH
    _ = ∫⁻b in A,∫⁻c,H (D b,c)∂W ∂W :=
      (setLIntegral_eq_inter_of_zero W A _ hhit _ (fun b hb => by
        have hb' : S b=∞ := not_not.mp hb
        simp only [H,D,radiusDensity_eq_zero a z σ b hb',zero_mul,lintegral_zero])).symm

 
theorem finiteAngle_conditional (W : Measure GDriver)
    (hW : IsBrownianReal (fun t (b : GDriver) => b.1 t) W)
    (a : ℝ) (ha : 1/4<a) (z : ℂ) (hz : 0<z.im)
    (σ ρ : ℝ) (hρ : 0<ρ) (hρσ : ρ≤σ) (hσ : σ≤z.im)
    (A : Set GDriver)
    (hA : MeasurableSet[(radialTime_stopping a (by linarith) z hz σ (hρ.trans_le hρσ) hσ).measurableSpace] A)
    (f : CenteredMoments.Angle→ℝ≥0∞) (hf : Measurable f) :
    (∫⁻b in A,f (Jacobi.finiteAngle a z ρ b)∂radialLaw W a z ρ) =
    ∫⁻b in A,∫⁻c,f (Jacobi.finiteAngle a (radialPoint a z σ b).1
      ((radialPoint a z σ b).1.im*(ρ/σ)) c)
      ∂radialLaw W a (radialPoint a z σ b).1 ((radialPoint a z σ b).1.im*(ρ/σ))
      ∂radialLaw W a z σ := by
  have hq : 0<ρ/σ := div_pos hρ (hρ.trans_le hρσ)
  have hq1 : ρ/σ≤1 := (div_le_one (hρ.trans_le hρσ)).mpr hρσ
  let F : UpperPlane×GDriver→ℝ≥0∞ := fun p => f (Jacobi.finiteAngle a p.1.1 (p.1.1.im*(ρ/σ)) p.2)
  have hF : Measurable F := hf.comp (Jacobi.angleState_measurable.comp
    ((joint_radialState_measurable a (by linarith) (ρ/σ) hq hq1).comp measurable_swap))
  rw [←radialLaw_restart W hW a ha z hz σ ρ hρ hρσ hσ A hA F hF]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_of_ae (radial_hit_ae W a ha z hz ρ hρ (hρσ.trans hσ))] with b hb
  exact congrArg f (finiteAngle_restart a (by linarith) z hz σ ρ hρ hρσ hσ b hb)

end SLEExactGauge.LoewnerRestart
end
end
 

 
section
 

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
namespace SLEExactGauge.Jacobi
open CenteredMoments ExactSLEGreen ExactSLECalculus ExactSLEFiniteTilt ExactSLEGenerator ExactSLEMain

lemma sin_physicalTheta (v : State) (hy : 0 < Y v) :
    Real.sin (physicalTheta v) = Y v / ‖v.1‖ := by
  have hn : 0 < ‖v.1‖ := hy.trans_le (Complex.im_le_norm _)
  have hs := Real.sin_pos_of_pos_of_lt_pi (physicalTheta_mem v).1 (physicalTheta_mem v).2
  have hc := physicalTheta_cot v
  rw [Real.cot_eq_cos_div_sin, div_eq_div_iff hs.ne' hy.ne'] at hc
  have he : (X v)^2 + (Y v)^2 = ‖v.1‖^2 := by
    simpa only [X_apply, Y_apply, Complex.normSq_apply, pow_two] using Complex.normSq_eq_norm_sq v.1
  have hid := Real.sin_sq_add_cos_sq (physicalTheta v)
  have heq : (Real.sin (physicalTheta v) * ‖v.1‖)^2 = (Y v)^2 := by
    nlinarith [sq_nonneg (Real.sin (physicalTheta v) * X v - Real.cos (physicalTheta v) * Y v),
      congrArg (fun x : ℝ => x^2) hc,
      congrArg (fun x : ℝ => x * (Y v)^2) hid,
      congrArg (fun x : ℝ => x * (Real.sin (physicalTheta v))^2) he]
  apply (eq_div_iff hn.ne').mpr
  nlinarith [mul_pos hs hn]

 
lemma radialWeight_inverse_sine (a : ℝ) (ha : 0 < a) (z : ℂ) (hz : 0 < z.im)
    (ρ : ℝ) (hρ : 0 < ρ) (hr : ρ ≤ z.im) (b : ExactSLEGenerator.Driver)
    (hb : radialTime a b.1 z ρ ≠ ∞) :
    radialWeight a b.1 z ρ * (Real.sin (finiteAngle a z ρ b : ℝ)) ^ (-p a) =
      ρ ^ (-alpha a) := by
  have ht := radialTime_attained a ha z hz ρ hρ hr b hb
  have hy := LoewnerScaling.Y_actual_pos ht.1
  have hs := Real.sin_pos_of_pos_of_lt_pi (finiteAngle a z ρ b).2.1
    (finiteAngle a z ρ b).2.2
  have hθ : Real.sin (finiteAngle a z ρ b : ℝ) =
      Y (actualState a b.1 (radialTime a b.1 z ρ).toNNReal z) /
        ‖(actualState a b.1 (radialTime a b.1 z ρ).toNNReal z).1‖ := by
    simpa only [finiteAngle, angleState, radialState, ite_eq_right hb] using sin_physicalTheta _ hy
  rw [radialWeight, ite_eq_right hb, physicalGreen_eq_radius_sine a _ hy, ht.2, ← hθ,
    mul_assoc, ← Real.rpow_add hs]
  simp

lemma inverse_radial_density (a : ℝ) (ha : 0 < a) (z : ℂ) (hz : 0 < z.im)
    (ρ : ℝ) (hρ : 0 < ρ) (hr : ρ ≤ z.im) (b : ExactSLEGenerator.Driver) :
    (ρ^(alpha a) * physicalGreen a (z,0)) *
        ((radialWeight a b.1 z ρ / physicalGreen a (z,0)) *
          (Real.sin (finiteAngle a z ρ b : ℝ))^(-p a)) =
      if radialTime a b.1 z ρ ≠ ∞ then 1 else 0 := by
  by_cases hb : radialTime a b.1 z ρ ≠ ∞
  · rw [ite_eq_left hb]
    have hp : physicalGreen a (z,0) ≠ 0 := (Real.exp_pos _).ne'
    calc
      _ = ρ^(alpha a) * (radialWeight a b.1 z ρ *
          (Real.sin (finiteAngle a z ρ b : ℝ))^(-p a)) := by field_simp
      _ = 1 := by
        rw [radialWeight_inverse_sine a ha z hz ρ hρ hr b hb, ← Real.rpow_add hρ]
        simp
  · simp only [ite_eq_right hb, radialWeight, ite_eq_left (not_not.mp hb), zero_div, zero_mul, mul_zero]

 

theorem radial_change_law (W : Measure ExactSLEGenerator.Driver)
    (a : ℝ) (ha : 1/4 < a) (z : ℂ) (hz : 0 < z.im)
    (ρ : ℝ) (hρ : 0 < ρ) (hr : ρ ≤ z.im)
    (g : ExactSLEGenerator.Driver → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻b in {b | radialTime a b.1 z ρ ≠ ∞}, g b ∂W) =
      ENNReal.ofReal (ρ^(alpha a) * physicalGreen a (z,0)) *
        ∫⁻b, ENNReal.ofReal ((Real.sin (finiteAngle a z ρ b : ℝ))^(-p a)) * g b
          ∂radialLaw W a z ρ := by
  have ha0 : 0 < a := by linarith
  have hhit : MeasurableSet {b : ExactSLEGenerator.Driver | radialTime a b.1 z ρ ≠ ∞} :=
    ((radialTime_stopping a ha0 z hz ρ hρ hr).measurable' (measurableSet_singleton ∞)).compl
  have hs : Measurable (fun b : ExactSLEGenerator.Driver =>
      ENNReal.ofReal ((Real.sin (finiteAngle a z ρ b : ℝ))^(-p a))) := by
    exact (show Measurable (fun θ : Angle => ENNReal.ofReal ((Real.sin θ)^(-p a))) by fun_prop).comp
      (finiteAngle_measurable a ha0 z hz ρ hρ hr)
  have hd : Measurable (fun b : ExactSLEGenerator.Driver =>
      ENNReal.ofReal (radialWeight a b.1 z ρ / physicalGreen a (z,0))) :=
    ((radialWeight_measurable a ha z hz ρ hρ hr).div_const _).ennreal_ofReal
  have hf : Measurable (fun b =>
      ENNReal.ofReal ((Real.sin (finiteAngle a z ρ b : ℝ))^(-p a)) * g b) := hs.mul hg
  rw [radialLaw, lintegral_withDensity_eq_lintegral_mul W hd hf, ← lintegral_const_mul _ (hd.mul hf)]
  rw [← lintegral_indicator hhit]
  apply lintegral_congr
  intro b
  have hpos : 0 ≤ (radialWeight a b.1 z ρ / physicalGreen a (z,0)) :=
    div_nonneg (radialWeight_bound a ha z hz ρ hρ hr b).1 (Real.exp_pos _).le
  have hc : 0 ≤ ρ^(alpha a) * physicalGreen a (z,0) :=
    mul_nonneg (Real.rpow_nonneg hρ.le _) (Real.exp_pos _).le
  have he := congrArg ENNReal.ofReal (inverse_radial_density a ha0 z hz ρ hρ hr b)
  rw [ENNReal.ofReal_mul hc, ENNReal.ofReal_mul hpos] at he
  simp only [Pi.mul_apply]
  rw [← mul_assoc _ _ (g b), ← mul_assoc _ _ (g b), he]
  by_cases hb : radialTime a b.1 z ρ ≠ ∞ <;> simp [hb]

lemma radial_hit_probability_eq (W : Measure ExactSLEGenerator.Driver)
    (a : ℝ) (ha : 1/4 < a) (z : ℂ) (hz : 0 < z.im)
    (s : ℝ) (hs : 0 ≤ s) :
    W {b | radialTime a b.1 z (levelRadius a (2*z.im) s) ≠ ∞} =
      ENNReal.ofReal ((levelRadius a (2*z.im) s)^(alpha a) * physicalGreen a (z,0)) *
        ∫⁻θ : Angle, ENNReal.ofReal ((Real.sin θ)^(-p a)) ∂finiteAngleLaw W a z s := by
  have hρ := levelRadius_pos a (2*z.im) s (by positivity : 0 < 2*z.im)
  have hr := levelRadius_initial_le a (by linarith) z hz s hs
  have he := radial_change_law W a ha z hz _ hρ hr (fun _ => 1) measurable_const
  simp only [lintegral_one, Measure.restrict_apply_univ, mul_one] at he
  rw [finiteAngleLaw, lintegral_map (by fun_prop)
    (finiteAngle_measurable a (by linarith) z hz _ hρ hr)]
  exact he

lemma physicalGreen_initial_bound (a : ℝ) (ha : 1/4 < a) (z : ℂ) (hz : 0 < z.im) :
    physicalGreen a (z,0) ≤ z.im^(-alpha a) := by
  have hr : physicalRadius (z,0) = z.im := by simp [physicalRadius, Y_apply, J_apply]
  rw [Real.rpow_def_of_pos hz]
  simpa only [mul_comm] using physicalGreen_bound a z.im ha hz (z,0) hz hr.ge

 

theorem radial_hit_probability_long (W : Measure ExactSLEGenerator.Driver) [IsProbabilityMeasure W]
    (hW : IsBrownianReal (fun t (b : ExactSLEGenerator.Driver) => b.1 t) W)
    (a : ℝ) (ha : 1/4 < a) (z : ℂ) (hz : 0 < z.im)
    (s : ℝ) (hs : mixingTime (4*a) ≤ s) :
    W {b | radialTime a b.1 z (levelRadius a (2*z.im) s) ≠ ∞} ≤
      ENNReal.ofReal ((levelRadius a (2*z.im) s / z.im)^(alpha a)) *
        (2 * ∫⁻θ : Angle, ENNReal.ofReal ((Real.sin θ)^(-p a)) ∂angleLaw a) := by
  have hs0 : 0 ≤ s := le_trans (by unfold mixingTime majorantBase; positivity) hs
  have hρ := levelRadius_pos a (2*z.im) s (by positivity : 0 < 2*z.im)
  rw [radial_hit_probability_eq W a ha z hz s hs0]
  apply mul_le_mul
  · apply ENNReal.ofReal_le_ofReal
    rw [Real.div_rpow hρ.le hz.le, div_eq_mul_inv, ← Real.rpow_neg hz.le]
    exact mul_le_mul_of_nonneg_left (physicalGreen_initial_bound a ha z hz)
      (Real.rpow_nonneg hρ.le _)
  · exact (finiteAngleLaw_integral_bounds W hW a ha z hz s hs _ (by fun_prop)).2
  all_goals positivity

 
def visitConstant (a : ℝ) : ℝ≥0∞ :=
  2 * (∫⁻θ : Angle, ENNReal.ofReal ((Real.sin θ)^(-p a)) ∂angleLaw a) +
    ENNReal.ofReal (Real.exp (2*a*mixingTime (4*a)*alpha a))

lemma visitConstant_lt_top (a : ℝ) : visitConstant a < ∞ :=
  ENNReal.add_lt_top.mpr ⟨ENNReal.mul_lt_top (by norm_num) (angle_inverse_power_finite a),
    ENNReal.ofReal_lt_top⟩

lemma visitConstant_pos (a : ℝ) : 0 < visitConstant a :=
  lt_of_lt_of_le (ENNReal.ofReal_pos.mpr (Real.exp_pos _)) (le_add_left le_rfl)

lemma levelRadius_ratio (a : ℝ) (z : ℂ) (hz : 0 < z.im) (s : ℝ) :
    levelRadius a (2*z.im) s / z.im = Real.exp (-2*a*s) := by
  unfold levelRadius
  field_simp

 

theorem radial_hit_probability (W : Measure ExactSLEGenerator.Driver) [IsProbabilityMeasure W]
    (hW : IsBrownianReal (fun t (b : ExactSLEGenerator.Driver) => b.1 t) W)
    (a : ℝ) (ha : 1/4 < a) (z : ℂ) (hz : 0 < z.im) (s : ℝ) (_hs : 0 ≤ s) :
    W {b | radialTime a b.1 z (levelRadius a (2*z.im) s) ≠ ∞} ≤
      visitConstant a * ENNReal.ofReal ((levelRadius a (2*z.im) s / z.im)^(alpha a)) := by
  by_cases hm : mixingTime (4*a) ≤ s
  · exact (radial_hit_probability_long W hW a ha z hz s hm).trans (by
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_right (le_add_right le_rfl) zero_le)
  · have hh : ENNReal.ofReal (Real.exp (2*a*mixingTime (4*a)*alpha a)) *
        ENNReal.ofReal ((levelRadius a (2*z.im) s / z.im)^(alpha a)) ≥ 1 := by
      rw [levelRadius_ratio a z hz s, ← ENNReal.ofReal_mul (Real.exp_pos _).le,
        ← Real.exp_mul, ← Real.exp_add, ← ENNReal.ofReal_one]
      apply ENNReal.ofReal_le_ofReal
      rw [Real.one_le_exp_iff]
      have hp := alpha_pos ha
      nlinarith [mul_nonneg (show 0 ≤ 2*a by linarith)
        (sub_nonneg.mpr (not_le.mp hm).le)]
    exact (prob_le_one (μ := W)).trans (hh.trans
      (mul_le_mul_of_nonneg_right (le_add_left le_rfl) zero_le))

 
theorem radial_hit_probability_radius (W : Measure ExactSLEGenerator.Driver) [IsProbabilityMeasure W]
    (hW : IsBrownianReal (fun t (b : ExactSLEGenerator.Driver) => b.1 t) W)
    (a : ℝ) (ha : 1/4 < a) (z : ℂ) (hz : 0 < z.im)
    (ρ : ℝ) (hρ : 0 < ρ) (hr : ρ ≤ z.im) :
    W {b | radialTime a b.1 z ρ ≠ ∞} ≤ visitConstant a * ENNReal.ofReal ((ρ/z.im)^(alpha a)) := by
  let s : ℝ := -(Real.log (ρ/z.im))/(2*a)
  have ha0 : 0 < a := by linarith
  have hq : 0 < ρ/z.im := div_pos hρ hz
  have hs : 0 ≤ s := div_nonneg (neg_nonneg.mpr (Real.log_nonpos hq.le ((div_le_one hz).mpr hr)))
    (by positivity)
  have he : levelRadius a (2*z.im) s = ρ := by
    have hexp : -2*a*s = Real.log (ρ/z.im) := by dsimp [s]; field_simp
    unfold levelRadius
    rw [hexp, Real.exp_log hq]
    field_simp
  simpa only [he] using radial_hit_probability W hW a ha z hz s hs

end SLEExactGauge.Jacobi
end
end

end OAI
