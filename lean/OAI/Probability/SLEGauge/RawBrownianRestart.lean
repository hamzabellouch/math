import Mathlib
import OAI.Probability.SLE.MomentGauge
import OAI.Probability.SLEGauge.BrownianRestart
import OAI.Probability.SLEGauge.SurvivalLocalization
import OAI.Probability.SLEGauge.LoewnerScaling

namespace OAI

/-! Hausdorff gauges, Loewner evolution and trace measures. -/

section
 

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology Function
open scoped NNReal ENNReal ContinuousMapZero BoundedContinuousFunction
namespace SLEExactGauge.LoewnerRestart
open FlowIdentification ExactSLEGenerator ExactSLEMain

 
def restart (t : ℝ≥0) (b : GDriver) : GDriver :=
  driverHomeomorph (BrownianRestart.shift t (driverHomeomorph.symm b))

@[simp] lemma restart_apply (t u : ℝ≥0) (b : GDriver) :
    (restart t b).1 u=b.1 (t+u)-b.1 t := rfl

lemma continuous_restart_joint : Continuous (fun p : ℝ≥0×GDriver => restart p.1 p.2) :=
  driverHomeomorph.continuous.comp (BrownianRestart.continuous_shift_joint.comp
    (continuous_fst.prodMk (driverHomeomorph.symm.continuous.comp continuous_snd)))

 
def restartAt (S : GDriver→ℝ≥0∞) (b : GDriver) : GDriver := restart (S b).toNNReal b

lemma comap_rawFiltration (t : ℝ≥0) :
    MeasurableSpace.comap driverHomeomorph (rawFiltration t)=BrownianRestart.filtration t := by
  simp only [rawFiltration,BrownianRestart.filtration,Filtration.natural_eq_comap,
    MeasurableSpace.comap_comp]
  rfl

lemma measurable_driver_raw (t : ℝ≥0) :
    @Measurable TDriver GDriver (BrownianRestart.filtration t) (rawFiltration t) driverHomeomorph :=
  measurable_iff_comap_le.mpr (comap_rawFiltration t).le

lemma measurable_driver_raw_all :
    @Measurable TDriver GDriver (⨆t,BrownianRestart.filtration t) (⨆t,rawFiltration t) driverHomeomorph := by
  apply measurable_iff_comap_le.mpr
  simp only [MeasurableSpace.comap_iSup,comap_rawFiltration,le_refl]

lemma stoppingTime_transport {S : GDriver→ℝ≥0∞} (hS : IsStoppingTime rawFiltration S) :
    IsStoppingTime BrownianRestart.filtration (S ∘ driverHomeomorph) := by
  intro t
  exact measurable_driver_raw t (hS t)

lemma measurable_driver_stopped {S : GDriver→ℝ≥0∞} (hS : IsStoppingTime rawFiltration S) :
    @Measurable TDriver GDriver (stoppingTime_transport hS).measurableSpace hS.measurableSpace
      driverHomeomorph := by
  intro A hA
  refine ⟨measurable_driver_raw_all hA.1,fun t => ?_⟩
  exact measurable_driver_raw t (hA.2 t)

lemma measurable_restartAt {S : GDriver→ℝ≥0∞} (hS : IsStoppingTime rawFiltration S) :
    Measurable (restartAt S) :=
  continuous_restart_joint.measurable.comp
    ((ENNReal.measurable_toNNReal.comp hS.measurable').prodMk measurable_id)

lemma restartAt_transport (S : GDriver→ℝ≥0∞) (b : TDriver) :
    driverHomeomorph (BrownianRestart.shiftAt (S ∘ driverHomeomorph) b)=
      restartAt S (driverHomeomorph b) := by
  simp only [restartAt,restart,BrownianRestart.shiftAt,Function.comp_apply,
    Homeomorph.symm_apply_apply]

lemma setIntegral_restartAt {W : Measure GDriver}
    (hW : IsBrownianReal (fun t (b : GDriver) => b.1 t) W)
    {S : GDriver→ℝ≥0∞} (hS : IsStoppingTime rawFiltration S)
    {A : Set GDriver} (hA : MeasurableSet[hS.measurableSpace] A) (f : GDriver→ᵇℝ) :
    (∫b in A ∩ {b | S b≠∞}, f (restartAt S b) ∂W)=
      ∫_b in A ∩ {b | S b≠∞}, (∫b,f b∂W) ∂W := by
  have h := BrownianRestart.setIntegral_shiftAt_finite
    (LoewnerScaling.brownian_map_inverse_driver W hW) (stoppingTime_transport hS)
    (measurable_driver_stopped hS hA) (f.compContinuous ⟨driverHomeomorph,driverHomeomorph.continuous⟩)
  have hm : MeasurableEmbedding driverHomeomorph.symm :=
    driverMeasurableEquiv.symm.measurableEmbedding
  rw [hm.setIntegral_map,hm.setIntegral_map,hm.integral_map] at h
  change
    (∫b in driverHomeomorph.symm ⁻¹' (driverHomeomorph ⁻¹' A ∩
      {b | S (driverHomeomorph b)≠∞}),
      f (driverHomeomorph (BrownianRestart.shiftAt
        (fun b => S (driverHomeomorph b)) (driverHomeomorph.symm b))) ∂W)=
    ∫_b in driverHomeomorph.symm ⁻¹' (driverHomeomorph ⁻¹' A ∩
      {b | S (driverHomeomorph b)≠∞}),
      (∫b,f (driverHomeomorph (driverHomeomorph.symm b))∂W) ∂W at h
  have hA' : driverHomeomorph.symm ⁻¹' (driverHomeomorph ⁻¹' A)=A := by
    ext b
    change driverHomeomorph (driverHomeomorph.symm b) ∈ A ↔ b∈A
    rw [driverHomeomorph.apply_symm_apply]
  simpa [restartAt,restart,BrownianRestart.shiftAt,hA'] using h

 

theorem map_restartAt_restrict {W : Measure GDriver}
    (hW : IsBrownianReal (fun t (b : GDriver) => b.1 t) W)
    {S : GDriver→ℝ≥0∞} (hS : IsStoppingTime rawFiltration S)
    {A : Set GDriver} (hA : MeasurableSet[hS.measurableSpace] A) :
    (W.restrict (A ∩ {b | S b≠∞})).map (restartAt S)=W (A ∩ {b | S b≠∞}) • W := by
  let := hW.isGaussianProcess.isProbabilityMeasure
  have : IsFiniteMeasure (W (A ∩ {b | S b≠∞}) • W) := W.smul_finite (measure_ne_top W _)
  have : PolishSpace GDriver := (isClosed_eq (continuous_eval_const 0) continuous_const).polishSpace
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  rw [integral_map (measurable_restartAt hS).aemeasurable f.continuous.aestronglyMeasurable,
    setIntegral_restartAt hW hS hA f,integral_smul_measure]
  simp only [integral_const,measureReal_def,Measure.restrict_apply_univ]

 

theorem map_data_restartAt {X : Type*} [MeasurableSpace X] {W : Measure GDriver}
    (hW : IsBrownianReal (fun t (b : GDriver) => b.1 t) W)
    {S : GDriver→ℝ≥0∞} (hS : IsStoppingTime rawFiltration S)
    {D : GDriver→X} (hD : Measurable[hS.measurableSpace] D) :
    (W.restrict {b | S b≠∞}).map (fun b => (D b,restartAt S b))=
      ((W.restrict {b | S b≠∞}).map D).prod W := by
  let := hW.isGaussianProcess.isProbabilityMeasure
  have hD' : Measurable D := hD.mono hS.measurableSpace_le le_rfl
  have hY := measurable_restartAt hS
  apply Measure.ext_prod
  intro A B hA hB
  rw [Measure.map_apply (hD'.prodMk hY) (hA.prod hB),Measure.prod_prod,
    Measure.map_apply hD' hA,Measure.restrict_apply (hD' hA)]
  have he := congrArg (fun μ : Measure GDriver => μ B) (map_restartAt_restrict hW hS (hD hA))
  rw [Measure.map_apply hY hB,Measure.restrict_apply (hY hB),Measure.smul_apply,smul_eq_mul] at he
  rw [Measure.restrict_apply ((hD'.prodMk hY) (hA.prod hB))]
  convert he using 1
  congr 1
  ext b
  simp only [mem_inter_iff,mem_preimage,mem_prod,mem_ofPred_eq]
  tauto

 
theorem lintegral_data_restartAt {X : Type*} [MeasurableSpace X] {W : Measure GDriver}
    (hW : IsBrownianReal (fun t (b : GDriver) => b.1 t) W)
    {S : GDriver→ℝ≥0∞} (hS : IsStoppingTime rawFiltration S)
    {D : GDriver→X} (hD : Measurable[hS.measurableSpace] D)
    {F : X×GDriver→ℝ≥0∞} (hF : Measurable F) :
    (∫⁻b in {b | S b≠∞},F (D b,restartAt S b) ∂W)=
      ∫⁻b in {b | S b≠∞},∫⁻c,F (D b,c) ∂W ∂W := by
  let := hW.isGaussianProcess.isProbabilityMeasure
  have hD' : Measurable D := hD.mono hS.measurableSpace_le le_rfl
  rw [←lintegral_map hF (hD'.prodMk (measurable_restartAt hS)),map_data_restartAt hW hS hD,
    lintegral_prod _ hF.aemeasurable,lintegral_map hF.lintegral_prod_right' hD']

end SLEExactGauge.LoewnerRestart
end
end
 

 
section
 

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
namespace ExactSLEGreen
open ExactSLEMain

lemma actualState_restart {a : ℝ} {b : ℝ≥0→ℝ} (hb : Continuous b)
    {s t : ℝ≥0} {z : ℂ} (hz : alive a b (s+t) z) :
    actualState a b (s+t) z =
      ((actualState a (shiftDriver b s) t (loewnerMap a b s z-(b s:ℂ))).1,
        (actualState a (shiftDriver b s) t (loewnerMap a b s z-(b s:ℂ))).2+
          (actualState a b s z).2) := by
  have hs := (alive_restart_iff a b z s t).mp hz
  apply Prod.ext
  · simp only [actualState,shiftDriver,Complex.ofReal_sub]
    rw [(loewnerMap_restart a b z s t hz).2]
    ring
  · simp only [actualState,deriv_loewnerMap_restart hb hz,norm_mul,
      Real.log_mul (norm_ne_zero_iff.mpr (deriv_loewnerMap_ne_zero
        (continuous_shiftDriver hb s) hs.2))
        (norm_ne_zero_iff.mpr (deriv_loewnerMap_ne_zero hb hs.1))]

lemma physicalRadius_add_log (v : State) (l : ℝ) :
    physicalRadius (v.1,v.2+l)=Real.exp (-l)*physicalRadius v := by
  simp only [physicalRadius,Y_apply,J_apply,neg_add,Real.exp_add]
  ring

lemma logGreen_add_log (a : ℝ) (v : State) (l : ℝ) :
    logGreen a (v.1,v.2+l)=alpha a*l+logGreen a v := by
  simp only [logGreen,J_apply,Y_apply,Q,X_apply]
  ring

lemma physicalGreen_add_log (a : ℝ) (v : State) (l : ℝ) :
    physicalGreen a (v.1,v.2+l)=Real.exp (alpha a*l)*physicalGreen a v := by
  rw [physicalGreen,logGreen_add_log,Real.exp_add]
  rfl

 
lemma physicalRadius_restart {a : ℝ} {b : ℝ≥0→ℝ} (hb : Continuous b)
    {s t : ℝ≥0} {z : ℂ} (hz : alive a b (s+t) z) :
    physicalRadius (actualState a b (s+t) z)=
      ‖deriv (loewnerMap a b s) z‖⁻¹ *
        physicalRadius (actualState a (shiftDriver b s) t (loewnerMap a b s z-(b s:ℂ))) := by
  rw [actualState_restart hb hz,physicalRadius_add_log]
  congr 1
  rw [actualState,Real.exp_neg,Real.exp_log]
  exact norm_pos_iff.mpr (deriv_loewnerMap_ne_zero hb
    ((alive_restart_iff a b z s t).mp hz).1)

 
lemma physicalGreen_restart {a : ℝ} {b : ℝ≥0→ℝ} (hb : Continuous b)
    {s t : ℝ≥0} {z : ℂ} (hz : alive a b (s+t) z) :
    physicalGreen a (actualState a b (s+t) z)=
      ‖deriv (loewnerMap a b s) z‖^(alpha a) *
        physicalGreen a (actualState a (shiftDriver b s) t (loewnerMap a b s z-(b s:ℂ))) := by
  rw [actualState_restart hb hz,physicalGreen_add_log]
  congr 1
  rw [Real.rpow_def_of_pos (norm_pos_iff.mpr (deriv_loewnerMap_ne_zero hb
    ((alive_restart_iff a b z s t).mp hz).1))]
  congr 1
  exact mul_comm _ _

end ExactSLEGreen

namespace SLEExactGauge.LoewnerRestart
open FlowIdentification ExactSLEMain ExactSLEGreen

lemma restart_eq_shiftDriver (s : ℝ≥0) (b : GDriver) :
    ((restart s b).1 : ℝ≥0→ℝ)=shiftDriver b.1 s := rfl

 

theorem survivingGreen_restart (a : ℝ) (b : GDriver) (s t : ℝ≥0) {z : ℂ}
    (hz : alive a b.1 s z) :
    survivingGreen a (s+t) b z = ‖deriv (loewnerMap a b.1 s) z‖^(alpha a) *
      survivingGreen a t (restart s b) (loewnerMap a b.1 s z-(b.1 s:ℂ)) := by
  classical
  have hc : alive a b.1 (s+t) z ↔
      alive a (restart s b).1 t (loewnerMap a b.1 s z-(b.1 s:ℂ)) := by
    rw [alive_restart_iff]
    exact and_iff_right hz
  by_cases h : alive a b.1 (s+t) z
  · unfold survivingGreen
    rw [ite_eq_left h, ite_eq_left (hc.mp h),physicalGreen_restart b.1.continuous h,
      restart_eq_shiftDriver]
    ring
  · simp only [survivingGreen,ite_eq_right h,ite_eq_right (hc.not.mp h),mul_zero]

 
theorem survivingGreen_restart_ratio (a : ℝ) (b : GDriver) (s t : ℝ≥0) {z : ℂ}
    (hz : alive a b.1 s z) :
    survivingGreen a (s+t) b z / survivingGreen a s b z =
      survivingGreen a t (restart s b) (loewnerMap a b.1 s z-(b.1 s:ℂ)) /
        survivingGreen a 0 (restart s b) (loewnerMap a b.1 s z-(b.1 s:ℂ)) := by
  have he := survivingGreen_restart a b s 0 hz
  simp only [add_zero] at he
  rw [survivingGreen_restart a b s t hz,he]
  exact mul_div_mul_left _ _ (Real.rpow_pos_of_pos
    (norm_pos_iff.mpr (deriv_loewnerMap_ne_zero b.1.continuous hz)) _).ne'

end SLEExactGauge.LoewnerRestart
end
end
 

 
section
 

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ExactSLECalculus
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma N_rpow {f : E → ℝ} {v e : E} (r : ℝ)
    (hf : DifferentiableAt ℝ f v) (hp : 0 < f v) :
    N (fun w => f w ^ r) e v = r * f v ^ (r-1) * N f e v := by
  have hh := Real.contDiffAt_rpow_const (n := 1) (p := r) (Or.inl hp.ne')
  simpa only [Function.comp_def, Real.deriv_rpow_const] using
    N_comp (e := e) hf hh.differentiableAt_one

lemma L_rpow {f : E → ℝ} {v A e : E} (r : ℝ)
    (hf : ContDiffAt ℝ 2 f v) (hp : 0 < f v) :
    L (fun w => f w ^ r) A e v = r * f v ^ (r-1) * L f A e v +
      (1/2:ℝ) * (r * (r-1) * f v ^ (r-2)) * N f e v ^ 2 := by
  have hh := Real.contDiffAt_rpow_const (n := 2) (p := r) (Or.inl hp.ne')
  have he : deriv (deriv (fun x : ℝ => x ^ r)) (f v) =
      r * (r-1) * f v ^ (r-2) := by
    rw [Real.deriv_rpow_const', deriv_const_mul_field, Real.deriv_rpow_const]
    rw [show r - 1 - 1 = r - 2 by ring]
    ring
  simpa only [Function.comp_def, Real.deriv_rpow_const, he] using
    L_comp (A := A) (e := e) hf hh

end ExactSLECalculus

namespace ExactSLEGreen
open ExactSLECalculus

 

noncomputable def centeredGenerator (a : ℝ) (f : State → ℝ) (v : State) : ℝ :=
  L f (physicalDrift a v) noise v + noiseLog a v * N f noise v

lemma green_product_generator (a : ℝ) (ha : a ≠ 0) (f : State → ℝ)
    (v : State) (hv : 0 < Y v) (hf : ContDiffAt ℝ 2 f v) :
    L (fun w => physicalGreen a w * f w) (physicalDrift a v) noise v =
      physicalGreen a v * centeredGenerator a f v := by
  have hg : ContDiffAt ℝ 2 (physicalGreen a) v :=
    (contDiffAt_physicalGreen a v hv).of_le (by norm_cast)
  rw [L_mul hg hf]
  have hz : L (physicalGreen a) (physicalDrift a v) noise v = 0 :=
    green_generator_zero a ha v hv
  rw [hz, show N (physicalGreen a) noise v = physicalGreen a v * noiseLog a v from
    green_fderiv_noise a v hv]
  dsimp [centeredGenerator]
  ring

lemma N_Q (v : State) : N Q noise v = -2 * X v := by
  rw [N, (hasFDerivAt_Q v).fderiv]
  simp [noise]

lemma L_Q (a : ℝ) (v : State) :
    L Q (physicalDrift a v) noise v =
      1 + 2 * a * (X v ^ 2 - Y v ^ 2) / Q v := by
  have hn : N Q noise = fun w => -2 * X w := funext N_Q
  rw [L, hn, N, (X.hasFDerivAt.const_mul (-2 : ℝ)).fderiv,
    (hasFDerivAt_Q v).fderiv]
  simp only [_root_.smul_apply, _root_.add_apply, smul_eq_mul,
    regX_drift, regY_drift]
  simp only [X_apply, noise, Complex.neg_re, Complex.one_re]
  ring

lemma N_Y (v : State) : N Y noise v = 0 := by
  rw [N, Y.hasFDerivAt.fderiv]
  simp [noise]

lemma L_Y (a : ℝ) (v : State) :
    L Y (physicalDrift a v) noise v = -a * Y v / Q v := by
  have hn : N Y noise = fun _ => (0 : ℝ) := funext N_Y
  rw [L, hn, N, fderiv_const_apply, _root_.zero_apply,
    Y.hasFDerivAt.fderiv, regY_drift]
  ring

lemma centeredGenerator_Qpow (a q : ℝ) (v : State) (hv : 0 < Y v) :
    centeredGenerator a (fun w => Q w ^ (q/2)) v =
      q * Q v ^ (q/2-2) * ((1/2-a) * Q v + (q/2-2*a) * X v ^ 2) := by
  have hc : ContDiffAt ℝ 2 Q v := ((X.contDiff.pow 2).add (Y.contDiff.pow 2)).contDiffAt
  have hq := Q_pos hv
  have he : Q v ^ (q/2-1) = Q v ^ (q/2-2) * Q v := by
    rw [← Real.rpow_add_one hq.ne']
    congr 1
    ring
  rw [centeredGenerator, L_rpow _ hc hq, N_rpow _ (hasFDerivAt_Q v).differentiableAt hq,
    L_Q, N_Q, he]
  dsimp only [noiseLog, p]
  field_simp
  ring_nf
  simp only [Q]
  ring

lemma centeredGenerator_Ypow (a q : ℝ) (v : State) (hv : 0 < Y v) :
    centeredGenerator a (fun w => Y w ^ q) v = -a * q * Y v ^ q / Q v := by
  have he : Y v ^ (q-1) * Y v = Y v ^ q := by
    rw [← Real.rpow_add_one hv.ne']
    congr 1
    ring
  rw [centeredGenerator, L_rpow _ Y.contDiff.contDiffAt hv,
    N_rpow _ Y.differentiableAt hv, N_Y, L_Y]
  calc
    _ = -a * q * (Y v ^ (q-1) * Y v) / Q v := by ring
    _ = _ := by rw [he]

 
noncomputable def lifetimeTest (q : ℝ) (v : State) : ℝ :=
  Q v ^ (q/2) + 2 * Y v ^ q

lemma lifetimeTest_smooth (q : ℝ) (v : State) (hv : 0 < Y v) :
    ContDiffAt ℝ (↑(⊤ : ℕ∞)) (lifetimeTest q) v := by
  exact ((((X.contDiff.pow 2).add (Y.contDiff.pow 2)).contDiffAt.rpow_const_of_ne
    (Q_pos hv).ne').add (contDiffAt_const.mul (Y.contDiff.contDiffAt.rpow_const_of_ne hv.ne')))

lemma lifetimeTest_nonneg (q : ℝ) (v : State) (hv : 0 ≤ Y v) :
    0 ≤ lifetimeTest q v := by
  unfold lifetimeTest Q
  positivity

lemma lifetimeTest_coercive (q : ℝ) (v : State) (hv : 0 ≤ Y v) :
    Q v ^ (q/2) ≤ lifetimeTest q v := by
  dsimp [lifetimeTest]
  exact le_add_of_nonneg_right (mul_nonneg (by norm_num) (Real.rpow_nonneg hv _))

lemma centeredGenerator_lifetimeTest (a q : ℝ) (v : State) (hv : 0 < Y v) :
    centeredGenerator a (lifetimeTest q) v =
      q * Q v ^ (q/2-2) * ((1/2-a) * Q v + (q/2-2*a) * X v ^ 2) -
      2 * a * q * Y v ^ q / Q v := by
  have hQ : ContDiffAt ℝ 2 (fun w => Q w ^ (q/2)) v :=
    (((X.contDiff.pow 2).add (Y.contDiff.pow 2)).contDiffAt.rpow_const_of_ne (Q_pos hv).ne')
  have hY : ContDiffAt ℝ 2 (fun w => Y w ^ q) v :=
    Y.contDiff.contDiffAt.rpow_const_of_ne hv.ne'
  have split : centeredGenerator a (lifetimeTest q) v =
      centeredGenerator a (fun w => Q w ^ (q/2)) v +
      2 * centeredGenerator a (fun w => Y w ^ q) v := by
    unfold centeredGenerator lifetimeTest
    rw [L_add hQ (contDiffAt_const.mul hY), L_const_mul hY,
      N_add (hQ.differentiableAt (by norm_num)) ((contDiffAt_const.mul hY).differentiableAt (by norm_num)),
      N_const_mul (hY.differentiableAt (by norm_num))]
    ring
  rw [split, centeredGenerator_Qpow _ _ _ hv, centeredGenerator_Ypow _ _ _ hv]
  ring

lemma height_power_comparison (q : ℝ) (hq : q ≤ 2) (v : State) (hv : 0 < Y v) :
    Y v ^ 2 * Q v ^ (q/2-1) ≤ Y v ^ q := by
  have hsq : 0 < Y v ^ 2 := sq_pos_of_pos hv
  have hle : Y v ^ 2 ≤ Q v := by dsimp only [Q]; nlinarith [sq_nonneg (X v)]
  have h := mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_nonpos hsq hle (by linarith : q/2-1 ≤ 0)) hsq.le
  have he : Y v ^ 2 * (Y v ^ 2) ^ (q/2-1) = Y v ^ q := by
    rw [← Real.rpow_two (Y v), ← Real.rpow_mul hv.le, ← Real.rpow_add hv]
    congr 1
    ring
  exact h.trans_eq he

 

lemma centeredGenerator_lifetimeTest_le (a q : ℝ) (ha : 0 < a)
    (hq : 0 < q) (hq2 : q ≤ 2) (v : State) (hv : 0 < Y v) :
    centeredGenerator a (lifetimeTest q) v ≤
      -(q * (6*a-1-q)/2) * Q v ^ (q/2-1) := by
  have hQ := Q_pos hv
  have hp := height_power_comparison q hq2 v hv
  have he : Q v ^ (q/2-1) = Q v ^ (q/2-2) * Q v := by
    rw [← Real.rpow_add_one hQ.ne']
    congr 1
    ring
  have hdiv : Y v ^ 2 * Q v ^ (q/2-2) ≤ Y v ^ q / Q v := by
    apply (le_div_iff₀ hQ).mpr
    nlinarith only [hp.trans_eq (by rfl), show Y v ^ 2 * Q v ^ (q/2-1) =
      (Y v ^ 2 * Q v ^ (q/2-2)) * Q v by rw [he]; ring]
  rw [centeredGenerator_lifetimeTest _ _ _ hv, he]
  have hs : X v ^ 2 ≤ Q v := by dsimp only [Q]; nlinarith [sq_nonneg (Y v)]
  have hn := mul_le_mul_of_nonneg_left hdiv (show 0 ≤ 2*a*q by positivity)
  have hpos : 0 ≤ q * Q v ^ (q/2-2) := by positivity
  have hx := mul_le_mul_of_nonneg_left hs (show 0 ≤ q/2 * (q * Q v ^ (q/2-2)) by positivity)
  dsimp only [Q] at hn hx ⊢
  simp only [div_eq_mul_inv] at hn hx ⊢
  nlinarith only [hn, hx]

noncomputable def lifetimeExponent (a : ℝ) : ℝ := min 1 (3*a-1/2)
noncomputable def lifetimeDrift (a : ℝ) : ℝ :=
  lifetimeExponent a * (6*a-1-lifetimeExponent a)/2

lemma lifetimeExponent_pos {a : ℝ} (ha : 1/4 < a) : 0 < lifetimeExponent a := by
  dsimp [lifetimeExponent]
  exact lt_min (by norm_num) (by linarith)

lemma lifetimeExponent_le_one (a : ℝ) : lifetimeExponent a ≤ 1 := min_le_left _ _

lemma lifetimeDrift_pos {a : ℝ} (ha : 1/4 < a) : 0 < lifetimeDrift a := by
  have hq := lifetimeExponent_pos ha
  have hq' : lifetimeExponent a ≤ 3*a-1/2 := min_le_right _ _
  exact div_pos (mul_pos hq (by linarith)) (by norm_num)

 
lemma green_lifetime_generator_le (a : ℝ) (ha : 1/4 < a)
    (v : State) (hv : 0 < Y v) :
    L (fun w => physicalGreen a w * lifetimeTest (lifetimeExponent a) w)
      (physicalDrift a v) noise v ≤
    -lifetimeDrift a * physicalGreen a v * Q v ^ (lifetimeExponent a/2-1) := by
  rw [green_product_generator a (by linarith) _ _ hv
    ((lifetimeTest_smooth _ _ hv).of_le (by norm_cast))]
  have h := mul_le_mul_of_nonneg_left
    (centeredGenerator_lifetimeTest_le a (lifetimeExponent a) (by linarith)
      (lifetimeExponent_pos ha) ((lifetimeExponent_le_one a).trans (by norm_num)) v hv)
    (Real.exp_pos (logGreen a v)).le
  dsimp only [lifetimeDrift, physicalGreen] at *
  convert h using 1
  first | rfl | ring

end ExactSLEGreen
end

end OAI
