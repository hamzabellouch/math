import Mathlib
import OAI.Probability.SLE.MomentGauge
import OAI.Probability.SLEGauge.CommonStoppedMass

namespace OAI

/-! Hausdorff gauges, Loewner evolution and trace measures. -/

section
 

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
namespace SLEExactGauge.LoewnerRestart
open FlowIdentification ExactSLEGenerator ExactSLEMain

theorem map_data_restartAt_on {X : Type*} [MeasurableSpace X] {W : Measure GDriver}
    (hW : IsBrownianReal (fun t (b : GDriver) => b.1 t) W)
    {S : GDriver→ℝ≥0∞} (hS : IsStoppingTime rawFiltration S)
    {D : GDriver→X} (hD : Measurable[hS.measurableSpace] D)
    {A : Set GDriver} (hA : MeasurableSet[hS.measurableSpace] A) :
    (W.restrict (A∩{b | S b≠∞})).map (fun b => (D b,restartAt S b))=
      ((W.restrict (A∩{b | S b≠∞})).map D).prod W := by
  let := hW.isGaussianProcess.isProbabilityMeasure
  have hD' : Measurable D := hD.mono hS.measurableSpace_le le_rfl
  have hY := measurable_restartAt hS
  apply Measure.ext_prod
  intro B C hB hC
  rw [Measure.map_apply (hD'.prodMk hY) (hB.prod hC),Measure.prod_prod,
    Measure.map_apply hD' hB,Measure.restrict_apply (hD' hB)]
  have he := congrArg (fun μ : Measure GDriver => μ C)
    (map_restartAt_restrict hW hS ((hD hB).inter hA))
  rw [Measure.map_apply hY hC,Measure.restrict_apply (hY hC),
    Measure.smul_apply,smul_eq_mul] at he
  rw [Measure.restrict_apply ((hD'.prodMk hY) (hB.prod hC))]
  convert he using 1 <;> congr 1
  ext b
  simp only [mem_inter_iff,mem_preimage,mem_prod,mem_ofPred_eq]
  tauto
  simp only [inter_assoc]

 

theorem lintegral_data_restartAt_on {X : Type*} [MeasurableSpace X] {W : Measure GDriver}
    (hW : IsBrownianReal (fun t (b : GDriver) => b.1 t) W)
    {S : GDriver→ℝ≥0∞} (hS : IsStoppingTime rawFiltration S)
    {D : GDriver→X} (hD : Measurable[hS.measurableSpace] D)
    {A : Set GDriver} (hA : MeasurableSet[hS.measurableSpace] A)
    {F : X×GDriver→ℝ≥0∞} (hF : Measurable F) :
    (∫⁻b in A∩{b | S b≠∞},F (D b,restartAt S b) ∂W)=
      ∫⁻b in A∩{b | S b≠∞},∫⁻c,F (D b,c) ∂W ∂W := by
  let := hW.isGaussianProcess.isProbabilityMeasure
  have hD' : Measurable D := hD.mono hS.measurableSpace_le le_rfl
  rw [←lintegral_map hF (hD'.prodMk (measurable_restartAt hS)),
    map_data_restartAt_on hW hS hD hA,lintegral_prod _ hF.aemeasurable,
    lintegral_map hF.lintegral_prod_right' hD']

end SLEExactGauge.LoewnerRestart
end
end
 

 
section
 

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped Classical NNReal ENNReal
namespace SLEExactGauge.LoewnerRestart
open FlowIdentification ExactSLEMain ExactSLEGenerator

lemma kernel_with_data_measurable {X : Type*} [MeasurableSpace X]
    (K : Kernel GDriver X) [IsSFiniteKernel K]
    {F : (ℝ≥0×GDriver)×X→ℝ≥0∞} (hF : Measurable F) :
    Measurable (fun p : (ℝ≥0×GDriver)×GDriver => ∫⁻z,F (p.1,z)∂K p.2) := by
  let L : Kernel ((ℝ≥0×GDriver)×GDriver) X := K.comap Prod.snd measurable_snd
  exact (hF.comp (measurable_fst.fst.prodMk measurable_snd)).lintegral_kernel_prod_right' (κ:=L)

 

lemma lintegral_kernel_restartAt_on_shift {X : Type*} [MeasurableSpace X]
    (K : Kernel GDriver X) [IsSFiniteKernel K] {W : Measure GDriver}
    (hW : IsBrownianReal (fun t (b : GDriver) => b.1 t) W)
    {S : GDriver→ℝ≥0∞} (hS : IsStoppingTime rawFiltration S)
    {t : ℝ≥0} {A : Set GDriver}
    (hA : MeasurableSet[(shiftStop_isStoppingTime hS t).measurableSpace] A)
    {F : (ℝ≥0×GDriver)×X→ℝ≥0∞} (hF : Measurable F) :
    (∫⁻b in A∩{b | S b≠∞},∫⁻z,F (stoppedData S b,z)∂K (restartAt S b)∂W)=
      ∫⁻b in {b | S b≠∞},∫⁻c,(concatenatedEvent S A).indicator
        (fun p : (ℝ≥0×GDriver)×GDriver => ∫⁻z,F (p.1,z)∂K p.2)
        (stoppedData S b,c)∂W∂W := by
  have hAe : MeasurableSet A := (shiftStop_isStoppingTime hS t).measurableSpace_le A hA
  have hfinite : MeasurableSet {b | S b≠∞} :=
    (hS.measurable' (measurableSet_singleton ∞)).compl
  have htest := (kernel_with_data_measurable K hF).indicator
    (concatenatedEvent_measurable hS hAe)
  have hi := lintegral_data_restartAt_on hW hS (stoppedData_raw_measurable hS)
    MeasurableSet.univ htest
  simp only [univ_inter] at hi
  rw [←hi,←Measure.restrict_restrict hAe,←lintegral_indicator hAe]
  apply setLIntegral_congr_fun hfinite
  intro b hb
  have he : (stoppedData S b,restartAt S b)∈concatenatedEvent S A ↔ b∈A :=
    concatenatedEvent_stoppedData hb
  by_cases h : b∈A
  · simp only [Set.indicator_of_mem h,Set.indicator_of_mem (he.mpr h)]
  · simp only [Set.indicator_of_notMem h,Set.indicator_of_notMem (mt he.mp h)]

 

theorem restartAt_conditional_kernel {X : Type*} [MeasurableSpace X]
    (K L G : Kernel GDriver X) [IsSFiniteKernel K] [IsSFiniteKernel L] [IsSFiniteKernel G]
    {W : Measure GDriver} (hW : IsBrownianReal (fun t (b : GDriver) => b.1 t) W)
    {t : ℝ≥0}
    (hcond : ∀H : GDriver×X→ℝ≥0∞,
      @Measurable (GDriver×X) ℝ≥0∞ ((rawFiltration t).prod inferInstance) inferInstance H →
      (∫⁻c,∫⁻z,H (c,z)∂K c∂W)=(∫⁻c,∫⁻z,H (c,z)∂L c∂W)+∫⁻c,∫⁻z,H (c,z)∂G c∂W)
    {S : GDriver→ℝ≥0∞} (hS : IsStoppingTime rawFiltration S)
    {A : Set GDriver} (hA : MeasurableSet[(shiftStop_isStoppingTime hS t).measurableSpace] A)
    {F : (ℝ≥0×GDriver)×X→ℝ≥0∞} (hF : Measurable F) :
    (∫⁻b in A∩{b | S b≠∞},∫⁻z,F (stoppedData S b,z)∂K (restartAt S b)∂W)=
      (∫⁻b in A∩{b | S b≠∞},∫⁻z,F (stoppedData S b,z)∂L (restartAt S b)∂W)+
      ∫⁻b in A∩{b | S b≠∞},∫⁻z,F (stoppedData S b,z)∂G (restartAt S b)∂W := by
  let := hW.isGaussianProcess.isProbabilityMeasure
  let E := concatenatedEvent S A
  let T (M : Kernel GDriver X) (p : ℝ≥0×GDriver) (c : GDriver) :=
    E.indicator (fun q : (ℝ≥0×GDriver)×GDriver => ∫⁻z,F (q.1,z)∂M q.2) (p,c)
  have hsection (p : ℝ≥0×GDriver) : MeasurableSet[rawFiltration t] {c | (p,c)∈E} :=
    (concatenatedEvent_raw_joint hS hA).preimage (measurable_const.prodMk measurable_id)
  have hFsection (p : ℝ≥0×GDriver) : Measurable (fun z : X => F (p,z)) :=
    hF.comp (measurable_const.prodMk measurable_id)
  have hi (p : ℝ≥0×GDriver) : (∫⁻c,T K p c∂W)=(∫⁻c,T L p c∂W)+∫⁻c,T G p c∂W := by
    let H : GDriver×X→ℝ≥0∞ := fun q =>
      ({c | (p,c)∈E}).indicator (fun _ => F (p,q.2)) q.1
    have hH : @Measurable (GDriver×X) ℝ≥0∞ ((rawFiltration t).prod inferInstance)
        inferInstance H := by
      exact ((hFsection p).comp measurable_snd).indicator
        ((hsection p).preimage measurable_fst)
    have he (M : Kernel GDriver X) (c : GDriver) : (∫⁻z,H (c,z)∂M c)=T M p c := by
      by_cases hc : (p,c)∈E
      · simp only [H,T,Set.indicator_apply,Set.mem_ofPred_eq,hc,ite_true]
      · simp only [H,T,Set.indicator_apply,Set.mem_ofPred_eq,hc,ite_false,lintegral_zero]
    simpa only [he] using hcond H hH
  rw [lintegral_kernel_restartAt_on_shift K hW hS hA hF,
    lintegral_kernel_restartAt_on_shift L hW hS hA hF,
    lintegral_kernel_restartAt_on_shift G hW hS hA hF]
  change (∫⁻b in {b | S b≠∞},∫⁻c,T K (stoppedData S b) c∂W∂W)=
    (∫⁻b in {b | S b≠∞},∫⁻c,T L (stoppedData S b) c∂W∂W)+
    ∫⁻b in {b | S b≠∞},∫⁻c,T G (stoppedData S b) c∂W∂W
  simp_rw [hi]
  apply lintegral_add_left
  have hM := ((kernel_with_data_measurable L hF).indicator
    (concatenatedEvent_measurable hS ((shiftStop_isStoppingTime hS t).measurableSpace_le A hA)))
  exact hM.lintegral_prod_right'.comp
    ((stoppedData_raw_measurable hS).mono hS.measurableSpace_le le_rfl)

end SLEExactGauge.LoewnerRestart
end
end
 

 
section
 

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology CompactlySupported
open scoped Classical NNReal ENNReal
namespace SLEExactGauge.LoewnerRestart
open FlowIdentification ExactSLEMain ExactSLEGreen ExactSLEGenerator

lemma survivingGreen_zero (a : ℝ) (ha : 0<a) (b : GDriver) (z : UpperPlane) :
    survivingGreen a 0 b z.1=initialGreen a z := by
  have hi : alive a b.1 0 z.1 := radialStop_actual a ha z.1 z.2 (z.1.im/2)
    (by have := z.2; positivity) (by have := z.2; linarith) 0 b 0 bot_le
  simp only [survivingGreen,ite_eq_left hi,actualState_zero ha b z.2,initialGreen]

lemma survivingKernel_zero (a : ℝ) (ha : 1/4<a) (b : GDriver) :
    survivingKernel a ha 0 b=initialGreenMeasure a := by
  rw [survivingKernel_apply]
  simp only [survivingGreen_zero a (lt_trans (by norm_num) ha),initialGreenMeasure]

lemma survivingKernel_restrict_alive (a : ℝ) (ha : 1/4<a) (b : GDriver) (s : ℝ≥0) :
    (survivingKernel a ha s b).restrict {z : UpperPlane | alive a b.1 s z.1}=
      survivingKernel a ha s b := by
  have hD : MeasurableSet {z : UpperPlane | alive a b.1 s z.1} :=
    (measurableSet_alive_joint a ha).preimage
      (measurable_const.prodMk (measurable_const.prodMk measurable_id))
  rw [survivingKernel_apply,restrict_withDensity hD,←withDensity_indicator hD]
  congr 1
  funext z
  by_cases hz : alive a b.1 s z.1
  · simp only [Set.indicator_apply,Set.mem_ofPred_eq,ite_eq_left hz]
  · simp only [Set.indicator_apply,Set.mem_ofPred_eq,ite_eq_right hz,survivingGreen,ENNReal.ofReal_zero]

lemma restartPush_initialGreen (a : ℝ) (ha : 1/4<a) (b : GDriver) (s : ℝ≥0) :
    restartPush a (lt_trans (by norm_num) ha) b s (initialGreenMeasure a)=
      survivingKernel a ha s b := by
  have h := restartPush_survivingKernel a ha b s 0
  rwa [survivingKernel_zero,add_zero,survivingKernel_restrict_alive] at h

 

lemma restartPush_test_joint_measurable (a : ℝ) (ha : 1/4<a)
    (μ : Kernel GDriver UpperPlane) [IsSFiniteKernel μ] {f : UpperPlane→ℝ≥0∞} (hf : Measurable f) :
    Measurable (fun p : (ℝ≥0×GDriver)×GDriver =>
      ∫⁻z,f z∂restartPush a (lt_trans (by norm_num) ha) p.1.2 p.1.1 (μ p.2)) := by
  simp_rw [restartPush_lintegral a ha _ _ _ hf]
  let K : Kernel ((ℝ≥0×GDriver)×GDriver) UpperPlane := μ.comap Prod.snd measurable_snd
  have hin : Measurable (fun p : ((ℝ≥0×GDriver)×GDriver)×UpperPlane =>
      (p.1.1.1,(p.1.1.2,p.2))) :=
    (measurable_fst.fst.fst).prodMk ((measurable_fst.fst.snd).prodMk measurable_snd)
  exact ((restartWeight_joint_measurable a ha).comp hin |>.mul
    (hf.comp ((inverseUpper_joint_measurable a ha).comp hin))).lintegral_kernel_prod_right' (κ:=K)

lemma restartPush_mean (a : ℝ) (ha : 1/4<a) (b : GDriver) (s : ℝ≥0)
    (μ : Kernel GDriver UpperPlane) (W : Measure GDriver)
    (hμ : μ ∘ₘ W=initialGreenMeasure a) {f : UpperPlane→ℝ≥0∞} (hf : Measurable f) :
    (∫⁻c,∫⁻z,f z∂restartPush a (lt_trans (by norm_num) ha) b s (μ c)∂W)=
      ∫⁻z,f z∂survivingKernel a ha s b := by
  have hJ := (continuous_inverseUpper a (lt_trans (by norm_num) ha) b s).measurable
  have hg : Measurable (fun z => restartWeight a b s z*
      f (inverseUpper a (lt_trans (by norm_num) ha) b s z)) :=
    (restartWeight_measurable a ha b s).mul (hf.comp hJ)
  simp_rw [restartPush_lintegral a ha b s _ hf]
  rw [←Measure.lintegral_bind (m:=W) μ.aemeasurable hg.aemeasurable]
  change (∫⁻z,restartWeight a b s z*f (inverseUpper a (lt_trans (by norm_num) ha) b s z)
    ∂μ ∘ₘ W)=_
  rw [hμ,←restartPush_lintegral a ha b s _ hf,restartPush_initialGreen]

 

theorem restartPush_stopped_terminal_mean (a : ℝ) (ha : 1/4<a)
    (μ : Kernel GDriver UpperPlane) [IsSFiniteKernel μ] (W : Measure GDriver)
    (hW : IsBrownianReal (fun t (b : GDriver) => b.1 t) W)
    (hμ : μ ∘ₘ W=initialGreenMeasure a)
    (S : GDriver→ℝ≥0∞) (hS : IsStoppingTime rawFiltration S)
    {A : Set GDriver} (hA : MeasurableSet[hS.measurableSpace] A)
    {f : UpperPlane→ℝ≥0∞} (hf : Measurable f) :
    (∫⁻b in A∩{b | S b≠∞},∫⁻z,f z∂restartPush a (lt_trans (by norm_num) ha)
      b (S b).toNNReal (μ (restartAt S b))∂W)=
      ∫⁻b in A∩{b | S b≠∞},∫⁻z,f z∂stoppedSurvivingKernel a ha S hS b∂W := by
  let F : ((ℝ≥0×GDriver)×GDriver)→ℝ≥0∞ := fun p =>
    ∫⁻z,f z∂restartPush a (lt_trans (by norm_num) ha) p.1.2 p.1.1 (μ p.2)
  have h := lintegral_data_restartAt_on hW hS (stoppedData_raw_measurable hS) hA
    (restartPush_test_joint_measurable a ha μ hf)
  have he (b c : GDriver) : F (stoppedData S b,c)=
      ∫⁻z,f z∂restartPush a (lt_trans (by norm_num) ha) b (S b).toNNReal (μ c) := by
    simp only [F,restartPush,inverseUpper_stoppedData,
      restartWeight_stoppedData a (lt_trans (by norm_num) ha)]
  change (∫⁻b in A∩{b | S b≠∞},F (stoppedData S b,restartAt S b)∂W)=
    ∫⁻b in A∩{b | S b≠∞},∫⁻c,F (stoppedData S b,c)∂W∂W at h
  simp_rw [he] at h
  rw [h]
  apply setLIntegral_congr_fun ((hS.measurableSpace_le A hA).inter
    (hS.measurable' (measurableSet_singleton ∞)).compl)
  intro b hb
  dsimp only
  rw [restartPush_mean a ha _ _ μ W hμ hf,stoppedSurvivingKernel_apply]
  have hbfin : S b≠∞ := hb.2
  simp only [stoppedSurvivingGreen,ite_eq_right hbfin,survivingKernel_apply]

lemma restartPush_measure_joint_measurable (a : ℝ) (ha : 1/4<a)
    (μ : Kernel GDriver UpperPlane) [IsSFiniteKernel μ] :
    Measurable (fun p : (ℝ≥0×GDriver)×GDriver =>
      restartPush a (lt_trans (by norm_num) ha) p.1.2 p.1.1 (μ p.2)) := by
  apply Measure.measurable_of_measurable_coe
  intro A hA
  have h := restartPush_test_joint_measurable a ha μ
    (measurable_const.indicator hA : Measurable (A.indicator (fun _ => (1:ℝ≥0∞))))
  simpa only [lintegral_indicator hA,setLIntegral_one] using h

 

def restartCandidateKernel (a : ℝ) (ha : 1/4<a)
    (μ : Kernel GDriver UpperPlane) [IsSFiniteKernel μ]
    (S : GDriver→ℝ≥0∞) (hS : IsStoppingTime rawFiltration S) :
    Kernel GDriver UpperPlane where
  toFun b := if S b=∞ then 0 else
    restartPush a (lt_trans (by norm_num) ha) b (S b).toNNReal (μ (restartAt S b))
  measurable' := by
    have hin : Measurable (fun b => (((S b).toNNReal,b),restartAt S b)) :=
      ((ENNReal.measurable_toNNReal.comp hS.measurable').prodMk measurable_id).prodMk
        (measurable_restartAt hS)
    have h := (restartPush_measure_joint_measurable a ha μ).comp hin
    change Measurable (fun b => restartPush a (lt_trans (by norm_num) ha)
      b (S b).toNNReal (μ (restartAt S b))) at h
    exact Measurable.ite (hS.measurable' (measurableSet_singleton ∞)) measurable_const h

lemma restartCandidateKernel_apply (a : ℝ) (ha : 1/4<a)
    (μ : Kernel GDriver UpperPlane) [IsSFiniteKernel μ]
    (S : GDriver→ℝ≥0∞) (hS : IsStoppingTime rawFiltration S) (b : GDriver) :
    restartCandidateKernel a ha μ S hS b=if S b=∞ then 0 else
      restartPush a (lt_trans (by norm_num) ha) b (S b).toNNReal (μ (restartAt S b)) := rfl

 

theorem restartCandidateKernel_average_on (a : ℝ) (ha : 1/4<a)
    (μ : Kernel GDriver UpperPlane) [IsSFiniteKernel μ] (W : Measure GDriver)
    (hW : IsBrownianReal (fun t (b : GDriver) => b.1 t) W)
    (hμ : μ ∘ₘ W=initialGreenMeasure a)
    (S : GDriver→ℝ≥0∞) (hS : IsStoppingTime rawFiltration S)
    {A : Set GDriver} (hA : MeasurableSet[hS.measurableSpace] A) :
    restartCandidateKernel a ha μ S hS ∘ₘ (W.restrict A)=
      stoppedSurvivingKernel a ha S hS ∘ₘ (W.restrict A) := by
  have hfinite : MeasurableSet {b | S b≠∞} :=
    (hS.measurable' (measurableSet_singleton ∞)).compl
  ext B hB
  rw [Measure.bind_apply hB (Kernel.aemeasurable _),Measure.bind_apply hB (Kernel.aemeasurable _)]
  have he := restartPush_stopped_terminal_mean a ha μ W hW hμ S hS hA
    (measurable_const.indicator hB : Measurable (B.indicator (fun _ => (1:ℝ≥0∞))))
  simp only [lintegral_indicator hB,setLIntegral_one] at he
  calc
    _ = ∫⁻b in A∩{b | S b≠∞},
        restartPush a (lt_trans (by norm_num) ha) b (S b).toNNReal (μ (restartAt S b)) B ∂W := by
      rw [inter_comm A {b | S b≠∞},←Measure.restrict_restrict hfinite,←lintegral_indicator hfinite]
      apply lintegral_congr
      intro b
      by_cases hb : S b=∞ <;> simp [restartCandidateKernel_apply,hb]
    _ = _ := he
    _ = ∫⁻b in A,stoppedSurvivingKernel a ha S hS b B∂W := by
      rw [inter_comm A {b | S b≠∞},←Measure.restrict_restrict hfinite,←lintegral_indicator hfinite]
      apply lintegral_congr
      intro b
      by_cases hb : S b=∞
      · simp [hb,stoppedSurvivingKernel_apply,stoppedSurvivingGreen]
      · simp [hb]

 

theorem restartCandidateKernel_average_le_initial (a : ℝ) (ha : 1/4<a)
    (μ : Kernel GDriver UpperPlane) [IsSFiniteKernel μ] (W : Measure GDriver)
    (hW : IsBrownianReal (fun t (b : GDriver) => b.1 t) W)
    (hμ : μ ∘ₘ W=initialGreenMeasure a)
    (S : GDriver→ℝ≥0∞) (hS : IsStoppingTime rawFiltration S) :
    restartCandidateKernel a ha μ S hS ∘ₘ W ≤ initialGreenMeasure a := by
  let := hW.isGaussianProcess.isProbabilityMeasure
  have h := restartCandidateKernel_average_on a ha μ W hW hμ S hS MeasurableSet.univ
  rw [Measure.restrict_univ] at h
  rw [h]
  exact stoppedSurvivingKernel_average_le_initial a ha W hW S hS

 

theorem restartCandidateKernel_compact_lintegral_lt_top (a : ℝ) (ha : 1/4<a)
    (μ : Kernel GDriver UpperPlane) [IsSFiniteKernel μ] (W : Measure GDriver)
    (hW : IsBrownianReal (fun t (b : GDriver) => b.1 t) W)
    (hμ : μ ∘ₘ W=initialGreenMeasure a)
    (S : GDriver→ℝ≥0∞) (hS : IsStoppingTime rawFiltration S)
    {K : Set UpperPlane} (hK : IsCompact K) :
    (∫⁻b,restartCandidateKernel a ha μ S hS b K∂W)<∞ := by
  rw [←Measure.bind_apply hK.measurableSet (Kernel.aemeasurable _)]
  exact ((restartCandidateKernel_average_le_initial a ha μ W hW hμ S hS) K).trans_lt
    hK.measure_lt_top

end SLEExactGauge.LoewnerRestart
end
end
 

 
section
 

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology CompactlySupported
open scoped Classical NNReal ENNReal
namespace SLEExactGauge.LoewnerRestart
open FlowIdentification ExactSLEMain ExactSLEGenerator ExactSLEGreen MassVersions

lemma restartPullback_joint_measurable (a : ℝ) (ha : 1/4<a)
    {f : UpperPlane→ℝ≥0∞} (hf : Measurable f) :
    Measurable (fun p : (ℝ≥0×GDriver)×UpperPlane =>
      restartWeight a p.1.2 p.1.1 p.2*
        f (inverseUpper a (lt_trans (by norm_num) ha) p.1.2 p.1.1 p.2)) := by
  have hin : Measurable (fun p : (ℝ≥0×GDriver)×UpperPlane => (p.1.1,(p.1.2,p.2))) :=
    measurable_fst.fst.prodMk (measurable_fst.snd.prodMk measurable_snd)
  have hweight : Measurable (fun p : (ℝ≥0×GDriver)×UpperPlane =>
      restartWeight a p.1.2 p.1.1 p.2) := by
    simpa only [Function.comp_def] using (restartWeight_joint_measurable a ha).comp hin
  have hinverse : Measurable (fun p : (ℝ≥0×GDriver)×UpperPlane =>
      inverseUpper a (lt_trans (by norm_num) ha) p.1.2 p.1.1 p.2) := by
    simpa only [Function.comp_def] using (inverseUpper_joint_measurable a ha).comp hin
  exact hweight.mul (hf.comp hinverse)

 

theorem restartPush_conditional_kernel (a : ℝ) (ha : 1/4<a)
    (K L : Kernel GDriver UpperPlane) [IsSFiniteKernel K] [IsSFiniteKernel L]
    {W : Measure GDriver} (hW : IsBrownianReal (fun t (b : GDriver) => b.1 t) W)
    {t : ℝ≥0}
    (hcond : ∀H : GDriver×UpperPlane→ℝ≥0∞,
      Measurable[(rawFiltration t).prod (inferInstance : MeasurableSpace UpperPlane)] H →
      (∫⁻c,∫⁻z,H (c,z)∂K c∂W)=(∫⁻c,∫⁻z,H (c,z)∂L c∂W)+
        ∫⁻c,∫⁻z,H (c,z)∂survivingKernel a ha t c∂W)
    {S : GDriver→ℝ≥0∞} (hS : IsStoppingTime rawFiltration S)
    {A : Set GDriver} (hA : MeasurableSet[(shiftStop_isStoppingTime hS t).measurableSpace] A)
    {f : UpperPlane→ℝ≥0∞} (hf : Measurable f) :
    (∫⁻b in A∩{b | S b≠∞},∫⁻z,f z∂restartPush a (lt_trans (by norm_num) ha)
        b (S b).toNNReal (K (restartAt S b))∂W)=
      (∫⁻b in A∩{b | S b≠∞},∫⁻z,f z∂restartPush a (lt_trans (by norm_num) ha)
        b (S b).toNNReal (L (restartAt S b))∂W)+
      ∫⁻b in A∩{b | S b≠∞},∫⁻z,f z∂(survivingKernel a ha ((S b).toNNReal+t) b).restrict
        {z : UpperPlane | alive a b.1 (S b).toNNReal z.1}∂W := by
  let F : (ℝ≥0×GDriver)×UpperPlane→ℝ≥0∞ := fun p =>
    restartWeight a p.1.2 p.1.1 p.2*
      f (inverseUpper a (lt_trans (by norm_num) ha) p.1.2 p.1.1 p.2)
  have h := restartAt_conditional_kernel K L (survivingKernel a ha t) hW hcond hS hA
    (restartPullback_joint_measurable a ha hf)
  have he (M : Kernel GDriver UpperPlane) (b : GDriver) :
      (∫⁻z,F (stoppedData S b,z)∂M (restartAt S b))=
      ∫⁻z,f z∂restartPush a (lt_trans (by norm_num) ha) b (S b).toNNReal (M (restartAt S b)) := by
    rw [restartPush_lintegral a ha _ _ _ hf]
    simp only [F,inverseUpper_stoppedData,restartWeight_stoppedData a (lt_trans (by norm_num) ha)]
  change (∫⁻b in A∩{b | S b≠∞},∫⁻z,F (stoppedData S b,z)∂K (restartAt S b)∂W)=
    (∫⁻b in A∩{b | S b≠∞},∫⁻z,F (stoppedData S b,z)∂L (restartAt S b)∂W)+
    ∫⁻b in A∩{b | S b≠∞},∫⁻z,F (stoppedData S b,z)∂survivingKernel a ha t (restartAt S b)∂W at h
  simp_rw [he] at h
  simpa only [restartAt,restartPush_survivingKernel] using h

 

theorem recoveredMass_restarted_potential (a : ℝ) (ha : 1/4<a)
    (W : Measure GDriver) (hW : IsBrownianReal (fun t (b : GDriver) => b.1 t) W)
    (s : ℕ→Finset ℕ) (c : ℕ→ℕ→ℝ)
    (hc : ∀k j,j∈s k→0≤c k j) (hs : ∀k j,j∈s k→k≤j)
    (hsum : ∀k,∑j∈s k,c k j=1)
    (hconv : ∀ᵐ b ∂W, ∀v : ℝ≥0∞, ∀g : C_c(UpperPlane,ℝ), Tendsto
      (fun k => ∑j∈s k,c k j*∫z,g z∂actualUpperMass a
        (Real.exp (-2*a*(j+1))) v b)
      atTop (𝓝 (∫z,g z∂recoveredMass a ha s c hc v b)))
    {S : GDriver→ℝ≥0∞} (hS : IsStoppingTime rawFiltration S)
    {t : ℝ≥0} {A : Set GDriver}
    (hA : MeasurableSet[(shiftStop_isStoppingTime hS t).measurableSpace] A)
    {f : UpperPlane→ℝ≥0∞} (hf : Measurable f) :
    let μ := recoveredMass a ha s c hc
    (∫⁻b in A∩{b | S b≠∞},∫⁻z,f z∂restartPush a (lt_trans (by norm_num) ha)
        b (S b).toNNReal (μ ∞ (restartAt S b))∂W)=
      (∫⁻b in A∩{b | S b≠∞},∫⁻z,f z∂restartPush a (lt_trans (by norm_num) ha)
        b (S b).toNNReal (μ t (restartAt S b))∂W)+
      ∫⁻b in A∩{b | S b≠∞},∫⁻z,f z∂(survivingKernel a ha ((S b).toNNReal+t) b).restrict
        {z : UpperPlane | alive a b.1 (S b).toNNReal z.1}∂W := by
  intro μ
  let := hW.isGaussianProcess.isProbabilityMeasure
  let K : ℝ≥0∞→Kernel GDriver UpperPlane := fun v =>
    ⟨μ v,recoveredMass_measurable a ha s c hc v⟩
  let (v : ℝ≥0∞) (b : GDriver) : IsFiniteMeasureOnCompacts (K v b) := radonLimit_finite _
  have (v : ℝ≥0∞) : IsSFiniteKernel (K v) := isSFiniteKernel_of_locally_finite (K v)
  have hcond (H : GDriver×UpperPlane→ℝ≥0∞)
      (hH : Measurable[(rawFiltration t).prod (inferInstance : MeasurableSpace UpperPlane)] H) :
      (∫⁻b,∫⁻z,H (b,z)∂K ∞ b∂W)=(∫⁻b,∫⁻z,H (b,z)∂K t b∂W)+
        ∫⁻b,∫⁻z,H (b,z)∂survivingKernel a ha t b∂W := by
    have hi := (recoveredMass_all_stopping a ha W hW s c hc hs hsum hconv
      _ (isStoppingTime_const rawFiltration t)).2.2.2.2 H
    rw [IsStoppingTime.measurableSpace_const] at hi
    have hn : Measurable H := hH.mono (prod_sigma_le (rawFiltration.le t) _) le_rfl
    have he (b : GDriver) : (∫⁻z,H (b,z)∂survivingKernel a ha t b)=
        ∫⁻z,H (b,z)*ENNReal.ofReal (survivingGreen a t b z.1)∂upperArea := by
      rw [survivingKernel_apply]
      exact (lintegral_withDensity_eq_lintegral_mul upperArea
        (survivingGreen_spatial_measurable a ha t b).ennreal_ofReal
        (hn.comp (measurable_const.prodMk measurable_id))).trans
        (lintegral_congr fun _ => mul_comm _ _)
    simp_rw [he]
    simpa only [K,Kernel.coe_mk,μ,stoppedSurvivingGreen, ENNReal.some_eq_coe', ENNReal.coe_ne_top, ↓reduceIte,
      ENNReal.toNNReal_coe] using hi hH
  exact restartPush_conditional_kernel a ha (K ∞) (K t) hW hcond hS hA hf

end SLEExactGauge.LoewnerRestart
end
end
 

 
section
 

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology CompactlySupported
open scoped Classical NNReal ENNReal
namespace SLEExactGauge.LoewnerRestart
open FlowIdentification ExactSLEMain ExactSLEGenerator ExactSLEGreen MassVersions

 
def afterStopFiltration {S : GDriver→ℝ≥0∞} (hS : IsStoppingTime rawFiltration S) :
    Filtration ℝ≥0 (inferInstance : MeasurableSpace GDriver) where
  seq t := (shiftStop_isStoppingTime hS t).measurableSpace
  mono' := fun t u htu => (shiftStop_isStoppingTime hS t).measurableSpace_mono
    (shiftStop_isStoppingTime hS u) (fun b => by
      change S b+(t:ℝ≥0∞) ≤ S b+(u:ℝ≥0∞)
      exact add_le_add le_rfl (ENNReal.coe_le_coe.mpr htu))
  le' t := (shiftStop_isStoppingTime hS t).measurableSpace_le

lemma raw_function_congr {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
    {t : ℝ≥0} {f : GDriver→X} (hf : Measurable[rawFiltration t] f)
    {b c : GDriver} (h : ∀ u≤t,b.1 u=c.1 u) : f b=f c := by
  have he := (raw_event_congr (hf (measurableSet_singleton (f b))) h).mp
    (show b∈f ⁻¹' {f b} from rfl)
  exact he.symm

lemma raw_measure_congr {X : Type*} [MeasurableSpace X] {t : ℝ≥0}
    {K : GDriver→Measure X} (hK : Measurable[rawFiltration t] K)
    {b c : GDriver} (h : ∀ u≤t,b.1 u=c.1 u) : K b=K c := by
  ext A hA
  exact raw_function_congr ((Measure.measurable_coe hA).comp hK) h

 

def freshPast (S : GDriver→ℝ≥0∞) (t : ℝ≥0) (b : GDriver) : GDriver :=
  pastDriver t (restart (S b).toNNReal
    (pastDriver (shiftStop S t b).toNNReal b))

lemma freshPast_raw_measurable {S : GDriver→ℝ≥0∞}
    (hS : IsStoppingTime rawFiltration S) (t : ℝ≥0) :
    Measurable[(afterStopFiltration hS) t] (freshPast S t) := by
  have htime : Measurable[(afterStopFiltration hS) t]
      (fun b => (S b).toNNReal) :=
    (ENNReal.measurable_toNNReal.comp hS.measurable).mono (measurableSpace_le_shiftStop hS t) le_rfl
  have hfrozen := pastDriver_stopping_measurable (shiftStop S t) (shiftStop_isStoppingTime hS t)
  exact ((pastDriver_raw_measurable t).mono (rawFiltration.le t) le_rfl).comp
    (continuous_restart_joint.measurable.comp (htime.prodMk hfrozen))

lemma freshPast_eq (S : GDriver→ℝ≥0∞) (t : ℝ≥0) {b : GDriver} (hb : S b≠∞) :
    freshPast S t b=pastDriver t (restartAt S b) := by
  have he : (shiftStop S t b).toNNReal=(S b).toNNReal+t := by
    rw [shiftStop,ENNReal.toNNReal_add hb ENNReal.coe_ne_top,ENNReal.toNNReal_coe]
  apply Subtype.ext
  ext u
  change (restart (S b).toNNReal (pastDriver (shiftStop S t b).toNNReal b)).1 (min u t)=
    (restart (S b).toNNReal b).1 (min u t)
  simp only [restart_apply,he]
  rw [pastDriver_eq _ b _ (add_le_add (le_refl (S b).toNNReal) (min_le_right u t)),
    pastDriver_eq _ b _ (le_self_add)]

 

lemma restartCandidateKernel_raw_measurable (a : ℝ) (ha : 1/4<a)
    (K : Kernel GDriver UpperPlane) [IsSFiniteKernel K] {t : ℝ≥0}
    (hK : Measurable[rawFiltration t] K)
    {S : GDriver→ℝ≥0∞} (hS : IsStoppingTime rawFiltration S) :
    Measurable[(afterStopFiltration hS) t] (restartCandidateKernel a ha K S hS) := by
  classical
  have hD := (stoppedData_raw_measurable hS).mono (measurableSpace_le_shiftStop hS t) le_rfl
  have hM := (restartPush_measure_joint_measurable a ha K).comp
    (hD.prodMk (freshPast_raw_measurable hS t))
  have htop : MeasurableSet[(afterStopFiltration hS) t] {b | S b=∞} :=
    (measurableSpace_le_shiftStop hS t) _ (hS.measurable (measurableSet_singleton ∞))
  have hh : Measurable[(afterStopFiltration hS) t] (fun b =>
      if S b=∞ then (0:Measure UpperPlane) else restartPush a (lt_trans (by norm_num) ha)
        (stoppedData S b).2 (stoppedData S b).1 (K (freshPast S t b))) :=
    Measurable.ite htop measurable_const hM
  convert hh using 1
  funext b
  change (if S b=∞ then 0 else restartPush a _ b (S b).toNNReal (K (restartAt S b)))=
    if S b=∞ then 0 else restartPush a _ (stoppedData S b).2 (stoppedData S b).1
      (K (freshPast S t b))
  by_cases hb : S b=∞
  · simp only [hb,ite_true]
  · simp only [ite_eq_right hb,freshPast_eq S t hb]
    rw [raw_measure_congr hK (pastDriver_eq t (restartAt S b))]
    simp only [restartPush,inverseUpper_stoppedData,
      restartWeight_stoppedData a (lt_trans (by norm_num) ha)]

 
def recoveredRestart (a : ℝ) (ha : 1/4<a)
    (s : ℕ→Finset ℕ) (c : ℕ→ℕ→ℝ) (hc : ∀k j,j∈s k→0≤c k j)
    (S : GDriver→ℝ≥0∞) (v : ℝ≥0∞) (b : GDriver) : Measure UpperPlane :=
  if S b=∞ then 0 else restartPush a (lt_trans (by norm_num) ha) b (S b).toNNReal
    (recoveredMass a ha s c hc v (restartAt S b))

lemma recoveredRestart_measurable (a : ℝ) (ha : 1/4<a)
    (s : ℕ→Finset ℕ) (c : ℕ→ℕ→ℝ) (hc : ∀k j,j∈s k→0≤c k j)
    {S : GDriver→ℝ≥0∞} (hS : IsStoppingTime rawFiltration S) (v : ℝ≥0∞) :
    Measurable (recoveredRestart a ha s c hc S v) := by
  let K : Kernel GDriver UpperPlane :=
    ⟨recoveredMass a ha s c hc v,recoveredMass_measurable a ha s c hc v⟩
  let (b : GDriver) : IsFiniteMeasureOnCompacts (K b) := radonLimit_finite _
  have : IsSFiniteKernel K := isSFiniteKernel_of_locally_finite K
  exact (restartCandidateKernel a ha K S hS).measurable

lemma recoveredRestart_compact_stronglyAdapted (a : ℝ) (ha : 1/4<a)
    (s : ℕ→Finset ℕ) (c : ℕ→ℕ→ℝ) (hc : ∀k j,j∈s k→0≤c k j)
    {S : GDriver→ℝ≥0∞} (hS : IsStoppingTime rawFiltration S) (f : C_c(UpperPlane,ℝ)) :
    StronglyAdapted (afterStopFiltration hS)
      (fun t : ℝ≥0 => fun b => ∫z,f z∂recoveredRestart a ha s c hc S t b) := by
  intro t
  let K : Kernel GDriver UpperPlane :=
    ⟨recoveredMass a ha s c hc t,recoveredMass_measurable a ha s c hc t⟩
  let (b : GDriver) : IsFiniteMeasureOnCompacts (K b) := radonLimit_finite _
  have : IsSFiniteKernel K := isSFiniteKernel_of_locally_finite K
  have hh := restartCandidateKernel_raw_measurable a ha K
    (recoveredMass_raw_measurable a ha s c hc t) hS
  let : MeasurableSpace GDriver := (afterStopFiltration hS) t
  let L : @Kernel GDriver UpperPlane ((afterStopFiltration hS) t) inferInstance :=
    ⟨recoveredRestart a ha s c hc S t,hh⟩
  exact f.continuous.stronglyMeasurable.integral_kernel (κ:=L)

end SLEExactGauge.LoewnerRestart
end
end

end OAI
