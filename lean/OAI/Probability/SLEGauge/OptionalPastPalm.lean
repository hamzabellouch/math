import Mathlib
import OAI.Probability.SLE.MomentGauge
import OAI.Probability.SLEGauge.SubdiskMoments

namespace OAI

/-! Hausdorff gauges, Loewner evolution and trace measures. -/

section
 

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology CompactlySupported
open scoped Classical NNReal ENNReal
namespace SLEExactGauge.PastMass
open FlowIdentification ExactSLEMain ExactSLEGenerator ExactSLEGreen
open TraceMassContinuity MassVersions TraceMassIntegration

lemma optional_green_set_balance (a : ℝ) (S : GDriver→ℝ≥0∞)
    (hS : IsStoppingTime rawFiltration S) (W : Measure GDriver)
    (μ : ℝ≥0∞→GDriver→Measure UpperPlane)
    (hH : ∀H : GDriver × UpperPlane→ℝ≥0∞,
      Measurable[hS.measurableSpace.prod (inferInstance : MeasurableSpace UpperPlane)] H →
      (∫⁻b,∫⁻z,H (b,z)∂μ ∞ b∂W)=
        (∫⁻b,∫⁻z,H (b,z)∂μ (S b) b∂W)+
        ∫⁻b,∫⁻z,H (b,z)*ENNReal.ofReal (stoppedSurvivingGreen a (S b) b z.1)∂upperArea∂W)
    (Q : Set UpperPlane) (hQ : MeasurableSet Q) :
    (∫⁻b, μ ∞ b Q∂W) = (∫⁻b, μ (S b) b Q∂W)+
      ∫⁻b,∫⁻z in Q, ENNReal.ofReal (stoppedSurvivingGreen a (S b) b z.1)∂upperArea∂W := by
  let H : GDriver × UpperPlane→ℝ≥0∞ := fun p=> Q.indicator (fun _=>1) p.2
  have hm : Measurable[hS.measurableSpace.prod (inferInstance : MeasurableSpace UpperPlane)] H :=
    (measurable_const.indicator hQ).comp measurable_snd
  have he (ν : Measure UpperPlane) (b : GDriver) : (∫⁻z,H (b,z)∂ν)=ν Q := by
    simp only [H,lintegral_indicator hQ,lintegral_one,Measure.restrict_apply_univ]
  have hg (b : GDriver) :
      (∫⁻z,H (b,z)*ENNReal.ofReal (stoppedSurvivingGreen a (S b) b z.1)∂upperArea)=
        ∫⁻z in Q,ENNReal.ofReal (stoppedSurvivingGreen a (S b) b z.1)∂upperArea := by
    rw [show (fun z => H (b,z)*ENNReal.ofReal (stoppedSurvivingGreen a (S b) b z.1))=
      Q.indicator (fun z=>ENNReal.ofReal (stoppedSurvivingGreen a (S b) b z.1)) from by
        funext z; by_cases hz : z∈Q <;> simp [H,hz], lintegral_indicator hQ]
  simpa only [he,hg] using hH H hm

lemma expected_green_past_kernel (a : ℝ) (ha : 1/4<a) (W : Measure GDriver) [SFinite W]
    (S : GDriver→ℝ≥0∞) (hS : IsStoppingTime rawFiltration S)
    (Q : Set UpperPlane) :
    (∫⁻b,∫⁻z in Q,ENNReal.ofReal (stoppedSurvivingGreen a (S b) b z.1)∂upperArea∂W)=
      ∫⁻z in Q,ENNReal.ofReal (initialGreen a z)*pastGreenKernel W a S z∂upperArea := by
  simp_rw [initial_mul_pastGreenKernel]
  exact lintegral_lintegral_swap (stoppedSurvivingGreen_joint_measurable a ha S hS).ennreal_ofReal.aemeasurable

 

lemma strict_past_mass_ae (κ : ℝ) (W : Measure GDriver)
    (μ : ℝ≥0∞→GDriver→Measure UpperPlane)
    (hp : ∀ᵐ b∂W, TraceMassFacts κ (driverHomeomorph.symm b) (fun v=>μ v b))
    (Q : Set UpperPlane) (hQ : MeasurableSet Q) (hfin : ∀b, μ ∞ b Q≠∞)
    (S : GDriver→ℝ≥0∞) :
    (fun b=>μ ∞ b (Q∩{z | S b<visitTime κ b z})) =ᵐ[W]
      (fun b=>μ ∞ b Q-μ (S b) b Q) :=
  hp.mono fun b hb=>stopped_strictPast_mass κ b (fun v=>μ v b) hb Q hQ (hfin b) (S b)

lemma strict_past_mass_aemeasurable (κ : ℝ) (W : Measure GDriver)
    (μ : ℝ≥0∞→GDriver→Measure UpperPlane)
    (hp : ∀ᵐ b∂W, TraceMassFacts κ (driverHomeomorph.symm b) (fun v=>μ v b))
    (Q : Set UpperPlane) (hQ : MeasurableSet Q) (hfin : ∀b, μ ∞ b Q≠∞)
    (S : GDriver→ℝ≥0∞) (hm : Measurable (μ ∞))
    (hsm : Measurable (fun b=>μ (S b) b)) :
    AEMeasurable (fun b=>μ ∞ b (Q∩{z | S b<visitTime κ b z})) W :=
  ((Measure.measurable_coe hQ).comp hm |>.sub ((Measure.measurable_coe hQ).comp hsm)).aemeasurable.congr
    (strict_past_mass_ae κ W μ hp Q hQ hfin S).symm

 

lemma strict_past_Palm (κ a : ℝ) (ha : 1/4<a) (W : Measure GDriver) [SFinite W]
    (μ : ℝ≥0∞→GDriver→Measure UpperPlane)
    (hp : ∀ᵐ b∂W, TraceMassFacts κ (driverHomeomorph.symm b) (fun v=>μ v b))
    (S : GDriver→ℝ≥0∞) (hS : IsStoppingTime rawFiltration S)
    (hsm : Measurable (fun b=>μ (S b) b))
    (hH : ∀H : GDriver × UpperPlane→ℝ≥0∞,
      Measurable[hS.measurableSpace.prod (inferInstance : MeasurableSpace UpperPlane)] H →
      (∫⁻b,∫⁻z,H (b,z)∂μ ∞ b∂W)=
        (∫⁻b,∫⁻z,H (b,z)∂μ (S b) b∂W)+
        ∫⁻b,∫⁻z,H (b,z)*ENNReal.ofReal (stoppedSurvivingGreen a (S b) b z.1)∂upperArea∂W)
    (Q : Set UpperPlane) (hQ : MeasurableSet Q) (hfin : ∀b, μ ∞ b Q≠∞)
    (hf : (∫⁻b,μ ∞ b Q∂W)≠∞) :
    (∫⁻b,μ ∞ b (Q∩{z | S b<visitTime κ b z})∂W)=
      ∫⁻z in Q,ENNReal.ofReal (initialGreen a z)*pastGreenKernel W a S z∂upperArea := by
  have hle : (fun b=>μ (S b) b Q) ≤ᵐ[W] (fun b=>μ ∞ b Q) :=
    hp.mono fun b hb=>hb.monotone le_top Q
  have hsf : (∫⁻b,μ (S b) b Q∂W)≠∞ := ne_top_of_le_ne_top hf (lintegral_mono_ae hle)
  have hmS : Measurable (fun b=>μ (S b) b Q) := (Measure.measurable_coe hQ).comp hsm
  rw [lintegral_congr_ae (strict_past_mass_ae κ W μ hp Q hQ hfin S),
    lintegral_sub hmS hsf hle,
    optional_green_set_balance a S hS W μ hH Q hQ, ENNReal.add_sub_cancel_left hsf]
  exact expected_green_past_kernel a ha W S hS Q

end SLEExactGauge.PastMass
end
end
 

 
section
 

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology CompactlySupported
open scoped Classical NNReal ENNReal
namespace SLEExactGauge.PastMass
open FlowIdentification ExactSLEMain ExactSLEGenerator ExactSLEGreen
open TraceMassContinuity MassVersions TraceMassIntegration

 

structure TracePalmData (κ a : ℝ) (W : Measure GDriver)
    (μ : ℝ≥0∞→GDriver→Measure UpperPlane) : Prop where
  terminal_measurable : Measurable (μ ∞)
  finite_compact : ∀v b, IsFiniteMeasureOnCompacts (μ v b)
  adapted : Adapted rawFiltration (fun t : ℝ≥0=>μ t)
  mean : μ ∞ ∘ₘ W=initialGreenMeasure a
  path : ∀ᵐ b∂W,TraceMassFacts κ (driverHomeomorph.symm b) (fun v=>μ v b)
  optional_measurable : ∀(S : GDriver→ℝ≥0∞) (hS : IsStoppingTime rawFiltration S),
    Measurable[hS.measurableSpace] (fun b=>μ (S b) b)
  optional_kernel : ∀(S : GDriver→ℝ≥0∞) (hS : IsStoppingTime rawFiltration S)
    (H : GDriver × UpperPlane→ℝ≥0∞),
    Measurable[hS.measurableSpace.prod (inferInstance : MeasurableSpace UpperPlane)] H →
      (∫⁻b,∫⁻z,H (b,z)∂μ ∞ b∂W)=
        (∫⁻b,∫⁻z,H (b,z)∂μ (S b) b∂W)+
        ∫⁻b,∫⁻z,H (b,z)*ENNReal.ofReal (stoppedSurvivingGreen a (S b) b z.1)∂upperArea∂W

 

def countablePastKernel {ι : Type*} (e : ℕ→ι) (q : ι→ℝ≥0)
    (W : Measure GDriver) (a : ℝ) (μ : ℝ≥0∞→GDriver→Measure UpperPlane)
    (Q : Set UpperPlane) (H : ℝ≥0∞) (z : UpperPlane) : ℝ≥0∞ :=
  ⨆n : ℕ, pastGreenKernel W a
    (finiteTestTime ((Finset.range n).image (q∘e)) (fun t b=>μ t b Q) H) z

namespace TracePalmData
variable {κ a : ℝ} {W : Measure GDriver} {μ : ℝ≥0∞→GDriver→Measure UpperPlane}
    (D : TracePalmData κ a W μ)
include D

lemma evaluation_adapted (Q : Set UpperPlane) (hQ : MeasurableSet Q) :
    Adapted rawFiltration (fun t : ℝ≥0=>fun b=>μ t b Q) :=
  fun t=>(Measure.measurable_coe hQ).comp (D.adapted t)

lemma test_stopping (Q : Set UpperPlane) (hQ : MeasurableSet Q) (F : Finset ℝ≥0) (H : ℝ≥0∞) :
    IsStoppingTime rawFiltration (finiteTestTime F (fun t b=>μ t b Q) H) :=
  finiteTestTime_stopping _ _ (D.evaluation_adapted Q hQ) F H

lemma compact_expected_finite (Q : Set UpperPlane) (hQ : IsCompact Q) :
    (∫⁻b,μ ∞ b Q∂W)≠∞ := by
  rw [←Measure.bind_apply hQ.measurableSet D.terminal_measurable.aemeasurable,D.mean]
  exact hQ.measure_lt_top.ne

lemma compact_finite (Q : Set UpperPlane) (hQ : IsCompact Q) (v : ℝ≥0∞) (b : GDriver) :
    μ v b Q≠∞ := by
  let := D.finite_compact v b
  exact hQ.measure_lt_top.ne

lemma stopped_Palm (ha : 1/4<a) [SFinite W] (S : GDriver→ℝ≥0∞)
    (hS : IsStoppingTime rawFiltration S) (Q : Set UpperPlane) (hQ : IsCompact Q) :
    (∫⁻b,μ ∞ b (Q∩{z | S b<visitTime κ b z})∂W)=
      ∫⁻z in Q,ENNReal.ofReal (initialGreen a z)*pastGreenKernel W a S z∂upperArea :=
  strict_past_Palm κ a ha W μ D.path S hS
    ((D.optional_measurable S hS).mono hS.measurableSpace_le le_rfl)
    (D.optional_kernel S hS) Q hQ.measurableSet (D.compact_finite Q hQ ∞)
    (D.compact_expected_finite Q hQ)

lemma finite_Palm (ha : 1/4<a) [SFinite W] (Q : Set UpperPlane) (hQ : IsCompact Q)
    (F : Finset ℝ≥0) (H : ℝ≥0∞) :
    (∫⁻b,μ ∞ b (Q∩{z | ∃q∈F,H<μ q b Q ∧ (q:ℝ≥0∞)<visitTime κ b z})∂W)=
      ∫⁻z in Q,ENNReal.ofReal (initialGreen a z)*
        pastGreenKernel W a (finiteTestTime F (fun t b=>μ t b Q) H) z∂upperArea := by
  simpa only [finiteTestTime_lt_iff] using
    D.stopped_Palm ha _ (D.test_stopping Q hQ.measurableSet F H) Q hQ

lemma compact_past_aemeasurable (Q : Set UpperPlane) (hQ : IsCompact Q)
    (S : GDriver→ℝ≥0∞) (hS : IsStoppingTime rawFiltration S) :
    AEMeasurable (fun b=>μ ∞ b (Q∩{z | S b<visitTime κ b z})) W :=
  strict_past_mass_aemeasurable κ W μ D.path Q hQ.measurableSet
    (D.compact_finite Q hQ ∞) S D.terminal_measurable
    ((D.optional_measurable S hS).mono hS.measurableSpace_le le_rfl)

lemma countable_kernel_measurable (ha : 1/4<a) [SFinite W]
    {ι : Type*} (e : ℕ→ι) (q : ι→ℝ≥0) (Q : Set UpperPlane) (hQ : MeasurableSet Q)
    (H : ℝ≥0∞) : Measurable (countablePastKernel e q W a μ Q H) :=
  .iSup fun _=>pastGreenKernel_measurable W a ha _ (D.test_stopping Q hQ _ H)

 

lemma countable_Palm (ha : 1/4<a) [IsProbabilityMeasure W]
    (hW : IsBrownianReal (fun t (b : GDriver)=>b.1 t) W)
    {ι : Type*} (e : ℕ→ι) (q : ι→ℝ≥0) (he : Function.Surjective e)
    (Q : Set UpperPlane) (hQ : IsCompact Q) (H : ℝ≥0∞) :
    (∫⁻b,μ ∞ b (Q∩{z | ∃i,H<μ (q i) b Q ∧ (q i:ℝ≥0∞)<visitTime κ b z})∂W)=
      ∫⁻z in Q,ENNReal.ofReal (initialGreen a z)*countablePastKernel e q W a μ Q H z∂upperArea := by
  let S (n : ℕ) := finiteTestTime ((Finset.range n).image (q∘e)) (fun t b=>μ t b Q) H
  have hS (n : ℕ) : IsStoppingTime rawFiltration (S n) := D.test_stopping Q hQ.measurableSet _ H
  let A (n : ℕ) (b : GDriver) := μ ∞ b (Q∩{z | S n b<visitTime κ b z})
  have hAm (n : ℕ) : AEMeasurable (A n) W := D.compact_past_aemeasurable Q hQ (S n) (hS n)
  have hmono : ∀b,Monotone (fun n=>A n b) := by
    intro b n k hnk
    apply measure_mono
    intro z hz
    exact ⟨hz.1,(finiteTestTime_sequence_antitone e q (fun t b=>μ t b Q) H b hnk).trans_lt hz.2⟩
  have heq : (fun b=>μ ∞ b (Q∩{z | ∃i,H<μ (q i) b Q ∧ (q i:ℝ≥0∞)<visitTime κ b z})) =ᵐ[W]
      (fun b=>⨆n,A n b) := D.path.mono fun b hb=>
    all_past_mass_eq_iSup e q he κ b (fun v=>μ v b) hb Q hQ.measurableSet H
  have hKmono : Monotone (fun n z=>ENNReal.ofReal (initialGreen a z)*pastGreenKernel W a (S n) z) := by
    intro n k hnk z
    apply mul_le_mul_right
    exact pastGreenKernel_antitone W hW a ha (S k) (S n) (hS k) (hS n)
      (fun b=>finiteTestTime_sequence_antitone e q (fun t b=>μ t b Q) H b hnk) z
  rw [lintegral_congr_ae heq,lintegral_iSup' hAm (Eventually.of_forall hmono)]
  simp only [A,D.stopped_Palm ha _ (hS _) Q hQ]
  simp only [countablePastKernel,ENNReal.mul_iSup]
  exact (lintegral_iSup (fun n=>(initialGreen_continuous a).measurable.ennreal_ofReal.mul
    (pastGreenKernel_measurable W a ha (S n) (hS n))) hKmono).symm

lemma countable_past_aemeasurable {ι : Type*} (e : ℕ→ι) (q : ι→ℝ≥0)
    (he : Function.Surjective e) (Q : Set UpperPlane) (hQ : IsCompact Q) (H : ℝ≥0∞) :
    AEMeasurable (fun b=>μ ∞ b (Q∩{z | ∃i,H<μ (q i) b Q ∧ (q i:ℝ≥0∞)<visitTime κ b z})) W := by
  have heq : (fun b=>μ ∞ b (Q∩{z | ∃i,H<μ (q i) b Q ∧ (q i:ℝ≥0∞)<visitTime κ b z})) =ᵐ[W]
      (fun b=>⨆n : ℕ,μ ∞ b (Q∩{z | finiteTestTime ((Finset.range n).image (q∘e))
        (fun t b=>μ t b Q) H b<visitTime κ b z})) := D.path.mono fun b hb=>
    all_past_mass_eq_iSup e q he κ b (fun v=>μ v b) hb Q hQ.measurableSet H
  exact (AEMeasurable.iSup (fun n=>D.compact_past_aemeasurable Q hQ _
    (D.test_stopping Q hQ.measurableSet _ H))).congr heq.symm

end TracePalmData

 

theorem actual_Palm_data (κ : ℝ) (hκ : 0<κ) (hκ8 : κ<8)
    (W : Measure TDriver) (hW : Target.IsWiener W) :
    ∃ (s : ℕ→Finset ℕ) (c : ℕ→ℕ→ℝ) (hc : ∀k j,j∈s k→0≤c k j),
      (∀k j,j∈s k→k≤j) ∧ (∀k,∑j∈s k,c k j=1) ∧
      TracePalmData κ (Target.a κ) (W.map driverHomeomorph)
        (recoveredMass (Target.a κ) (a_gt_quarter hκ hκ8) s c hc) := by
  obtain ⟨s,c,hc,hs,hsum,hreg,hzero,hmeas,hprog,hmean,hstop,hpath⟩ :=
    actual_canonical_trace_mass κ hκ hκ8 W hW
  refine ⟨s,c,hc,hs,hsum,hmeas ∞,fun v b=>(hreg v b).1,hprog.adapted,hmean,?_,
    fun S hS=>(hstop S hS).1,fun S hS=>(hstop S hS).2.2.2.2.1⟩
  apply driverMeasurableEquiv.measurableEmbedding.ae_map_iff.mpr
  filter_upwards [hpath] with b hb
  change TraceMassFacts κ (driverHomeomorph.symm (driverHomeomorph b))
    (fun v=>recoveredMass (Target.a κ) (a_gt_quarter hκ hκ8) s c hc v (driverHomeomorph b))
  simpa only [Homeomorph.symm_apply_apply] using hb.1

end SLEExactGauge.PastMass
end
end
 

 
section
 

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology CompactlySupported
open scoped NNReal ENNReal
namespace SLEExactGauge.TraceMassContinuity
open FlowIdentification ExactSLEMain ExactSLEGenerator ExactSLEGreen MassVersions TraceMassIntegration
open LoewnerRestart PastMass

structure CanonicalMassData (κ a : ℝ) (ha : 1/4<a) (W : Measure GDriver)
    (μ : ℝ≥0∞→GDriver→Measure UpperPlane) : Prop extends TracePalmData κ a W μ where
  regular : ∀v b,(μ v b).Regular
  initial_zero : ∀b, μ 0 b=0
  progressive : IsProgressive rawFiltration (fun t : ℝ≥0=>μ t)
  optional_test_moments : ∀(S : GDriver→ℝ≥0∞) (_hS : IsStoppingTime rawFiltration S)
    (f : C_c(UpperPlane,ℝ)) (m : ℕ), MemLp (fun b=>∫z,f z∂μ (S b) b) (m:ℝ≥0∞) W
  optional_compact_moments : ∀(S : GDriver→ℝ≥0∞) (_hS : IsStoppingTime rawFiltration S)
    (K : Set UpperPlane), IsCompact K→∀m : ℕ,MemLp (fun b=>(μ (S b) b K).toReal) (m:ℝ≥0∞) W
  restart : ∀(S : GDriver→ℝ≥0∞) (_hS : IsStoppingTime rawFiltration S),
    ∀ᵐ b∂W,S b≠∞→(μ (S b) b).restrict {z : UpperPlane | alive a b.1 (S b).toNNReal z.1}=0 ∧
      ∀v : ℝ≥0∞,(μ (S b+v) b).restrict {z : UpperPlane | alive a b.1 (S b).toNNReal z.1}=
        restartPush a (lt_trans (by norm_num) ha) b (S b).toNNReal (μ v (restartAt S b))
  positive_increments : ∀ᵐ b∂W,∀u v : ℝ≥0,u<v→
    0<(μ v b-μ u b) univ ∧ ∃K : Set UpperPlane,IsCompact K ∧
      0<(μ v b-μ u b) K ∧ (μ v b-μ u b) K<∞

 

theorem actual_canonical_mass_data (κ : ℝ) (hκ : 0<κ) (hκ8 : κ<8)
    (W : Measure TDriver) (hW : Target.IsWiener W) :
    ∃(s : ℕ→Finset ℕ) (c : ℕ→ℕ→ℝ) (hc : ∀k j,j∈s k→0≤c k j),
      (∀k j,j∈s k→k≤j) ∧ (∀k,∑j∈s k,c k j=1) ∧
      let μ := recoveredMass (Target.a κ) (a_gt_quarter hκ hκ8) s c hc
      CanonicalMassData κ (Target.a κ) (a_gt_quarter hκ hκ8) (W.map driverHomeomorph) μ ∧
      (∀(S : GDriver→ℝ≥0∞),IsStoppingTime rawFiltration S→∀f : C_c(UpperPlane,ℝ),
        Tendsto (fun k=>eLpNorm (fun b=>(∑j∈s k,c k j*∫z,f z∂actualUpperMass (Target.a κ)
          (Real.exp (-2*(Target.a κ)*(j+1))) (S b) b)-(∫z,f z∂μ (S b) b))
            1 (W.map driverHomeomorph)) atTop (𝓝 0)) ∧
      (∀ᵐ b∂(W.map driverHomeomorph),∀v : ℝ≥0∞,∀f : C_c(UpperPlane,ℝ),
        Tendsto (fun k=>∑j∈s k,c k j*∫z,f z∂actualUpperMass (Target.a κ)
          (Real.exp (-2*(Target.a κ)*(j+1))) v b) atTop (𝓝 (∫z,f z∂μ v b))) := by
  obtain ⟨s,c,hc,hs,hsum,hreg,hzero,hmeas,hprog,hmean,hstop,hpath⟩ :=
    actual_canonical_trace_mass κ hκ hκ8 W hW
  let μ := recoveredMass (Target.a κ) (a_gt_quarter hκ hκ8) s c hc
  have hp : ∀ᵐ b∂(W.map driverHomeomorph),
      TraceMassFacts κ (driverHomeomorph.symm b) (fun v=>μ v b) ∧
      (∀v : ℝ≥0∞,∀f : C_c(UpperPlane,ℝ),Tendsto
        (fun k=>∑j∈s k,c k j*∫z,f z∂actualUpperMass (Target.a κ)
          (Real.exp (-2*(Target.a κ)*(j+1))) v b) atTop (𝓝 (∫z,f z∂μ v b))) ∧
      (∀u v : ℝ≥0,u<v→0<(μ v b-μ u b) univ ∧ ∃K : Set UpperPlane,IsCompact K ∧
        0<(μ v b-μ u b) K ∧ (μ v b-μ u b) K<∞) := by
    apply driverMeasurableEquiv.measurableEmbedding.ae_map_iff.mpr
    filter_upwards [hpath] with b hb
    change TraceMassFacts κ (driverHomeomorph.symm (driverHomeomorph b))
      (fun v=>μ v (driverHomeomorph b)) ∧ _
    simp only [show driverMeasurableEquiv b=driverHomeomorph b from rfl,
      Homeomorph.symm_apply_apply]
    exact hb
  refine ⟨s,c,hc,hs,hsum,?_,?_,hp.mono (fun b hb=>hb.2.1)⟩
  · exact {
      terminal_measurable := hmeas ∞
      finite_compact := fun v b=>(hreg v b).1
      adapted := hprog.adapted
      mean := hmean
      path := hp.mono (fun b hb=>hb.1)
      optional_measurable := fun S hS=>(hstop S hS).1
      optional_kernel := fun S hS=>(hstop S hS).2.2.2.2.1
      regular := fun v b=>(hreg v b).2
      initial_zero := hzero
      progressive := hprog
      optional_test_moments := fun S hS=>(hstop S hS).2.1
      optional_compact_moments := fun S hS=>(hstop S hS).2.2.1
      restart := fun S hS=>(hstop S hS).2.2.2.2.2
      positive_increments := hp.mono (fun b hb=>hb.2.2) }
  · exact fun S hS=>(hstop S hS).2.2.2.1

end SLEExactGauge.TraceMassContinuity
end
end
 

 
section
 

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology CompactlySupported
open scoped NNReal ENNReal
namespace SLEExactGauge.CenteredMoments
open FlowIdentification ExactSLEMain ExactSLEGenerator ExactSLEGreen MassVersions
open TraceMassIntegration TraceMassContinuity CompactSequence

 

theorem actual_subdisk_positive_moments (κ : ℝ) (hκ : 0<κ) (hκ8 : κ<8)
    (W : Measure TDriver) (hW : Target.IsWiener W) :
    ∃ (s : ℕ→Finset ℕ) (c : ℕ→ℕ→ℝ) (hc : ∀k j,j∈s k→0≤c k j),
      (∀k j,j∈s k→k≤j) ∧ (∀k,∑j∈s k,c k j=1) ∧
      let μ := recoveredMass (Target.a κ) (a_gt_quarter hκ hκ8) s c hc
      CanonicalMassData κ (Target.a κ) (a_gt_quarter hκ hκ8) (W.map driverHomeomorph) μ ∧
      (∀v b,IsFiniteMeasureOnCompacts (μ v b) ∧ (μ v b).Regular) ∧
      Measurable (fun p : ℝ≥0∞×GDriver=>μ p.1 p.2) ∧
      (∀(S : GDriver→ℝ≥0∞) (hS : IsStoppingTime rawFiltration S),
        Measurable[hS.measurableSpace] (fun b=>μ (S b) b)) ∧
      (∀ᵐ b∂W,TraceMassFacts κ b (fun v=>μ v (driverHomeomorph b)) ∧
        (∀v : ℝ≥0∞,∀f : C_c(UpperPlane,ℝ),Tendsto
          (fun k=>∑j∈s k,c k j*∫z,f z∂actualUpperMass (Target.a κ)
             (Real.exp (-2*(Target.a κ)*(j+1))) v (driverHomeomorph b))
          atTop (𝓝 (∫z,f z∂μ v (driverHomeomorph b)))) ∧
        (∀u v : ℝ≥0,u<v →
          0<(μ v (driverHomeomorph b)-μ u (driverHomeomorph b)) univ)) ∧
      ∃n₀ : ℕ, let r := subdiskRadius n₀
      ∃Q : Measure (ℕ→ℝ≥0∞),IsProbabilityMeasure Q ∧
        (∀n,Q.map (initialVector n)=(finiteAngleLaw (W.map driverHomeomorph) (Target.a κ) n).map
          (fun p=>fun i : Fin (n+1)=>subdiskMass (Target.a κ) μ r i p)) ∧
        (∀ᵐ x∂Q,Monotone x ∧ Tendsto x atTop (𝓝 (diskSequenceMass x)) ∧ diskSequenceMass x<∞) ∧
        (∀ m : ℕ, 1 ≤ m →
          0<(∫⁻x,(diskSequenceMass x)^m∂Q) ∧
          (∫⁻x,(diskSequenceMass x)^m∂Q)<∞ ∧
          (∫⁻x,(diskSequenceMass x)^m∂Q)=⨆l,subdiskMoment (W.map driverHomeomorph) (Target.a κ) μ r m l ∧
          Tendsto (subdiskMoment (W.map driverHomeomorph) (Target.a κ) μ r m) atTop
            (𝓝 (∫⁻x,(diskSequenceMass x)^m∂Q))) := by
  obtain ⟨s,c,hc,hs,hsum,D,hL,hvAll⟩ :=
    actual_canonical_mass_data κ hκ hκ8 W hW
  let μ := recoveredMass (Target.a κ) (a_gt_quarter hκ hκ8) s c hc
  let V := W.map driverHomeomorph
  have hBW : IsBrownianReal (fun t (b : GDriver)=>b.1 t) V := brownian_map_driver W hW
  have : IsProbabilityMeasure V := hBW.isGaussianProcess.isProbabilityMeasure
  have hreg : ∀v b,IsFiniteMeasureOnCompacts (μ v b) ∧ (μ v b).Regular :=
    fun v b=>⟨D.finite_compact v b,D.regular v b⟩
  have (v : ℝ≥0∞) (b : GDriver) : IsFiniteMeasureOnCompacts (μ v b) := D.finite_compact v b
  have hμ : Measurable (fun p : ℝ≥0∞×GDriver=>μ p.1 p.2) :=
    recoveredMass_joint_measurable (Target.a κ) (a_gt_quarter hκ hκ8) s c hc
  have hraw (l : ℕ) (θ : Angle) :
      Measurable[(centeredTime_stopping (Target.a κ) (a_gt_quarter hκ hκ8) θ l).measurableSpace]
        (fun b=>μ (levelTime (Target.a κ) θ.1 b.1 l) b) := D.optional_measurable _ _
  have hp : ∀ᵐ b∂V,TraceMassFacts κ (driverHomeomorph.symm b) (fun v=>μ v b) := D.path
  have hv : ∀ᵐ b∂V,∀f : C_c(UpperPlane,ℝ),Tendsto
      (fun k=>∑j∈s k,c k j*∫z,f z∂actualUpperMass (Target.a κ)
        (Real.exp (-2*(Target.a κ)*(j+1))) ∞ b) atTop (𝓝 (∫z,f z∂μ ∞ b)) :=
    hvAll.mono (fun b hb=>hb ∞)
  have hmono : ∀ᵐ b∂V,Monotone (fun v=>μ v b) := hp.mono (fun b hb=>hb.monotone)
  obtain ⟨n₀,hn₀⟩ := exists_subdisk_positive_mean V hBW (Target.a κ)
    (a_gt_quarter hκ hκ8) μ hμ (hp.mono (fun b hb=>hb.initial_positive))
  let r := subdiskRadius n₀
  have hr : 0≤r := (subdiskRadius_pos n₀).le
  have hr1 : r<1 := subdiskRadius_lt_one n₀
  obtain ⟨Q,hQ,hlaw,hQmono⟩ := exists_subdisk_sequence_law V hBW r (Target.a κ)
    (a_gt_quarter hκ hκ8) μ hμ hraw hmono
  have he (m : ℕ) : (∫⁻x,(diskSequenceMass x)^m∂Q)=⨆l,subdiskMoment V (Target.a κ) μ r m l :=
    subdiskSequence_moment V r (Target.a κ) (a_gt_quarter hκ hκ8) μ hμ Q hlaw hQmono m
  have hf (m : ℕ) (hm : 1 ≤ m) : (∫⁻x,(diskSequenceMass x)^m∂Q)<∞ := by
    obtain ⟨D,hD,hDb⟩ := common_limit_subdisk_mixed_moment_bound r hr hr1 (Target.a κ) (a_gt_quarter hκ hκ8) m hm
    rw [he]
    apply lt_of_le_of_lt (iSup_le (fun l=> ?_)) hD
    exact hDb V hBW s c hc hsum μ (fun v b=>(hreg v b).1) hμ
      (hmono.mono (fun b hb v=>hb le_top)) hv l
  have hpos1 : 0<∫⁻x,diskSequenceMass x∂Q := by
    have hh := he 1
    simp only [pow_one] at hh
    rw [hh]
    apply hn₀.trans_le
    simpa only [subdiskMoment,pow_one] using
      le_iSup (fun l=>subdiskMoment V (Target.a κ) μ r 1 l) 1
  have hpos (m : ℕ) (hm : 1 ≤ m) : 0<∫⁻x,(diskSequenceMass x)^m∂Q := by
    have heq : Function.support (fun x=>diskSequenceMass x^m)=Function.support diskSequenceMass := by
      ext x; simp only [Function.mem_support, ne_eq, pow_eq_zero_iff (by omega : m≠0)]
    rw [lintegral_pos_iff_support (diskSequenceMass_measurable.pow_const m), heq]
    exact (lintegral_pos_iff_support diskSequenceMass_measurable).mp hpos1
  have hfin : ∀ᵐ x∂Q,diskSequenceMass x<∞ := ae_lt_top (diskSequenceMass_measurable)
    (show (∫⁻x,diskSequenceMass x∂Q)≠∞ by simpa only [pow_one] using (hf 1 le_rfl).ne)
  refine ⟨s,c,hc,hs,hsum,D,hreg,hμ,D.optional_measurable,?_,n₀,Q,hQ,hlaw,?_,?_⟩
  · have hboth := hp.and (hvAll.and D.positive_increments)
    have ht := driverMeasurableEquiv.measurableEmbedding.ae_map_iff.mp hboth
    filter_upwards [ht] with b hb
    have he : driverMeasurableEquiv b=driverHomeomorph b := rfl
    simp only [he,Homeomorph.symm_apply_apply] at hb
    exact ⟨hb.1,hb.2.1,fun u v huv=>(hb.2.2 u v huv).1⟩
  · filter_upwards [hQmono,hfin] with x hx hxf
    exact ⟨hx,diskSequenceMass_tendsto hx,hxf⟩
  · intro m hm
    refine ⟨hpos m hm,hf m hm,he m,?_⟩
    rw [he]
    exact tendsto_atTop_iSup (subdiskMoment_monotone V hBW r (Target.a κ)
      (a_gt_quarter hκ hκ8) μ hμ hraw hmono m)

end SLEExactGauge.CenteredMoments
end
end

end OAI
