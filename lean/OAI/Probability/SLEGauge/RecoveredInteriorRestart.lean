import Mathlib
import OAI.Probability.SLE.MomentGauge
import OAI.Probability.SLEGauge.NormalizedMarkedMoment
import OAI.Probability.SLEGauge.FiniteVariationMartingale

namespace OAI

/-! Hausdorff gauges, Loewner evolution and trace measures. -/

section
 

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology CompactlySupported
open scoped Classical NNReal ENNReal
namespace SLEExactGauge.LoewnerRestart
open FlowIdentification ExactSLEMain ExactSLEGreen ExactSLEGenerator MassVersions
open TraceRestriction TraceMassContinuity TraceMassIntegration CompensatorUniqueness

 

theorem recoveredPostStop_eq_recoveredRestart (κ : ℝ) (hκ : 0<κ) (hκ8 : κ<8)
    (W : Measure GDriver) (hW : IsBrownianReal (fun t (b : GDriver) => b.1 t) W)
    (s : ℕ→Finset ℕ) (c : ℕ→ℕ→ℝ)
    (hc : ∀k j,j∈s k→0≤c k j) (hs : ∀k j,j∈s k→k≤j)
    (hsum : ∀k,∑j∈s k,c k j=1)
    (hmean : recoveredMass (Target.a κ) (a_gt_quarter hκ hκ8) s c hc ∞ ∘ₘ W=
      initialGreenMeasure (Target.a κ))
    (hpath : ∀ᵐ b ∂W, TraceMassFacts κ (driverHomeomorph.symm b)
      (fun v => recoveredMass (Target.a κ) (a_gt_quarter hκ hκ8) s c hc v b))
    (hconv : ∀ᵐ b ∂W, ∀v : ℝ≥0∞, ∀g : C_c(UpperPlane,ℝ), Tendsto
      (fun k => ∑j∈s k,c k j*∫z,g z∂actualUpperMass (Target.a κ)
        (Real.exp (-2*(Target.a κ)*(j+1))) v b)
      atTop (𝓝 (∫z,g z∂recoveredMass (Target.a κ) (a_gt_quarter hκ hκ8) s c hc v b)))
    {S : GDriver→ℝ≥0∞} (hS : IsStoppingTime rawFiltration S) :
    ∀ᵐ b ∂W, ∀v : ℝ≥0∞,
      recoveredPostStop (Target.a κ) (a_gt_quarter hκ hκ8) s c hc S v b=
        recoveredRestart (Target.a κ) (a_gt_quarter hκ hκ8) s c hc S v b := by
  let := hW.isGaussianProcess.isProbabilityMeasure
  let a := Target.a κ
  have ha : 1/4<a := a_gt_quarter hκ hκ8
  let μ := recoveredPostStop a ha s c hc S
  let ν := recoveredRestart a ha s c hc S
  let ℱ := afterStopFiltration hS
  have hμp := recoveredPostStop_path_properties κ hκ hκ8 W s c hc hs hpath hconv S
  have hνp := recoveredRestart_path_properties κ hκ hκ8 W hW s c hc hmean hpath hS
  have hμr (v : ℝ≥0∞) (b : GDriver) : (μ v b).Regular := by
    let := recoveredPostStop_finiteOnCompacts a ha s c hc S v b
    infer_instance
  have hνr : ∀ᵐ b ∂W, ∀v : ℝ≥0∞, (ν v b).Regular :=
    hνp.2.mono (fun b hb v => (hb.1 v).2)
  have hμo : ∀ᵐ b ∂W, Monotone (fun v : ℝ≥0∞ => μ v b) := hμp.mono (fun b hb => hb.2.1)
  have hνo : ∀ᵐ b ∂W, Monotone (fun v : ℝ≥0∞ => ν v b) := hνp.2.mono (fun b hb => hb.2.2.1)
  have hμi (f : C_c(UpperPlane,ℝ)) : Integrable (fun b => ∫z,f z∂μ ∞ b) W :=
    recoveredPostStop_terminal_integrable a ha s c hc W hmean hS f
  have hνi (f : C_c(UpperPlane,ℝ)) : Integrable (fun b => ∫z,f z∂ν ∞ b) W := hνp.1 f
  have hμm (f : C_c(UpperPlane,ℝ)) : StronglyAdapted ℱ (fun t : ℝ≥0 => fun b => ∫z,f z∂μ t b) :=
    recoveredPostStop_compact_stronglyAdapted a ha s c hc hS f
  have hνm (f : C_c(UpperPlane,ℝ)) : StronglyAdapted ℱ (fun t : ℝ≥0 => fun b => ∫z,f z∂ν t b) :=
    recoveredRestart_compact_stronglyAdapted a ha s c hc hS f
  have hμl (v : ℝ≥0∞) (f : C_c(UpperPlane,ℝ)) : ∀ᵐ b ∂W, Integrable f (μ v b) := by
    apply Eventually.of_forall
    intro b
    let := hμr v b
    exact f.integrable
  have hνl (v : ℝ≥0∞) (f : C_c(UpperPlane,ℝ)) : ∀ᵐ b ∂W, Integrable f (ν v b) := by
    filter_upwards [hνr] with b hb
    let := hb v
    exact f.integrable
  have hpot (f : C_c(UpperPlane,ℝ)) (hf : ∀z,0≤f z) (t : ℝ≥0) :
      W[(fun b => (∫z,f z∂μ ∞ b)-(∫z,f z∂μ t b)) | ℱ t] =ᵐ[W]
        W[(fun b => (∫z,f z∂ν ∞ b)-(∫z,f z∂ν t b)) | ℱ t] := by
    have hμti := integrable_test_of_ae_measure_le W (μ t) (μ ∞) hf
      (((hμm f t).mono (ℱ.le t)).aestronglyMeasurable) (hμl ∞ f) (hμi f)
      (hμo.mono (fun b hb => hb le_top))
    have hνti := integrable_test_of_ae_measure_le W (ν t) (ν ∞) hf
      (((hνm f t).mono (ℱ.le t)).aestronglyMeasurable) (hνl ∞ f) (hνi f)
      (hνo.mono (fun b hb => hb le_top))
    let V : Set GDriver→ℝ≥0∞ := fun A => ∫⁻b in A∩{b | S b≠∞},
      ∫⁻z,ENNReal.ofReal (f z)∂(survivingKernel a ha ((S b).toNNReal+t) b).restrict
        {z : UpperPlane | alive a b.1 (S b).toNNReal z.1}∂W
    exact condExp_sub_eq_of_lintegral_potential (ℱ.le t) W (μ t) (ν t) (μ ∞) (ν ∞) hf
      hμti hνti (hμi f) (hνi f) (hμl t f) (hνl t f) (hμl ∞ f) (hνl ∞ f) V
      (fun A hA => recoveredPostStop_potential a ha W hW s c hc hs hsum hconv hS hA
        f.continuous.measurable.ennreal_ofReal)
      (fun A hA => recoveredRestart_potential a ha W hW s c hc hs hsum hconv hS hA
        f.continuous.measurable.ennreal_ofReal)
  have he : ∀ᵐ b ∂W, ∀t : ℝ≥0, μ t b=ν t b := by
    apply ae_all_measure_eq_of_ae_regular (ℱ:=ℱ) (fun t : ℝ≥0 => μ t) (fun t : ℝ≥0 => ν t)
      (μ ∞) (ν ∞)
      (Eventually.of_forall fun b t => hμr t b)
      (hνr.mono (fun b hb t => hb t))
      (Eventually.of_forall (hμr ∞)) (hνr.mono (fun b hb => hb ∞))
      hμm hνm (hμp.mono fun b hb => hb.1) (hνp.2.mono fun b hb => hb.2.1)
      (fun f => hμp.mono fun b hb => (hb.2.2 f).1)
      (fun f => hνp.2.mono fun b hb => (hb.2.2.2 f).1)
      (hμo.mono fun b hb u v huv => hb (ENNReal.coe_le_coe.mpr huv))
      (hνo.mono fun b hb u v huv => hb (ENNReal.coe_le_coe.mpr huv))
      (hμo.mono fun b hb t => hb le_top) (hνo.mono fun b hb t => hb le_top)
      hμi hνi hpot
  have het : μ ∞ =ᵐ[W] ν ∞ := ae_terminal_measure_eq_of_ae_regular
    (fun t : ℝ≥0 => μ t) (fun t : ℝ≥0 => ν t) (μ ∞) (ν ∞)
    (Eventually.of_forall (hμr ∞)) (hνr.mono (fun b hb => hb ∞)) he
    (fun f => hμp.mono fun b hb => (hb.2.2 f).2)
    (fun f => hνp.2.mono fun b hb => (hb.2.2.2 f).2)
  filter_upwards [he,het] with b hb ht v
  induction v using ENNReal.recTopCoe with
  | top => exact ht
  | coe t => exact hb t

 

theorem recoveredMass_interior_restart (κ : ℝ) (hκ : 0<κ) (hκ8 : κ<8)
    (W : Measure GDriver) (hW : IsBrownianReal (fun t (b : GDriver) => b.1 t) W)
    (s : ℕ→Finset ℕ) (c : ℕ→ℕ→ℝ)
    (hc : ∀k j,j∈s k→0≤c k j) (hs : ∀k j,j∈s k→k≤j)
    (hsum : ∀k,∑j∈s k,c k j=1)
    (hmean : recoveredMass (Target.a κ) (a_gt_quarter hκ hκ8) s c hc ∞ ∘ₘ W=
      initialGreenMeasure (Target.a κ))
    (hpath : ∀ᵐ b ∂W, TraceMassFacts κ (driverHomeomorph.symm b)
      (fun v => recoveredMass (Target.a κ) (a_gt_quarter hκ hκ8) s c hc v b))
    (hconv : ∀ᵐ b ∂W, ∀v : ℝ≥0∞, ∀g : C_c(UpperPlane,ℝ), Tendsto
      (fun k => ∑j∈s k,c k j*∫z,g z∂actualUpperMass (Target.a κ)
        (Real.exp (-2*(Target.a κ)*(j+1))) v b)
      atTop (𝓝 (∫z,g z∂recoveredMass (Target.a κ) (a_gt_quarter hκ hκ8) s c hc v b)))
    {S : GDriver→ℝ≥0∞} (hS : IsStoppingTime rawFiltration S) :
    let μ := recoveredMass (Target.a κ) (a_gt_quarter hκ hκ8) s c hc
    ∀ᵐ b ∂W, S b≠∞ →
      (μ (S b) b).restrict {z : UpperPlane | alive (Target.a κ) b.1 (S b).toNNReal z.1}=0 ∧
      ∀v : ℝ≥0∞, (μ (S b+v) b).restrict
          {z : UpperPlane | alive (Target.a κ) b.1 (S b).toNNReal z.1}=
        restartPush (Target.a κ) (lt_trans (by norm_num) (a_gt_quarter hκ hκ8)) b
          (S b).toNNReal (μ v (restartAt S b)) := by
  intro μ
  filter_upwards [recoveredPostStop_eq_recoveredRestart κ hκ hκ8 W hW s c hc hs hsum
    hmean hpath hconv hS,hconv] with b hb hcV hSb
  refine ⟨?_,?_⟩
  · have hz := recoveredPostStop_zero_of_convergence (Target.a κ) (a_gt_quarter hκ hκ8)
      s c hc hs S b hcV
    simpa only [recoveredPostStop,ite_eq_right hSb,add_zero,μ] using hz
  · intro v
    simpa only [recoveredPostStop,recoveredRestart,ite_eq_right hSb,μ] using hb v

end SLEExactGauge.LoewnerRestart
end
end
 

 
section
 

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology CompactlySupported
open scoped Classical NNReal ENNReal
namespace SLEExactGauge.LoewnerRestart
open FlowIdentification ExactSLEMain ExactSLEGreen ExactSLEGenerator MassVersions
open TraceMassContinuity TraceMassIntegration

lemma restartPush_positive (a : ℝ) (ha : 1/4<a) (b : GDriver) (s : ℝ≥0)
    (μ : Measure UpperPlane) (hμ : 0<μ univ) :
    0<restartPush a (lt_trans (by norm_num) ha) b s μ univ := by
  apply pos_iff_ne_zero.mpr
  intro hz
  rw [restartPush,Measure.map_apply (continuous_inverseUpper a
    (lt_trans (by norm_num) ha) b s).measurable MeasurableSet.univ,preimage_univ] at hz
  have h := (withDensity_apply_eq_zero (restartWeight_measurable a ha b s)).mp hz
  have hs : {w : UpperPlane | restartWeight a b s w≠0}=univ := by
    ext w
    simp only [mem_ofPred_eq,mem_univ,iff_true]
    exact (restartWeight_pos a (lt_trans (by norm_num) ha) b s w).ne'
  rw [hs,univ_inter] at h
  exact hμ.ne' h

 

theorem recoveredMass_positive_after_stop (κ : ℝ) (hκ : 0<κ) (hκ8 : κ<8)
    (W : Measure GDriver) (hW : IsBrownianReal (fun t (b : GDriver) => b.1 t) W)
    (s : ℕ→Finset ℕ) (c : ℕ→ℕ→ℝ)
    (hc : ∀k j,j∈s k→0≤c k j) (hs : ∀k j,j∈s k→k≤j)
    (hsum : ∀k,∑j∈s k,c k j=1)
    (hmean : recoveredMass (Target.a κ) (a_gt_quarter hκ hκ8) s c hc ∞ ∘ₘ W=
      initialGreenMeasure (Target.a κ))
    (hpath : ∀ᵐ b ∂W, TraceMassFacts κ (driverHomeomorph.symm b)
      (fun v => recoveredMass (Target.a κ) (a_gt_quarter hκ hκ8) s c hc v b))
    (hconv : ∀ᵐ b ∂W, ∀v : ℝ≥0∞, ∀g : C_c(UpperPlane,ℝ), Tendsto
      (fun k => ∑j∈s k,c k j*∫z,g z∂actualUpperMass (Target.a κ)
        (Real.exp (-2*(Target.a κ)*(j+1))) v b)
      atTop (𝓝 (∫z,g z∂recoveredMass (Target.a κ) (a_gt_quarter hκ hκ8) s c hc v b)))
    {S : GDriver→ℝ≥0∞} (hS : IsStoppingTime rawFiltration S) :
    let μ := recoveredMass (Target.a κ) (a_gt_quarter hκ hκ8) s c hc
    ∀ᵐ b ∂W, S b≠∞ → ∀v : ℝ≥0∞, 0<v → 0<(μ (S b+v) b-μ (S b) b) univ := by
  intro μ
  filter_upwards [recoveredMass_interior_restart κ hκ hκ8 W hW s c hc hs hsum hmean
    hpath hconv hS,ae_restartAt hW hS hpath] with b hr hp hSb v hv
  have hr := hr hSb
  have hp := (hp hSb).initial_positive v hv
  let H := {z : UpperPlane | alive (Target.a κ) b.1 (S b).toNNReal z.1}
  have hH : MeasurableSet H := measurableSet_alive_spatial _ _ _
  have hx : (μ (S b+v) b-μ (S b) b).restrict H=
      restartPush (Target.a κ) (lt_trans (by norm_num) (a_gt_quarter hκ hκ8)) b
        (S b).toNNReal (μ v (restartAt S b)) := by
    rw [Measure.restrict_sub_eq_restrict_sub_restrict hH,hr.1,Measure.sub_zero,hr.2 v]
  have hpos := restartPush_positive (Target.a κ) (a_gt_quarter hκ hκ8) b
    (S b).toNNReal (μ v (restartAt S b)) hp
  rw [←hx] at hpos
  exact hpos.trans_le (Measure.le_iff'.mp Measure.restrict_le_self univ)

lemma measure_sub_antitone_right {X : Type*} [MeasurableSpace X]
    (μ : Measure X) {ν ξ : Measure X} (h : ν≤ξ) : μ-ξ≤μ-ν := by
  simp only [Measure.sub_def]
  apply sInf_le_sInf
  intro τ hτ
  exact (show μ≤τ+ν from hτ).trans (add_le_add le_rfl h)

 

theorem recoveredMass_positive_increments (κ : ℝ) (hκ : 0<κ) (hκ8 : κ<8)
    (W : Measure GDriver) (hW : IsBrownianReal (fun t (b : GDriver) => b.1 t) W)
    (s : ℕ→Finset ℕ) (c : ℕ→ℕ→ℝ)
    (hc : ∀k j,j∈s k→0≤c k j) (hs : ∀k j,j∈s k→k≤j)
    (hsum : ∀k,∑j∈s k,c k j=1)
    (hmean : recoveredMass (Target.a κ) (a_gt_quarter hκ hκ8) s c hc ∞ ∘ₘ W=
      initialGreenMeasure (Target.a κ))
    (hpath : ∀ᵐ b ∂W, TraceMassFacts κ (driverHomeomorph.symm b)
      (fun v => recoveredMass (Target.a κ) (a_gt_quarter hκ hκ8) s c hc v b))
    (hconv : ∀ᵐ b ∂W, ∀v : ℝ≥0∞, ∀g : C_c(UpperPlane,ℝ), Tendsto
      (fun k => ∑j∈s k,c k j*∫z,g z∂actualUpperMass (Target.a κ)
        (Real.exp (-2*(Target.a κ)*(j+1))) v b)
      atTop (𝓝 (∫z,g z∂recoveredMass (Target.a κ) (a_gt_quarter hκ hκ8) s c hc v b))) :
    let μ := recoveredMass (Target.a κ) (a_gt_quarter hκ hκ8) s c hc
    ∀ᵐ b ∂W, ∀u v : ℝ≥0, u<v →
      0<(μ v b-μ u b) univ ∧ ∃K : Set UpperPlane, IsCompact K ∧
        0<(μ v b-μ u b) K ∧ (μ v b-μ u b) K<∞ := by
  intro μ
  have hall : ∀ᵐ b ∂W, ∀q : ℚ, ∀v : ℝ≥0∞, 0<v →
      0<(μ ((Real.toNNReal (q:ℝ):ℝ≥0∞)+v) b-μ (Real.toNNReal (q:ℝ)) b) univ := by
    apply ae_all_iff.mpr
    intro q
    have hh := recoveredMass_positive_after_stop κ hκ hκ8 W hW s c hc hs hsum
      hmean hpath hconv (S:=fun _ => (Real.toNNReal (q:ℝ):ℝ≥0∞)) (isStoppingTime_const rawFiltration _)
    filter_upwards [hh] with b hb
    exact hb ENNReal.coe_ne_top
  filter_upwards [hall,hpath] with b hb hp u v huv
  obtain ⟨q,huq,hqv⟩ := exists_rat_btwn (show (u:ℝ)<(v:ℝ) from huv)
  let p : ℝ≥0 := Real.toNNReal (q:ℝ)
  have hq0 : 0≤(q:ℝ) := u.coe_nonneg.trans huq.le
  have huc : u≤p := by
    rw [←NNReal.coe_le_coe,Real.coe_toNNReal _ hq0]
    exact huq.le
  have hpc : p<v := by
    rw [←NNReal.coe_lt_coe,Real.coe_toNNReal _ hq0]
    exact hqv
  have he : (p:ℝ≥0∞)+((v-p:ℝ≥0):ℝ≥0∞)=(v:ℝ≥0∞) := by
    rw [←ENNReal.coe_add,add_tsub_cancel_of_le hpc.le]
  have hpos := hb q (v-p) (ENNReal.coe_pos.mpr (tsub_pos_iff_lt.mpr hpc))
  change 0<(μ ((p:ℝ≥0∞)+((v-p:ℝ≥0):ℝ≥0∞)) b-μ p b) univ at hpos
  rw [he] at hpos
  have hpos' : 0<(μ v b-μ u b) univ := hpos.trans_le
    ((measure_sub_antitone_right (μ v b) (hp.monotone (ENNReal.coe_le_coe.mpr huc))) univ)
  let : IsFiniteMeasureOnCompacts (μ v b) := radonLimit_finite _
  let : IsFiniteMeasureOnCompacts (μ v b-μ u b) := ⟨fun K hK =>
    ((Measure.sub_le : μ v b-μ u b≤μ v b) K).trans_lt hK.measure_lt_top⟩
  obtain ⟨K,-,hK,hpK⟩ := isOpen_univ.exists_lt_isCompact hpos'
  exact ⟨hpos',K,hK,hpK,hK.measure_lt_top⟩

end SLEExactGauge.LoewnerRestart
end
end
 

 
section
 

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology CompactlySupported
open scoped NNReal ENNReal
namespace ExactSLEGreen
open ExactSLEGenerator ExactSLEMain SLEExactGauge.MassVersions

lemma recoveredMass_compact_stronglyAdapted (a : ℝ) (ha : 1/4<a)
    (s : ℕ→Finset ℕ) (c : ℕ→ℕ→ℝ) (hc : ∀k j,j∈s k→0≤c k j)
    (f : C_c(UpperPlane,ℝ)) :
    StronglyAdapted rawFiltration (fun t : ℝ≥0 => fun b =>
      ∫z,f z∂recoveredMass a ha s c hc t b) := by
  intro t
  let : MeasurableSpace ExactSLEGenerator.Driver := rawFiltration t
  let K : Kernel ExactSLEGenerator.Driver UpperPlane :=
    ⟨recoveredMass a ha s c hc t,recoveredMass_raw_measurable a ha s c hc t⟩
  exact f.continuous.stronglyMeasurable.integral_kernel (κ:=K)

 

theorem recoveredMass_stopped_condExp (a : ℝ) (ha : 1/4<a)
    (W : Measure ExactSLEGenerator.Driver) [IsProbabilityMeasure W]
    (hW : IsBrownianReal (fun t (b : ExactSLEGenerator.Driver) => b.1 t) W)
    (s : ℕ→Finset ℕ) (c : ℕ→ℕ→ℝ)
    (hc : ∀k j,j∈s k→0≤c k j) (hs : ∀k j,j∈s k→k≤j)
    (hsum : ∀k,∑j∈s k,c k j=1)
    (hconv : ∀ᵐ b ∂W, ∀v : ℝ≥0∞, ∀f : C_c(UpperPlane,ℝ), Tendsto
      (fun k => ∑j∈s k,c k j*∫z,f z∂actualUpperMass a
        (Real.exp (-2*a*(j+1))) v b)
      atTop (𝓝 (∫z,f z∂recoveredMass a ha s c hc v b)))
    (S : ExactSLEGenerator.Driver→ℝ≥0∞) (hS : IsStoppingTime rawFiltration S)
    (f : C_c(UpperPlane,ℝ)) :
    W[(fun b => (∫z,f z∂recoveredMass a ha s c hc ∞ b)-
      (∫z,f z∂recoveredMass a ha s c hc (S b) b)) | hS.measurableSpace] =ᵐ[W]
      fun b => ∫z : UpperPlane,f z*stoppedSurvivingGreen a (S b) b z.1∂upperArea := by
  let μ := recoveredMass a ha s c hc
  have hcv (v : ExactSLEGenerator.Driver→ℝ≥0∞) : ∀ᵐ b ∂W, Tendsto
      (fun k => ∑j∈s k,c k j*∫z,f z∂actualUpperMass a
        (Real.exp (-2*a*(j+1))) (v b) b)
      atTop (𝓝 (∫z,f z∂μ (v b) b)) := hconv.mono (fun b hb => hb (v b) f)
  have htop : IsStoppingTime rawFiltration (fun _ : ExactSLEGenerator.Driver => (∞:ℝ≥0∞)) :=
    fun t => by simp
  have hi (v : ExactSLEGenerator.Driver→ℝ≥0∞) (hv : IsStoppingTime rawFiltration v) :
      Integrable (fun b => ∫z,f z∂μ (v b) b) W :=
    memLp_one_iff_integrable.mp (by simpa only [Nat.cast_one] using
      actual_stopped_radon_limit_memLp a ha W hW v hv s c hc hsum _ f (hcv v) 1)
  have hg := stoppedSurvivingKernel_compact_mean_integrable a ha W hW S hS f
  simp_rw [stoppedSurvivingKernel_compact_eval] at hg
  have hgm : StronglyMeasurable[hS.measurableSpace]
      (fun b => ∫z : UpperPlane,f z*stoppedSurvivingGreen a (S b) b z.1∂upperArea) := by
    let : MeasurableSpace ExactSLEGenerator.Driver := hS.measurableSpace
    let K : Kernel ExactSLEGenerator.Driver UpperPlane :=
      ⟨stoppedSurvivingKernel a ha S hS,stoppedSurvivingKernel_raw_measurable a ha S hS⟩
    have h := f.continuous.stronglyMeasurable.integral_kernel (κ:=K)
    change StronglyMeasurable (fun b => ∫z,f z∂stoppedSurvivingKernel a ha S hS b) at h
    simpa only [stoppedSurvivingKernel_compact_eval] using h
  symm
  apply ae_eq_condExp_of_forall_setIntegral_eq hS.measurableSpace_le
    ((hi _ htop).sub (hi S hS)) (fun _ _ _ => hg.integrableOn) _ hgm.aestronglyMeasurable
  intro U hU _
  exact (actual_stopped_limit_compact_conditional a ha W hW S hS s c hs hc hsum
    (fun b => μ (S b) b) (μ ∞) f (hcv S) (hcv (fun _ => ∞)) U hU).symm

 

theorem recoveredMass_extraction_unique (a : ℝ) (ha : 1/4<a)
    (W : Measure ExactSLEGenerator.Driver) [IsProbabilityMeasure W]
    (hW : IsBrownianReal (fun t (b : ExactSLEGenerator.Driver) => b.1 t) W)
    (s₁ s₂ : ℕ→Finset ℕ) (c₁ c₂ : ℕ→ℕ→ℝ)
    (hc₁ : ∀k j,j∈s₁ k→0≤c₁ k j) (hc₂ : ∀k j,j∈s₂ k→0≤c₂ k j)
    (hs₁ : ∀k j,j∈s₁ k→k≤j) (hs₂ : ∀k j,j∈s₂ k→k≤j)
    (hsum₁ : ∀k,∑j∈s₁ k,c₁ k j=1) (hsum₂ : ∀k,∑j∈s₂ k,c₂ k j=1)
    (hconv₁ : ∀ᵐ b ∂W, ∀v : ℝ≥0∞, ∀f : C_c(UpperPlane,ℝ), Tendsto
      (fun k => ∑j∈s₁ k,c₁ k j*∫z,f z∂actualUpperMass a (Real.exp (-2*a*(j+1))) v b)
      atTop (𝓝 (∫z,f z∂recoveredMass a ha s₁ c₁ hc₁ v b)))
    (hconv₂ : ∀ᵐ b ∂W, ∀v : ℝ≥0∞, ∀f : C_c(UpperPlane,ℝ), Tendsto
      (fun k => ∑j∈s₂ k,c₂ k j*∫z,f z∂actualUpperMass a (Real.exp (-2*a*(j+1))) v b)
      atTop (𝓝 (∫z,f z∂recoveredMass a ha s₂ c₂ hc₂ v b)))
    (hcont₁ : ∀f : C_c(UpperPlane,ℝ), ∀ᵐ b ∂W, Continuous (fun v : ℝ≥0 =>
      ∫z,f z∂recoveredMass a ha s₁ c₁ hc₁ v b))
    (hcont₂ : ∀f : C_c(UpperPlane,ℝ), ∀ᵐ b ∂W, Continuous (fun v : ℝ≥0 =>
      ∫z,f z∂recoveredMass a ha s₂ c₂ hc₂ v b))
    (hmono₁ : ∀ᵐ b ∂W, Monotone (fun v : ℝ≥0∞ => recoveredMass a ha s₁ c₁ hc₁ v b))
    (hmono₂ : ∀ᵐ b ∂W, Monotone (fun v : ℝ≥0∞ => recoveredMass a ha s₂ c₂ hc₂ v b))
    (hexh₁ : ∀ᵐ b ∂W, ∀A : Set UpperPlane, MeasurableSet A → Tendsto
      (fun n : ℕ => recoveredMass a ha s₁ c₁ hc₁ (n:ℝ≥0) b A)
      atTop (𝓝 (recoveredMass a ha s₁ c₁ hc₁ ∞ b A)))
    (hexh₂ : ∀ᵐ b ∂W, ∀A : Set UpperPlane, MeasurableSet A → Tendsto
      (fun n : ℕ => recoveredMass a ha s₂ c₂ hc₂ (n:ℝ≥0) b A)
      atTop (𝓝 (recoveredMass a ha s₂ c₂ hc₂ ∞ b A))) :
    ∀ᵐ b ∂W, ∀v : ℝ≥0∞,
      recoveredMass a ha s₁ c₁ hc₁ v b=recoveredMass a ha s₂ c₂ hc₂ v b := by
  let μ := recoveredMass a ha s₁ c₁ hc₁
  let ν := recoveredMass a ha s₂ c₂ hc₂
  let (v : ℝ≥0∞) (b : ExactSLEGenerator.Driver) : (μ v b).Regular := radonLimit_regular _
  let (v : ℝ≥0∞) (b : ExactSLEGenerator.Driver) : (ν v b).Regular := radonLimit_regular _
  have htop : IsStoppingTime rawFiltration (fun _ : ExactSLEGenerator.Driver => (∞:ℝ≥0∞)) :=
    fun t => by simp
  have hi₁ (f : C_c(UpperPlane,ℝ)) : Integrable (fun b => ∫z,f z∂μ ∞ b) W := by
    apply memLp_one_iff_integrable.mp
    simpa only [Nat.cast_one] using (actual_stopped_radon_limit_memLp a ha W hW
      _ htop s₁ c₁ hc₁ hsum₁ (μ ∞) f (hconv₁.mono (fun b hb => hb ∞ f)) 1)
  have hi₂ (f : C_c(UpperPlane,ℝ)) : Integrable (fun b => ∫z,f z∂ν ∞ b) W := by
    apply memLp_one_iff_integrable.mp
    simpa only [Nat.cast_one] using (actual_stopped_radon_limit_memLp a ha W hW
      _ htop s₂ c₂ hc₂ hsum₂ (ν ∞) f (hconv₂.mono (fun b hb => hb ∞ f)) 1)
  have hzero₁ : μ 0=ᵐ[W] 0 := Eventually.of_forall (recoveredMass_zero a ha s₁ c₁ hc₁)
  have hzero₂ : ν 0=ᵐ[W] 0 := Eventually.of_forall (recoveredMass_zero a ha s₂ c₂ hc₂)
  have he : ∀ᵐ b ∂W, ∀v : ℝ≥0, μ v b=ν v b := by
    apply SLEExactGauge.CompensatorUniqueness.ae_all_measure_eq
      (ℱ:=rawFiltration) (fun v : ℝ≥0 => μ v) (fun v : ℝ≥0 => ν v) (μ ∞) (ν ∞)
      (recoveredMass_compact_stronglyAdapted a ha s₁ c₁ hc₁)
      (recoveredMass_compact_stronglyAdapted a ha s₂ c₂ hc₂)
      hzero₁ hzero₂ hcont₁ hcont₂
      (hmono₁.mono (fun b hb s t hst => hb (ENNReal.coe_le_coe.mpr hst)))
      (hmono₂.mono (fun b hb s t hst => hb (ENNReal.coe_le_coe.mpr hst)))
      (hmono₁.mono (fun b hb v => hb le_top))
      (hmono₂.mono (fun b hb v => hb le_top)) hi₁ hi₂
    intro f _ t
    have h₁ := recoveredMass_stopped_condExp a ha W hW s₁ c₁ hc₁ hs₁ hsum₁ hconv₁
      _ (isStoppingTime_const rawFiltration t) f
    have h₂ := recoveredMass_stopped_condExp a ha W hW s₂ c₂ hc₂ hs₂ hsum₂ hconv₂
      _ (isStoppingTime_const rawFiltration t) f
    have hh := h₁.trans h₂.symm
    rw [IsStoppingTime.measurableSpace_const] at hh
    simpa only [μ, ν, ENNReal.some_eq_coe'] using hh
  filter_upwards [he,hexh₁,hexh₂] with b hb h₁ h₂ v
  induction v using ENNReal.recTopCoe with
  | coe v => exact hb v
  | top =>
    apply Measure.ext
    intro A hA
    have h : Tendsto (fun n : ℕ => μ (n:ℝ≥0) b A) atTop (𝓝 (μ ∞ b A)) := h₁ A hA
    simp only [hb] at h
    exact tendsto_nhds_unique h (h₂ A hA)

end ExactSLEGreen
end
end
 

 
section
 

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology CompactlySupported
open scoped NNReal ENNReal
namespace SLEExactGauge.TraceMassContinuity
open FlowIdentification ExactSLEMain ExactSLEGenerator ExactSLEGreen MassVersions TraceMassIntegration
open LoewnerRestart

 

theorem actual_canonical_trace_mass (κ : ℝ) (hκ : 0<κ) (hκ8 : κ<8)
    (W : Measure TDriver) (hW : Target.IsWiener W) :
    ∃ (s : ℕ→Finset ℕ) (c : ℕ→ℕ→ℝ) (hc : ∀k j,j∈s k→0≤c k j),
      (∀k j,j∈s k→k≤j) ∧ (∀k,∑j∈s k,c k j=1) ∧
      let μ := recoveredMass (Target.a κ) (a_gt_quarter hκ hκ8) s c hc
      (∀v b, IsFiniteMeasureOnCompacts (μ v b) ∧ (μ v b).Regular) ∧
      (∀b, μ 0 b=0) ∧ (∀v, Measurable (μ v)) ∧
      IsProgressive rawFiltration (fun v : ℝ≥0 => μ v) ∧
      μ ∞ ∘ₘ (W.map driverHomeomorph)=initialGreenMeasure (Target.a κ) ∧
      (∀ (S : GDriver→ℝ≥0∞) (hS : IsStoppingTime rawFiltration S),
        Measurable[hS.measurableSpace] (fun b => μ (S b) b) ∧
        (∀f : C_c(UpperPlane,ℝ), ∀m : ℕ,
          MemLp (fun b => ∫z,f z∂μ (S b) b) (m:ℝ≥0∞) (W.map driverHomeomorph)) ∧
        (∀K : Set UpperPlane, IsCompact K → ∀m : ℕ,
          MemLp (fun b => (μ (S b) b K).toReal) (m:ℝ≥0∞) (W.map driverHomeomorph)) ∧
        (∀f : C_c(UpperPlane,ℝ), Tendsto (fun k => eLpNorm
          (fun b => (∑j∈s k,c k j*∫z,f z∂actualUpperMass (Target.a κ)
            (Real.exp (-2*(Target.a κ)*(j+1))) (S b) b)-(∫z,f z∂μ (S b) b))
              1 (W.map driverHomeomorph)) atTop (𝓝 0)) ∧
        (∀H : GDriver × UpperPlane→ℝ≥0∞,
          Measurable[hS.measurableSpace.prod (inferInstance : MeasurableSpace UpperPlane)] H →
          (∫⁻b,∫⁻z,H (b,z)∂μ ∞ b∂(W.map driverHomeomorph))=
            (∫⁻b,∫⁻z,H (b,z)∂μ (S b) b∂(W.map driverHomeomorph))+
            ∫⁻b,∫⁻z,H (b,z)*ENNReal.ofReal (stoppedSurvivingGreen (Target.a κ) (S b) b z.1)
              ∂upperArea∂(W.map driverHomeomorph)) ∧
        (∀ᵐ b ∂(W.map driverHomeomorph), S b≠∞ →
          (μ (S b) b).restrict {z : UpperPlane | alive (Target.a κ) b.1 (S b).toNNReal z.1}=0 ∧
          ∀v : ℝ≥0∞, (μ (S b+v) b).restrict
              {z : UpperPlane | alive (Target.a κ) b.1 (S b).toNNReal z.1}=
            restartPush (Target.a κ) (lt_trans (by norm_num) (a_gt_quarter hκ hκ8)) b
              (S b).toNNReal (μ v (restartAt S b)))) ∧
      ∀ᵐ b ∂W, TraceMassFacts κ b (fun v => μ v (driverHomeomorph b)) ∧
        (∀v : ℝ≥0∞, ∀f : C_c(UpperPlane,ℝ), Tendsto
          (fun k => ∑j∈s k,c k j*∫z,f z∂actualUpperMass (Target.a κ)
            (Real.exp (-2*(Target.a κ)*(j+1))) v (driverHomeomorph b))
          atTop (𝓝 (∫z,f z∂μ v (driverHomeomorph b)))) ∧
        (∀u v : ℝ≥0, u<v →
          0<(μ v (driverHomeomorph b)-μ u (driverHomeomorph b)) univ ∧
          ∃K : Set UpperPlane, IsCompact K ∧
            0<(μ v (driverHomeomorph b)-μ u (driverHomeomorph b)) K ∧
            (μ v (driverHomeomorph b)-μ u (driverHomeomorph b)) K<∞) := by
  obtain ⟨s,c,hc,hs,hsum,hreg,hzero,hmeas,hprog,hmean,hstop,hpath⟩ :=
    actual_common_trace_mass κ hκ hκ8 W hW
  let μ := recoveredMass (Target.a κ) (a_gt_quarter hκ hκ8) s c hc
  have hBW := brownian_map_driver W hW
  have hp : ∀ᵐ b ∂(W.map driverHomeomorph),
      TraceMassFacts κ (driverHomeomorph.symm b) (fun v => μ v b) := by
    apply driverMeasurableEquiv.measurableEmbedding.ae_map_iff.mpr
    filter_upwards [hpath] with b hb
    change TraceMassFacts κ (driverHomeomorph.symm (driverHomeomorph b))
      (fun v => μ v (driverHomeomorph b))
    simpa only [Homeomorph.symm_apply_apply] using hb.1
  have hv : ∀ᵐ b ∂(W.map driverHomeomorph), ∀v : ℝ≥0∞, ∀f : C_c(UpperPlane,ℝ), Tendsto
      (fun k => ∑j∈s k,c k j*∫z,f z∂actualUpperMass (Target.a κ)
        (Real.exp (-2*(Target.a κ)*(j+1))) v b)
      atTop (𝓝 (∫z,f z∂μ v b)) := by
    apply driverMeasurableEquiv.measurableEmbedding.ae_map_iff.mpr
    exact hpath.mono (fun b hb => hb.2)
  refine ⟨s,c,hc,hs,hsum,hreg,hzero,hmeas,hprog,hmean,?_,?_⟩
  · intro S hS
    rcases hstop S hS with ⟨hsm,hmom,hK,hL,hH⟩
    exact ⟨hsm,hmom,hK,hL,hH,recoveredMass_interior_restart κ hκ hκ8
      (W.map driverHomeomorph) hBW s c hc hs hsum hmean hp hv hS⟩
  · have hpos := recoveredMass_positive_increments κ hκ hκ8
      (W.map driverHomeomorph) hBW s c hc hs hsum hmean hp hv
    have hpos' := driverMeasurableEquiv.measurableEmbedding.ae_map_iff.mp hpos
    filter_upwards [hpath,hpos'] with b hb hbp
    exact ⟨hb.1,hb.2,hbp⟩

end SLEExactGauge.TraceMassContinuity
end
end
 

 
section
 

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology CompactlySupported
open scoped Classical NNReal ENNReal
namespace SLEExactGauge.CenteredMoments
open ExactSLEMain ExactSLEGenerator ExactSLEGreen KernelSimilarity

lemma diskMass_mono {ν η : Measure UpperPlane} (h : ν≤η) (a θ : ℝ) :
    diskMass a θ ν≤diskMass a θ η := by
  apply Measure.map_mono _ (diskMap_measurable θ)
  apply Measure.le_iff.mpr
  intro U hU
  rw [withDensity_apply _ hU,withDensity_apply _ hU]
  exact lintegral_mono' (Measure.restrict_mono le_rfl h) le_rfl

lemma diskMass_inner_le_enorm (a θ : ℝ) (ha : 1/4<a) (hθ : 0<θ) (hθπ : θ<Real.pi)
    (ν : Measure UpperPlane) [IsFiniteMeasureOnCompacts ν] :
    diskMass a θ ν (Metric.closedBall (0:ℂ) (1/4))≤‖∫z,diskTest a θ hθ hθπ z∂ν‖ₑ :=
  (diskMass_inner_le_test a θ ha hθ hθπ ν).trans (Real.ofReal_le_enorm _)

 

theorem common_limit_disk_tilted_moment (a : ℝ) (ha : 1/4<a)
    (m : ℕ) (hm : 1 ≤ m) :
    ∃D : ℝ≥0∞,D<∞ ∧ ∀(W : Measure ExactSLEGenerator.Driver) [IsProbabilityMeasure W],
      IsBrownianReal (fun t (b : ExactSLEGenerator.Driver)=>b.1 t) W →
      ∀(s : ℕ→Finset ℕ) (coeff : ℕ→ℕ→ℝ),
      (∀k j,j∈s k→0≤coeff k j) → (∀k,∑j∈s k,coeff k j=1) →
      ∀μ : ℝ≥0∞→ExactSLEGenerator.Driver→Measure UpperPlane,
      (∀b,IsFiniteMeasureOnCompacts (μ ∞ b)) → Measurable (μ ∞) →
      (∀ᵐ b∂W,∀v : ℝ≥0∞,μ v b≤μ ∞ b) →
      (∀ᵐ b∂W,∀f : C_c(UpperPlane,ℝ),Tendsto (fun k=>∑j∈s k,coeff k j*
        ∫z,f z∂actualUpperMass a (Real.exp (-2*a*(j+1))) ∞ b)
          atTop (𝓝 (∫z,f z∂μ ∞ b))) →
      ∀(θ : ℝ) (_hθ : 0<θ) (_hθπ : θ<Real.pi) (l : ℕ)
        (T : ExactSLEGenerator.Driver→ℝ≥0∞),
      (∫⁻b,(diskMass a θ (μ (T b) b) (Metric.closedBall (0:ℂ) (1/4)))^m
        ∂radialLaw W a (fromDisk θ 0) (Real.sin θ*Real.exp (-2*a*l)))≤
        D*ENNReal.ofReal ((Real.sin θ)^(-p a)) := by
  let K : Set ℂ := Subtype.val '' tsupport diskCutoff
  have hK : IsCompact K := diskCutoff.hasCompactSupport.image continuous_subtype_val
  have hcK : ∀z∈K,(1/2:ℝ)≤2*z.im := by
    rintro z ⟨w,hw,rfl⟩
    have hh := height_of_ball (diskCutoff_support w hw).le
    linarith
  obtain ⟨D,hD,hDb⟩ := actual_normalized_tilted_moment_bound a ha m hm K
    hK.measurableSet hK.isBounded (1/2) (by norm_num) (by norm_num) hcK
    (2^(2-alpha a)) (Real.rpow_nonneg (by norm_num) _)
  refine ⟨D,hD,?_⟩
  intro W hprob hW s coeff hcoeff hsum μ hμfin hμ hmono hlim θ hθ hθπ l T
  let (b : ExactSLEGenerator.Driver) : IsFiniteMeasureOnCompacts (μ ∞ b) := hμfin b
  let f := diskTest a θ hθ hθπ
  have hfm : Measurable (fun b=>∫z,f z∂μ ∞ b) := by
    let Kμ : Kernel ExactSLEGenerator.Driver UpperPlane := ⟨μ ∞,hμ⟩
    exact (f.continuous.stronglyMeasurable.integral_kernel (κ:=Kμ)).measurable
  have hb := hDb W hW θ hθ hθπ f (diskTest_support a θ hθ hθπ)
    (diskTest_bound a θ hθ hθπ) s coeff hcoeff hsum ∞ (μ ∞) hfm
    (hlim.mono (fun b hb=>hb f)) l
  refine le_trans (lintegral_mono_ae ?_) hb
  have habs : radialLaw W a (fromDisk θ 0) (Real.sin θ*Real.exp (-2*a*l)) ≪ W :=
    withDensity_absolutelyContinuous W _
  filter_upwards [habs.ae_le hmono] with b hb
  exact pow_le_pow_left' ((Measure.le_iff'.mp (diskMass_mono (hb (T b)) a θ)
    _).trans (diskMass_inner_le_enorm a θ ha hθ hθπ (μ ∞ b))) m

end SLEExactGauge.CenteredMoments
end
end

end OAI
