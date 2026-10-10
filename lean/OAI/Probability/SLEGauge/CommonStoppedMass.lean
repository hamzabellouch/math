import Mathlib
import OAI.Probability.SLE.MomentGauge
import OAI.Probability.SLEGauge.ConformalRestartMap
import OAI.Probability.SLEGauge.StoppedMassMeasurability

namespace OAI

/-! Hausdorff gauges, Loewner evolution and trace measures. -/

section
 

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology CompactlySupported
open scoped NNReal ENNReal
namespace ExactSLEGreen
open ExactSLEGenerator ExactSLEMain ExactSLEMassExtraction SLEExactGauge.MassVersions

 

theorem recoveredMass_all_stopping (a : ℝ) (ha : 1/4<a)
    (W : Measure ExactSLEGenerator.Driver) [IsProbabilityMeasure W]
    (hW : IsBrownianReal (fun t (b : ExactSLEGenerator.Driver) => b.1 t) W)
    (s : ℕ→Finset ℕ) (c : ℕ→ℕ→ℝ)
    (hc : ∀k j,j∈s k→0≤c k j) (hs : ∀k j,j∈s k→k≤j)
    (hsum : ∀k,∑j∈s k,c k j=1)
    (hconv : ∀ᵐ b ∂W, ∀v : ℝ≥0∞, ∀f : C_c(UpperPlane,ℝ), Tendsto
      (fun k => ∑j∈s k,c k j*∫z,f z∂actualUpperMass a
        (Real.exp (-2*a*(j+1))) v b)
      atTop (𝓝 (∫z,f z∂recoveredMass a ha s c hc v b))) :
    let μ := recoveredMass a ha s c hc
    ∀ (S : ExactSLEGenerator.Driver→ℝ≥0∞) (hS : IsStoppingTime rawFiltration S),
      Measurable[hS.measurableSpace] (fun b => μ (S b) b) ∧
      (∀f : C_c(UpperPlane,ℝ), ∀m : ℕ,
        MemLp (fun b => ∫z,f z∂μ (S b) b) (m:ℝ≥0∞) W) ∧
      (∀K : Set UpperPlane, IsCompact K → ∀m : ℕ,
        MemLp (fun b => (μ (S b) b K).toReal) (m:ℝ≥0∞) W) ∧
      (∀f : C_c(UpperPlane,ℝ), Tendsto (fun k => eLpNorm
        (fun b => (∑j∈s k,c k j*∫z,f z∂actualUpperMass a
          (Real.exp (-2*a*(j+1))) (S b) b)-(∫z,f z∂μ (S b) b)) 1 W)
        atTop (𝓝 0)) ∧
      (∀H : ExactSLEGenerator.Driver × UpperPlane→ℝ≥0∞,
        Measurable[hS.measurableSpace.prod (inferInstance : MeasurableSpace UpperPlane)] H →
        (∫⁻b,∫⁻z,H (b,z)∂μ ∞ b∂W)=(∫⁻b,∫⁻z,H (b,z)∂μ (S b) b∂W)+
          ∫⁻b,∫⁻z,H (b,z)*ENNReal.ofReal (stoppedSurvivingGreen a (S b) b z.1)∂upperArea∂W) := by
  intro μ S hS
  let (v : ℝ≥0∞) (b : ExactSLEGenerator.Driver) : IsFiniteMeasureOnCompacts (μ v b) :=
    radonLimit_finite _
  have hmeas := recoveredMass_stopping_raw_measurable a ha s c hc S hS
  let K : Kernel ExactSLEGenerator.Driver UpperPlane :=
    ⟨fun b => μ (S b) b,hmeas.mono hS.measurableSpace_le le_rfl⟩
  let ν : Kernel ExactSLEGenerator.Driver UpperPlane :=
    ⟨μ ∞,recoveredMass_measurable a ha s c hc ∞⟩
  let (b : ExactSLEGenerator.Driver) : IsFiniteMeasureOnCompacts (K b) := inferInstanceAs
    (IsFiniteMeasureOnCompacts (μ (S b) b))
  let (b : ExactSLEGenerator.Driver) : IsFiniteMeasureOnCompacts (ν b) := inferInstanceAs
    (IsFiniteMeasureOnCompacts (μ ∞ b))
  have hcv (f : C_c(UpperPlane,ℝ)) : ∀ᵐ b ∂W, Tendsto
      (fun k => ∑j∈s k,c k j*∫z,f z∂actualUpperMass a (Real.exp (-2*a*(j+1))) (S b) b)
      atTop (𝓝 (∫z,f z∂μ (S b) b)) := hconv.mono (fun b hb => hb (S b) f)
  have hct (f : C_c(UpperPlane,ℝ)) : ∀ᵐ b ∂W, Tendsto
      (fun k => ∑j∈s k,c k j*∫z,f z∂actualUpperMass a (Real.exp (-2*a*(j+1))) ∞ b)
      atTop (𝓝 (∫z,f z∂ν b)) := hconv.mono (fun b hb => hb ∞ f)
  have hmom (f : C_c(UpperPlane,ℝ)) (m : ℕ) :
      MemLp (fun b => ∫z,f z∂μ (S b) b) (m:ℝ≥0∞) W :=
    actual_stopped_radon_limit_memLp a ha W hW S hS s c hc hsum _ f (hcv f) m
  have hint (f : C_c(UpperPlane,ℝ)) : Integrable (fun b => ∫z,f z∂K b) W :=
    memLp_one_iff_integrable.mp (by simpa only [K,Kernel.coe_mk,Nat.cast_one] using hmom f 1)
  have htop : IsStoppingTime rawFiltration (fun _ : ExactSLEGenerator.Driver => (∞:ℝ≥0∞)) :=
    fun t => by simp
  have hintop (f : C_c(UpperPlane,ℝ)) : Integrable (fun b => ∫z,f z∂ν b) W :=
    memLp_one_iff_integrable.mp (by simpa only [Nat.cast_one] using
      actual_stopped_radon_limit_memLp a ha W hW _ htop s c hc hsum _ f (hct f) 1)
  have hcond (f : C_c(UpperPlane,ℝ)) (U : Set ExactSLEGenerator.Driver)
      (hU : MeasurableSet[hS.measurableSpace] U) :
      (∫b in U,(∫z,f z∂ν b)-(∫z,f z∂K b)∂W)=
        ∫b in U,(∫z : UpperPlane,f z*stoppedSurvivingGreen a (S b) b z.1∂upperArea)∂W :=
    actual_stopped_limit_compact_conditional a ha W hW S hS s c hs hc hsum
      K ν f (hcv f) (hct f) U hU
  refine ⟨hmeas,hmom,?_,?_,?_⟩
  · intro A hA m
    exact compact_mass_memLp K W (m:ℝ≥0∞) (fun f => hmom f m) A hA
  · intro f
    exact actual_stopped_radon_limit_L1 a ha W hW S hS _ (fun _ => Real.exp_pos _)
      (level_step_le_one a ha) s c hc hsum _ f (hcv f)
  · intro H hH
    exact stopped_compact_conditional_to_random_tests a ha W hW S hS K ν hint hintop hcond H hH

end ExactSLEGreen
end
end
 

 
section
 

noncomputable section
open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
namespace SLEExactGauge.TraceRestriction

variable {X Y : Type*} [MeasurableSpace X] [MetricSpace Y]
  [MeasurableSpace Y] [BorelSpace Y]

lemma firstVisit_finite_of_exhaustion (ν : Measure X)
    (ι : X→Y) (hι : Measurable ι) (γ : ℝ≥0→Y) (hγ : Continuous γ)
    (hlim : ∀A : Set X, MeasurableSet A → Tendsto
      (fun n : ℕ => (ν.restrict (visited ι γ n)) A) atTop (𝓝 (ν A))) :
    ∀ᵐ x ∂ν, firstVisit ι γ x<∞ := by
  let V := ι ⁻¹' range γ
  have hV : MeasurableSet V := by
    rw [show V=⋃n : ℕ,visited ι γ n from (iUnion_visited_nat ι γ).symm]
    exact MeasurableSet.iUnion (fun n => measurableSet_visited ι hι γ hγ n)
  have hz (n : ℕ) : (ν.restrict (visited ι γ n)) Vᶜ=0 := by
    rw [Measure.restrict_apply hV.compl]
    have he : Vᶜ∩visited ι γ n=∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      rintro x ⟨hn,u,hu,he⟩
      exact hn ⟨u,he⟩
    rw [he,measure_empty]
  have hnull : ν Vᶜ=0 := by
    have h := hlim Vᶜ hV.compl
    simp_rw [hz] at h
    exact tendsto_nhds_unique h tendsto_const_nhds
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hnull] with x hx
  apply (firstVisit_lt_top_iff ι γ x).mpr
  exact not_not.mp hx

 
omit [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace Y] in
lemma firstVisit_fiber_subset [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace Y]
    (ι : X→Y) (γ : ℝ≥0→Y) (hγ : Continuous γ)
    (t : ℝ≥0) : {x | firstVisit ι γ x=(t : ℝ≥0∞)}⊆ι ⁻¹' {γ t} := by
  rintro x hx
  change firstVisit ι γ x=(t : ℝ≥0∞) at hx
  by_cases h : ({u : ℝ≥0 | γ u=ι x}).Nonempty
  · have hclosed : IsClosed {u : ℝ≥0 | γ u=ι x} := isClosed_eq hγ continuous_const
    have hmem := hclosed.csInf_mem h ⟨0,fun _ _ => bot_le⟩
    have he : sInf {u : ℝ≥0 | γ u=ι x}=t := by
      apply ENNReal.coe_injective
      simpa only [firstVisit,dite_eq_left h] using hx
    rw [he] at hmem
    exact hmem.symm
  · simp only [firstVisit,dite_eq_right h] at hx
    exact False.elim (ENNReal.coe_ne_top hx.symm)

lemma firstVisit_fiber_null (ν : Measure X) [NullSingletonClass ν]
    (ι : X→Y) (hinj : Function.Injective ι) (γ : ℝ≥0→Y) (hγ : Continuous γ)
    (t : ℝ≥0) : ν {x | firstVisit ι γ x=(t : ℝ≥0∞)}=0 :=
  measure_mono_null (firstVisit_fiber_subset ι γ hγ t)
    (preimage_singleton_null_of_injective ν ι hinj (γ t))

 

lemma restrict_strictFirstVisit (ν : Measure X) [NullSingletonClass ν]
    (ι : X→Y) (hinj : Function.Injective ι) (γ : ℝ≥0→Y) (hγ : Continuous γ)
    (t : ℝ≥0) :
    ν.restrict {x | firstVisit ι γ x<(t : ℝ≥0∞)}=ν.restrict (visited ι γ t) := by
  apply Measure.restrict_congr_set
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp
    (firstVisit_fiber_null ν ι hinj γ hγ t)] with x hx
  apply propext
  rw [←firstVisit_le_iff ι γ hγ x t,lt_iff_le_and_ne]
  exact and_iff_left hx

end SLEExactGauge.TraceRestriction
end
end
 

 
section
 

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology CompactlySupported
open scoped NNReal ENNReal
namespace SLEExactGauge.TraceMassContinuity
open FlowIdentification ExactSLEMain ExactSLEGenerator ExactSLEGreen TraceRestriction

 

structure TraceMassFacts (κ : ℝ) (b : TDriver) (μ : ℝ≥0∞→Measure UpperPlane) : Prop where
  continuous_trace : ContinuousOn (Target.trace κ b) (Ici 0)
  atomless : NullSingletonClass (μ ∞)
  restriction : ∀t : ℝ≥0, μ t=(μ ∞).restrict
    (visited (fun z : UpperPlane => z.1) (internalTrace κ b) t)
  monotone : Monotone μ
  increment_support : ∀s t : ℝ≥0, s≤t → (μ t-μ s)
    {z : UpperPlane | z.1∉internalTrace κ b '' Icc s t}=0
  continuous_tests : ∀f : C_c(UpperPlane,ℝ), Continuous (fun t : ℝ≥0 => ∫z,f z∂μ t)
  local_variation : ∀K : Set UpperPlane, IsCompact K → ∀t : ℝ≥0, Tendsto
    (fun u : ℝ≥0 => ((μ u-μ t)+(μ t-μ u)) K) (𝓝 t) (𝓝 0)
  exhaustion : ∀A : Set UpperPlane, MeasurableSet A → Tendsto
    (fun n : ℕ => μ (n:ℝ≥0) A) atTop (𝓝 (μ ∞ A))
  remaining_decay : ∀K : Set UpperPlane, IsCompact K → Tendsto
    (fun n : ℕ => (μ ∞-μ (n:ℝ≥0)) K) atTop (𝓝 0)
  firstVisit_measurable : Measurable (firstVisit (fun z : UpperPlane => z.1) (internalTrace κ b))
  firstVisit_finite : ∀ᵐ z ∂μ ∞, firstVisit (fun z : UpperPlane => z.1) (internalTrace κ b) z<∞
  firstVisit_identity : ∀t : ℝ≥0, μ t=(μ ∞).restrict
    {z | firstVisit (fun z : UpperPlane => z.1) (internalTrace κ b) z≤(t:ℝ≥0∞)}
  strict_firstVisit_identity : ∀t : ℝ≥0, μ t=(μ ∞).restrict
    {z | firstVisit (fun z : UpperPlane => z.1) (internalTrace κ b) z<(t:ℝ≥0∞)}
  initial_positive : ∀t : ℝ≥0∞, 0<t → 0<μ t univ
  initial_positive_compact : ∀t : ℝ≥0∞, 0<t → ∃K : Set UpperPlane, IsCompact K ∧
    0<μ t K ∧ μ t K<∞

lemma traceMassFacts_of_restrictions (κ : ℝ) (hκ : 0<κ) (b : TDriver)
    (μ : ℝ≥0∞→Measure UpperPlane) [∀v,IsFiniteMeasureOnCompacts (μ v)]
    (hcont : ContinuousOn (Target.trace κ b) (Ici 0))
    (hatom : NullSingletonClass (μ ∞))
    (hres : ∀t : ℝ≥0, μ t=(μ ∞).restrict
      (visited (fun z : UpperPlane => z.1) (internalTrace κ b) t))
    (hexh : ∀A : Set UpperPlane, MeasurableSet A → Tendsto
      (fun n : ℕ => μ (n:ℝ≥0) A) atTop (𝓝 (μ ∞ A)))
    (hrem : ∀K : Set UpperPlane, IsCompact K → Tendsto
      (fun n : ℕ => (μ ∞-μ (n:ℝ≥0)) K) atTop (𝓝 0))
    (hpos : ∀t : ℝ≥0∞, 0<t → 0<μ t univ)
    (hposK : ∀t : ℝ≥0∞, 0<t → ∃K : Set UpperPlane, IsCompact K ∧ 0<μ t K ∧ μ t K<∞) :
    TraceMassFacts κ b μ := by
  let := hatom
  have hγ := continuous_internalTrace hκ b hcont
  refine ⟨hcont,hatom,hres,?_,?_,?_,?_,hexh,hrem,?_,?_,?_,?_,hpos,hposK⟩
  · intro u v huv
    induction v using ENNReal.recTopCoe with
    | top =>
      induction u using ENNReal.recTopCoe with
      | top => exact le_rfl
      | coe u => rw [hres u]; exact Measure.restrict_le_self
    | coe v =>
      have hu : u≠∞ := ne_top_of_le_ne_top ENNReal.coe_ne_top huv
      rw [←ENNReal.coe_toNNReal hu,hres,hres]
      exact Measure.restrict_mono (visited_mono _ _ (by
        apply ENNReal.coe_le_coe.mp
        simpa only [ENNReal.coe_toNNReal hu] using huv)) le_rfl
  · intro s t hst
    rw [hres,hres]
    exact increment_carried_by_segment (μ ∞) _ measurable_subtype_coe _ hγ hst
  · intro f
    simp_rw [hres]
    exact continuous_integral_visited (μ ∞) _ measurable_subtype_coe Subtype.val_injective
      _ hγ f f.integrable
  · intro K hK t
    simp_rw [hres]
    exact local_variation_visited (μ ∞) hκ b hcont K hK.measurableSet hK.measure_lt_top.ne t
  · exact measurable_firstVisit _ measurable_subtype_coe _ hγ
  · apply firstVisit_finite_of_exhaustion (μ ∞) _ measurable_subtype_coe _ hγ
    intro A hA
    simpa only [←hres] using hexh A hA
  · intro t
    rw [hres]
    congr 1
    ext z
    exact (firstVisit_le_iff _ _ hγ z t).symm
  · intro t
    rw [hres,restrict_strictFirstVisit (μ ∞) _ Subtype.val_injective _ hγ]

 

lemma TraceMassFacts.capacity_increment_support {κ : ℝ} (hκ : 0<κ) {b : TDriver}
    {μ : ℝ≥0∞→Measure UpperPlane} (hμ : TraceMassFacts κ b μ)
    (s t : ℝ) (hs : 0 ≤ s) (hst : s ≤ t) :
    (μ ((κ*t).toNNReal : ℝ≥0∞)-μ ((κ*s).toNNReal : ℝ≥0∞))
      {z : UpperPlane | z.1∉Target.trace κ b '' Icc s t}=0 := by
  have hst' : (κ*s).toNNReal≤(κ*t).toNNReal :=
    Real.toNNReal_mono (mul_le_mul_of_nonneg_left hst hκ.le)
  have h := hμ.increment_support _ _ hst'
  have hs0 : 0≤κ*s := mul_nonneg hκ.le hs
  have ht0 : 0≤κ*t := mul_nonneg hκ.le (hs.trans hst)
  simpa only [internalTrace_image hκ,Real.coe_toNNReal _ hs0,Real.coe_toNNReal _ ht0,
    mul_div_cancel_left₀ _ hκ.ne'] using h

end SLEExactGauge.TraceMassContinuity
end
end
 

 
section
 

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
namespace SLEExactGauge.TraceMassContinuity
open GermPositivity

 

def massTimeList (n : ℕ) : ℝ≥0∞ :=
  if n%4=0 then ∞ else if n%4=1 then ((n/4 : ℕ) : ℝ≥0)
    else if n%4=2 then smallTime (n/4)
      else TopologicalSpace.denseSeq ℝ≥0 (n/4)

@[simp] lemma massTimeList_top : massTimeList 0=∞ := by simp [massTimeList]

@[simp] lemma massTimeList_nat (n : ℕ) : massTimeList (4*n+1)=(n : ℝ≥0) := by
  simp [massTimeList,Nat.mul_add_div]

@[simp] lemma massTimeList_small (n : ℕ) : massTimeList (4*n+2)=(smallTime n : ℝ≥0∞) := by
  simp [massTimeList,Nat.mul_add_div]

@[simp] lemma massTimeList_dense (n : ℕ) :
    massTimeList (4*n+3)=(TopologicalSpace.denseSeq ℝ≥0 n : ℝ≥0∞) := by
  simp [massTimeList,Nat.mul_add_div]

lemma massTimeList_is_dense : Dense {u : ℝ≥0 | ∃i,massTimeList i=u} := by
  apply Dense.mono (s₁ := range (TopologicalSpace.denseSeq ℝ≥0)) _
    (TopologicalSpace.denseRange_denseSeq ℝ≥0)
  rintro u ⟨n,rfl⟩
  exact ⟨4*n+3,massTimeList_dense n⟩

end SLEExactGauge.TraceMassContinuity
end
end
 

 
section
 

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology CompactlySupported
open scoped NNReal ENNReal
namespace SLEExactGauge.TraceMassContinuity
open FlowIdentification ExactSLEMain ExactSLEGenerator ExactSLEGreen MassVersions TraceMassIntegration

 

theorem actual_common_trace_mass (κ : ℝ) (hκ : 0<κ) (hκ8 : κ<8)
    (W : Measure TDriver) (hW : Target.IsWiener W) :
    ∃ (s : ℕ→Finset ℕ) (c : ℕ→ℕ→ℝ) (hc : ∀k j,j∈s k→0≤c k j),
      (∀k j,j∈s k→k≤j) ∧ (∀k,∑j∈s k,c k j=1) ∧
      let μ := recoveredMass (Target.a κ) (a_gt_quarter hκ hκ8) s c hc
      (∀v b, IsFiniteMeasureOnCompacts (μ v b) ∧ (μ v b).Regular) ∧
      (∀b, μ 0 b=0) ∧ (∀v, Measurable (μ v)) ∧
      IsProgressive rawFiltration (fun v : ℝ≥0 => μ v) ∧
      μ ∞ ∘ₘ (W.map driverHomeomorph)=initialGreenMeasure (Target.a κ) ∧
      (∀ (S : ExactSLEGenerator.Driver→ℝ≥0∞) (hS : IsStoppingTime rawFiltration S),
        Measurable[hS.measurableSpace] (fun b => μ (S b) b) ∧
        (∀f : C_c(UpperPlane,ℝ), ∀m : ℕ,
          MemLp (fun b => ∫z,f z∂μ (S b) b) (m:ℝ≥0∞) (W.map driverHomeomorph)) ∧
        (∀K : Set UpperPlane, IsCompact K → ∀m : ℕ,
          MemLp (fun b => (μ (S b) b K).toReal) (m:ℝ≥0∞) (W.map driverHomeomorph)) ∧
        (∀f : C_c(UpperPlane,ℝ), Tendsto (fun k => eLpNorm
          (fun b => (∑j∈s k,c k j*∫z,f z∂actualUpperMass (Target.a κ)
            (Real.exp (-2*(Target.a κ)*(j+1))) (S b) b)-(∫z,f z∂μ (S b) b))
              1 (W.map driverHomeomorph)) atTop (𝓝 0)) ∧
        (∀H : ExactSLEGenerator.Driver × UpperPlane→ℝ≥0∞,
          Measurable[hS.measurableSpace.prod (inferInstance : MeasurableSpace UpperPlane)] H →
          (∫⁻b,∫⁻z,H (b,z)∂μ ∞ b∂(W.map driverHomeomorph))=
            (∫⁻b,∫⁻z,H (b,z)∂μ (S b) b∂(W.map driverHomeomorph))+
            ∫⁻b,∫⁻z,H (b,z)*ENNReal.ofReal (stoppedSurvivingGreen (Target.a κ) (S b) b z.1)
              ∂upperArea∂(W.map driverHomeomorph))) ∧
      ∀ᵐ b ∂W, TraceMassFacts κ b (fun v => μ v (driverHomeomorph b)) ∧
        (∀v : ℝ≥0∞, ∀f : C_c(UpperPlane,ℝ), Tendsto
          (fun k => ∑j∈s k,c k j*∫z,f z∂actualUpperMass (Target.a κ)
            (Real.exp (-2*(Target.a κ)*(j+1))) v (driverHomeomorph b))
          atTop (𝓝 (∫z,f z∂μ v (driverHomeomorph b)))) := by
  have hBW := brownian_map_driver W hW
  have : IsProbabilityMeasure (W.map driverHomeomorph) := hBW.isGaussianProcess.isProbabilityMeasure
  obtain ⟨s,c,hc,hs,hsum,hreg,hzero,hmeas,hprog,hmom,hcompact,hL1,hmean,hH,hpath⟩ :=
    actual_raw_mass_trace κ hκ hκ8 W hW massTimeList massTimeList_is_dense
      (fun n => 4*n+1) massTimeList_nat (fun n => 4*n+2) massTimeList_small 0 massTimeList_top
  let μ := recoveredMass (Target.a κ) (a_gt_quarter hκ hκ8) s c hc
  have hcv : ∀ᵐ b ∂(W.map driverHomeomorph), ∀v : ℝ≥0∞, ∀f : C_c(UpperPlane,ℝ),
      Tendsto (fun k => ∑j∈s k,c k j*∫z,f z∂actualUpperMass (Target.a κ)
        (Real.exp (-2*(Target.a κ)*(j+1))) v b) atTop (𝓝 (∫z,f z∂μ v b)) := by
    apply driverMeasurableEquiv.measurableEmbedding.ae_map_iff.mpr
    filter_upwards [hpath] with b hb
    exact hb.2.2.2.1
  refine ⟨s,c,hc,hs,hsum,hreg,hzero,hmeas,hprog,?_,?_,?_⟩
  · simpa only [massTimeList_top] using hmean 0 massTimeList_top
  · exact recoveredMass_all_stopping (Target.a κ) (a_gt_quarter hκ hκ8)
      (W.map driverHomeomorph) hBW s c hc hs hsum hcv
  · filter_upwards [hpath] with b hb
    rcases hb with ⟨hcont,hatom,hres,hconv,hexh,hrem,hpos,hposK⟩
    let (v : ℝ≥0∞) : IsFiniteMeasureOnCompacts (μ v (driverHomeomorph b)) := (hreg _ _).1
    exact ⟨traceMassFacts_of_restrictions κ hκ b (fun v => μ v (driverHomeomorph b))
      hcont hatom hres hexh hrem hpos hposK,hconv⟩

end SLEExactGauge.TraceMassContinuity
end
end
 

 
section
 

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped Classical NNReal ENNReal
namespace SLEExactGauge.LoewnerRestart
open FlowIdentification ExactSLEMain ExactSLEGenerator

 
def concatenate (s : ℝ≥0) (b c : GDriver) : GDriver :=
  ⟨⟨fun u => b.1 (min u s)+c.1 (u-s),
    (b.1.continuous.comp (continuous_id.min continuous_const)).add
      (c.1.continuous.comp (continuous_id.sub continuous_const))⟩,
    by
      change b.1 (min 0 s)+c.1 (0-s)=0
      simp only [min_eq_left (show 0 ≤ s from bot_le),zero_tsub,b.2,c.2,add_zero]⟩

@[simp] lemma concatenate_apply (s u : ℝ≥0) (b c : GDriver) :
    (concatenate s b c).1 u=b.1 (min u s)+c.1 (u-s) := rfl

lemma continuous_concatenate : Continuous (fun p : (ℝ≥0×GDriver)×GDriver =>
    concatenate p.1.1 p.1.2 p.2) := by
  apply Continuous.subtype_mk
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact (continuous_eval.comp
    ((continuous_subtype_val.comp continuous_fst.fst.snd).prodMk
      (continuous_snd.min continuous_fst.fst.fst))).add
    (continuous_eval.comp
      ((continuous_subtype_val.comp continuous_fst.snd).prodMk
        (continuous_snd.sub continuous_fst.fst.fst)))

lemma concatenate_before (s : ℝ≥0) (b c : GDriver) (u : ℝ≥0) (hu : u ≤ s) :
    (concatenate s b c).1 u=b.1 u := by
  simp only [concatenate_apply,min_eq_left hu,tsub_eq_zero_of_le hu,c.2,add_zero]

lemma concatenate_reconstruct (s : ℝ≥0) (b : GDriver) :
    concatenate s (pastDriver s b) (restart s b)=b := by
  apply Subtype.ext
  ext u
  by_cases hu : u ≤ s
  · rw [concatenate_before _ _ _ _ hu,pastDriver_eq _ _ _ hu]
  · have hsu : s ≤ u := le_of_not_ge hu
    simp only [concatenate_apply,min_eq_right hsu,restart_apply,pastDriver_eq s b s le_rfl,
      add_tsub_cancel_of_le hsu]
    ring

 
lemma raw_event_congr {u : ℝ≥0} {A : Set GDriver}
    (hA : MeasurableSet[rawFiltration u] A) {b c : GDriver}
    (h : ∀v ≤ u,b.1 v=c.1 v) : b∈A ↔ c∈A := by
  rw [rawFiltration,Filtration.natural_eq_comap,MeasurableSpace.measurableSet_comap] at hA
  obtain ⟨B,hB,rfl⟩ := hA
  have he : (fun v : Iic u => b.1 v)=(fun v : Iic u => c.1 v) :=
    funext (fun v => h v v.2)
  change (fun v : Iic u => b.1 v)∈B ↔ (fun v : Iic u => c.1 v)∈B
  rw [he]

 
lemma raw_stop_congr {S : GDriver→ℝ≥0∞} (hS : IsStoppingTime rawFiltration S)
    {b c : GDriver} {s : ℝ≥0} (hb : S b=s) (h : ∀u ≤ s,b.1 u=c.1 u) : S c=s := by
  have hc : S c ≤ s := (raw_event_congr (hS s) h).mp (by
    change S b ≤ (s:ℝ≥0∞)
    rw [hb])
  have hcf : S c≠∞ := ne_top_of_le_ne_top ENNReal.coe_ne_top hc
  have hct : (S c).toNNReal ≤ s := ENNReal.coe_le_coe.mp (by
    simpa only [ENNReal.coe_toNNReal hcf] using hc)
  have hbc : S b ≤ S c := by
    have hh := (raw_event_congr (hS (S c).toNNReal)
      (fun u hu => h u (hu.trans hct))).mpr
      (show S c ≤ ((S c).toNNReal:ℝ≥0∞) by rw [ENNReal.coe_toNNReal hcf])
    change S b ≤ ((S c).toNNReal:ℝ≥0∞) at hh
    simpa only [ENNReal.coe_toNNReal hcf] using hh
  exact le_antisymm hc (hb ▸ hbc)

 
def shiftStop (S : GDriver→ℝ≥0∞) (t : ℝ≥0) : GDriver→ℝ≥0∞ := fun b => S b+t

lemma shiftStop_isStoppingTime {S : GDriver→ℝ≥0∞} (hS : IsStoppingTime rawFiltration S)
    (t : ℝ≥0) : IsStoppingTime rawFiltration (shiftStop S t) := by
  intro u
  change MeasurableSet[rawFiltration u] {b | shiftStop S t b ≤ (u:ℝ≥0∞)}
  by_cases htu : t ≤ u
  · have he : {b : GDriver | shiftStop S t b ≤ u}={b | S b ≤ ((u-t:ℝ≥0):ℝ≥0∞)} := by
      ext b
      simp only [shiftStop,mem_ofPred_eq,ENNReal.coe_sub]
      exact (ENNReal.le_sub_iff_add_le_right ENNReal.coe_ne_top
        (ENNReal.coe_le_coe.mpr htu)).symm
    rw [he]
    exact (rawFiltration.mono tsub_le_self) _ (hS (u-t))
  · have he : {b : GDriver | shiftStop S t b ≤ u}=∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro b hb
      exact htu (ENNReal.coe_le_coe.mp ((le_add_left le_rfl).trans hb))
    rw [he]
    exact @MeasurableSet.empty GDriver (rawFiltration u)

lemma measurableSpace_le_shiftStop {S : GDriver→ℝ≥0∞}
    (hS : IsStoppingTime rawFiltration S) (t : ℝ≥0) :
    hS.measurableSpace ≤ (shiftStop_isStoppingTime hS t).measurableSpace :=
  hS.measurableSpace_mono (shiftStop_isStoppingTime hS t) (fun b => show S b ≤ S b+(t:ℝ≥0∞) from le_self_add)

 
lemma raw_stopped_event_congr {S : GDriver→ℝ≥0∞} (hS : IsStoppingTime rawFiltration S)
    {A : Set GDriver} (hA : MeasurableSet[hS.measurableSpace] A)
    {b c : GDriver} {u : ℝ≥0} (hb : S b ≤ u) (h : ∀v ≤ u,b.1 v=c.1 v) : b∈A ↔ c∈A := by
  have hc : S c ≤ u := (raw_event_congr (hS u) h).mp hb
  have hh := raw_event_congr (hA.2 u) h
  change (b∈A ∧ S b ≤ (u:ℝ≥0∞)) ↔ (c∈A ∧ S c ≤ (u:ℝ≥0∞)) at hh
  simpa only [hb,hc,and_true] using hh

 

def concatenatedEvent (S : GDriver→ℝ≥0∞) (A : Set GDriver) :
    Set ((ℝ≥0×GDriver)×GDriver) :=
  {p | S (concatenate p.1.1 p.1.2 p.2) ≤ (p.1.1:ℝ≥0∞) ∧
    concatenate p.1.1 p.1.2 p.2∈A}

lemma concatenatedEvent_measurable {S : GDriver→ℝ≥0∞}
    (hS : IsStoppingTime rawFiltration S) {A : Set GDriver} (hA : MeasurableSet A) :
    MeasurableSet (concatenatedEvent S A) := by
  have : PolishSpace GDriver := (isClosed_eq (continuous_eval_const 0) continuous_const).polishSpace
  have hc : Measurable (fun p : (ℝ≥0×GDriver)×GDriver => concatenate p.1.1 p.1.2 p.2) :=
    continuous_concatenate.measurable
  have ht : Measurable (fun p : (ℝ≥0×GDriver)×GDriver => (p.1.1:ℝ≥0∞)) :=
    ENNReal.continuous_coe.measurable.comp measurable_fst.fst
  exact (measurableSet_le (hS.measurable'.comp hc) ht).inter (hc hA)

lemma concatenatedEvent_past {S : GDriver→ℝ≥0∞}
    (hS : IsStoppingTime rawFiltration S) {t : ℝ≥0} {A : Set GDriver}
    (hA : MeasurableSet[(shiftStop_isStoppingTime hS t).measurableSpace] A)
    (s : ℝ≥0) (b c : GDriver) :
    ((s,b),c)∈concatenatedEvent S A ↔ ((s,b),pastDriver t c)∈concatenatedEvent S A := by
  have hsmall : ∀u ≤ s,(concatenate s b c).1 u=(concatenate s b (pastDriver t c)).1 u := by
    intro u hu
    rw [concatenate_before _ _ _ _ hu,concatenate_before _ _ _ _ hu]
  have hlong : ∀u ≤ s+t,(concatenate s b c).1 u=(concatenate s b (pastDriver t c)).1 u := by
    intro u hu
    simp only [concatenate_apply]
    rw [pastDriver_eq t c (u-s) (tsub_le_iff_right.mpr (by simpa only [add_comm] using hu))]
  have hg := raw_event_congr (hS s) hsmall
  change (S (concatenate s b c) ≤ (s:ℝ≥0∞) ∧ concatenate s b c∈A) ↔
    (S (concatenate s b (pastDriver t c)) ≤ (s:ℝ≥0∞) ∧
      concatenate s b (pastDriver t c)∈A)
  change (S (concatenate s b c) ≤ (s:ℝ≥0∞)) ↔
    (S (concatenate s b (pastDriver t c)) ≤ (s:ℝ≥0∞)) at hg
  rw [←hg]
  apply and_congr_right
  intro h
  exact raw_stopped_event_congr (shiftStop_isStoppingTime hS t) hA
    (by
      change S (concatenate s b c)+(t:ℝ≥0∞) ≤ ((s+t:ℝ≥0):ℝ≥0∞)
      rw [ENNReal.coe_add]
      exact add_le_add h le_rfl) hlong

lemma concatenatedEvent_raw_joint {S : GDriver→ℝ≥0∞}
    (hS : IsStoppingTime rawFiltration S) {t : ℝ≥0} {A : Set GDriver}
    (hA : MeasurableSet[(shiftStop_isStoppingTime hS t).measurableSpace] A) :
    @MeasurableSet ((ℝ≥0×GDriver)×GDriver)
      ((inferInstance : MeasurableSpace (ℝ≥0×GDriver)).prod (rawFiltration t))
      (concatenatedEvent S A) := by
  have hM : @Measurable ((ℝ≥0×GDriver)×GDriver) ((ℝ≥0×GDriver)×GDriver)
      ((inferInstance : MeasurableSpace (ℝ≥0×GDriver)).prod (rawFiltration t)) inferInstance
      (fun p => (p.1,pastDriver t p.2)) :=
    measurable_fst.prodMk ((pastDriver_raw_measurable t).comp measurable_snd)
  have hh := hM (concatenatedEvent_measurable hS
    ((shiftStop_isStoppingTime hS t).measurableSpace_le A hA))
  convert hh using 1
  ext p
  exact concatenatedEvent_past hS hA p.1.1 p.1.2 p.2

lemma concatenatedEvent_stoppedData {S : GDriver→ℝ≥0∞} {A : Set GDriver}
    {b : GDriver} (hb : S b≠∞) :
    (stoppedData S b,restartAt S b)∈concatenatedEvent S A ↔ b∈A := by
  simp only [concatenatedEvent,stoppedData,restartAt,mem_ofPred_eq,concatenate_reconstruct,
    ENNReal.coe_toNNReal hb,le_refl,true_and]

end SLEExactGauge.LoewnerRestart
end
end

end OAI
