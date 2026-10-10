import Mathlib
import OAI.Probability.SLE.MomentGauge
import OAI.Probability.SLEGauge.RawRestartTests

namespace OAI

/-! Hausdorff gauges, Loewner evolution and trace measures. -/

section
 
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped Classical NNReal ENNReal
namespace SLEExactGauge.MassVersions

lemma measurable_random_restrict {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (K : Kernel Ω X) [IsSFiniteKernel K] {A : Set (Ω×X)} (hA : MeasurableSet A) :
    Measurable (fun ω => (K ω).restrict {x | (ω,x)∈A}) := by
  let F : Ω→X→ℝ≥0∞ := fun ω x => if (ω,x)∈A then 1 else 0
  have hF : Measurable (Function.uncurry F) := by
    change Measurable (fun p : Ω×X => if p∈A then (1:ℝ≥0∞) else 0)
    exact Measurable.ite hA measurable_const measurable_const
  have he (ω : Ω) : K.withDensity F ω=(K ω).restrict {x | (ω,x)∈A} := by
    rw [Kernel.withDensity_apply K hF]
    change (K ω).withDensity ({x | (ω,x)∈A}.indicator (fun _ => 1))=_
    have hB : MeasurableSet {x | (ω,x)∈A} := hA.preimage (measurable_const.prodMk measurable_id)
    rw [withDensity_indicator hB]
    exact MeasureTheory.withDensity_one
  have he' : (K.withDensity F : Ω→Measure X)=(fun ω => (K ω).restrict {x | (ω,x)∈A}) := funext he
  rw [←he']
  exact (K.withDensity F).measurable

end SLEExactGauge.MassVersions
end
end
 

 
section
 

noncomputable section
open MeasureTheory Filter Set Topology
open scoped Classical NNReal ENNReal
namespace SLEExactGauge.TraceRestriction
variable {X Y : Type*} [MeasurableSpace X] [MetricSpace Y]
    [MeasurableSpace Y] [BorelSpace Y]

lemma tendsto_integral_visited_atTop (ν : Measure X)
    (ι : X→Y) (hι : Measurable ι) (γ : ℝ≥0→Y) (hγ : Continuous γ)
    (hfull : ∀ᵐ x ∂ν, ι x∈range γ) (f : X→ℝ) (hf : Integrable f ν) :
    Tendsto (fun t : ℝ≥0 => ∫x in visited ι γ t,f x∂ν) atTop (𝓝 (∫x,f x∂ν)) := by
  simp_rw [←integral_indicator (measurableSet_visited ι hι γ hγ _)]
  apply tendsto_integral_filter_of_dominated_convergence (fun x => ‖f x‖)
  · exact Eventually.of_forall (fun t => hf.aestronglyMeasurable.indicator
      (measurableSet_visited ι hι γ hγ t))
  · exact Eventually.of_forall (fun _ => Eventually.of_forall fun _ => norm_indicator_le_norm_self _ _)
  · exact hf.norm
  · filter_upwards [hfull] with x hx
    obtain ⟨u,hu⟩ := hx
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop u] with t ht
    exact (indicator_of_mem (show x∈visited ι γ t from ⟨u,⟨bot_le,ht⟩,hu⟩) f).symm

lemma continuous_integral_restrict_visited (ν : Measure X) [NullSingletonClass ν]
    (ι : X→Y) (hι : Measurable ι) (hinj : Function.Injective ι)
    (γ : ℝ≥0→Y) (hγ : Continuous γ) {A : Set X} (hA : MeasurableSet A)
    (f : X→ℝ) (hf : Integrable f ν) :
    Continuous (fun t : ℝ≥0 => ∫x,f x∂(ν.restrict (visited ι γ t)).restrict A) := by
  simp_rw [←integral_indicator hA]
  exact continuous_integral_visited ν ι hι hinj γ hγ (A.indicator f) (hf.indicator hA)

lemma tendsto_integral_restrict_visited_atTop (ν : Measure X)
    (ι : X→Y) (hι : Measurable ι) (γ : ℝ≥0→Y) (hγ : Continuous γ)
    (hfull : ∀ᵐ x ∂ν, ι x∈range γ) {A : Set X} (hA : MeasurableSet A)
    (f : X→ℝ) (hf : Integrable f ν) :
    Tendsto (fun t : ℝ≥0 => ∫x,f x∂(ν.restrict (visited ι γ t)).restrict A)
      atTop (𝓝 (∫x in A,f x∂ν)) := by
  simp_rw [←integral_indicator hA]
  exact tendsto_integral_visited_atTop ν ι hι γ hγ hfull (A.indicator f) (hf.indicator hA)

end SLEExactGauge.TraceRestriction
end
end
 

 
section
 

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology CompactlySupported
open scoped Classical NNReal ENNReal
namespace SLEExactGauge.LoewnerRestart
open FlowIdentification ExactSLEMain ExactSLEGreen ExactSLEGenerator MassVersions
open TraceRestriction TraceMassContinuity TraceMassIntegration

lemma measurableSet_alive_atStop_raw (a : ℝ) (ha : 1/4<a)
    {S : GDriver→ℝ≥0∞} (hS : IsStoppingTime rawFiltration S) :
    MeasurableSet[hS.measurableSpace.prod (inferInstance : MeasurableSpace UpperPlane)]
      {p : GDriver×UpperPlane | alive a p.1.1 (S p.1).toNNReal p.2.1} := by
  have hD := stoppedData_raw_measurable hS
  have hin : @Measurable (GDriver×UpperPlane) (ℝ≥0×(GDriver×UpperPlane))
      (hS.measurableSpace.prod inferInstance) inferInstance (fun p =>
      ((stoppedData S p.1).1,((stoppedData S p.1).2,p.2))) :=
    (hD.fst.comp measurable_fst).prodMk ((hD.snd.comp measurable_fst).prodMk measurable_snd)
  have he : {p : GDriver×UpperPlane | alive a p.1.1 (S p.1).toNNReal p.2.1}=
      (fun p : GDriver×UpperPlane => ((stoppedData S p.1).1,((stoppedData S p.1).2,p.2))) ⁻¹'
        {p : ℝ≥0×(GDriver×UpperPlane) | alive a p.2.1.1 p.1 p.2.2.1} := by
    ext p
    exact (alive_driver_congr (pastDriver_eq (S p.1).toNNReal p.1)).symm
  rw [he]
  exact (measurableSet_alive_joint a ha).preimage hin

lemma measurableSet_alive_spatial (a : ℝ) (b : GDriver) (t : ℝ≥0) :
    MeasurableSet {z : UpperPlane | alive a b.1 t z.1} :=
  ((isOpen_alive b.1.continuous t).preimage continuous_subtype_val).measurableSet

 
def recoveredPostStop (a : ℝ) (ha : 1/4<a)
    (s : ℕ→Finset ℕ) (c : ℕ→ℕ→ℝ) (hc : ∀k j,j∈s k→0≤c k j)
    (S : GDriver→ℝ≥0∞) (v : ℝ≥0∞) (b : GDriver) : Measure UpperPlane :=
  if S b=∞ then 0 else (recoveredMass a ha s c hc (S b+v) b).restrict
    {z : UpperPlane | alive a b.1 (S b).toNNReal z.1}

lemma recoveredPostStop_raw_measurable (a : ℝ) (ha : 1/4<a)
    (s : ℕ→Finset ℕ) (c : ℕ→ℕ→ℝ) (hc : ∀k j,j∈s k→0≤c k j)
    {S : GDriver→ℝ≥0∞} (hS : IsStoppingTime rawFiltration S) (t : ℝ≥0) :
    Measurable[(afterStopFiltration hS) t] (recoveredPostStop a ha s c hc S t) := by
  let : MeasurableSpace GDriver := (afterStopFiltration hS) t
  let K : Kernel GDriver UpperPlane := ⟨fun b => recoveredMass a ha s c hc (S b+t) b,
    recoveredMass_stopping_raw_measurable a ha s c hc _ (shiftStop_isStoppingTime hS t)⟩
  let (b : GDriver) : IsFiniteMeasureOnCompacts (K b) := radonLimit_finite _
  have : IsSFiniteKernel K := isSFiniteKernel_of_locally_finite K
  have hA : MeasurableSet {p : GDriver×UpperPlane | alive a p.1.1 (S p.1).toNNReal p.2.1} :=
    (prod_sigma_le (measurableSpace_le_shiftStop hS t) _ ) _ (measurableSet_alive_atStop_raw a ha hS)
  have htop : MeasurableSet {b : GDriver | S b=∞} :=
    (measurableSpace_le_shiftStop hS t) _ (hS.measurable (measurableSet_singleton ∞))
  exact Measurable.ite htop measurable_const (measurable_random_restrict K hA)

lemma recoveredPostStop_terminal_measurable (a : ℝ) (ha : 1/4<a)
    (s : ℕ→Finset ℕ) (c : ℕ→ℕ→ℝ) (hc : ∀k j,j∈s k→0≤c k j)
    {S : GDriver→ℝ≥0∞} (hS : IsStoppingTime rawFiltration S) :
    Measurable (recoveredPostStop a ha s c hc S ∞) := by
  let K : Kernel GDriver UpperPlane := ⟨recoveredMass a ha s c hc ∞,
    recoveredMass_measurable a ha s c hc ∞⟩
  let (b : GDriver) : IsFiniteMeasureOnCompacts (K b) := radonLimit_finite _
  have : IsSFiniteKernel K := isSFiniteKernel_of_locally_finite K
  have hA : MeasurableSet {p : GDriver×UpperPlane | alive a p.1.1 (S p.1).toNNReal p.2.1} :=
    (prod_sigma_le hS.measurableSpace_le _) _ (measurableSet_alive_atStop_raw a ha hS)
  have htop : MeasurableSet {b : GDriver | S b=∞} := hS.measurable' (measurableSet_singleton ∞)
  have hh : Measurable (fun b : GDriver => if S b=∞ then (0:Measure UpperPlane) else
      (K b).restrict {z | alive a b.1 (S b).toNNReal z.1}) :=
    Measurable.ite htop measurable_const (measurable_random_restrict K hA)
  change Measurable (fun b => recoveredPostStop a ha s c hc S ∞ b)
  simpa only [recoveredPostStop,add_top,K,Kernel.coe_mk] using hh

lemma recoveredPostStop_measurable (a : ℝ) (ha : 1/4<a)
    (s : ℕ→Finset ℕ) (c : ℕ→ℕ→ℝ) (hc : ∀k j,j∈s k→0≤c k j)
    {S : GDriver→ℝ≥0∞} (hS : IsStoppingTime rawFiltration S) (v : ℝ≥0∞) :
    Measurable (recoveredPostStop a ha s c hc S v) := by
  induction v using ENNReal.recTopCoe with
  | top => exact recoveredPostStop_terminal_measurable a ha s c hc hS
  | coe t =>
    exact (recoveredPostStop_raw_measurable a ha s c hc hS t).mono
      ((afterStopFiltration hS).le t) le_rfl

lemma recoveredPostStop_finiteOnCompacts (a : ℝ) (ha : 1/4<a)
    (s : ℕ→Finset ℕ) (c : ℕ→ℕ→ℝ) (hc : ∀k j,j∈s k→0≤c k j)
    (S : GDriver→ℝ≥0∞) (v : ℝ≥0∞) (b : GDriver) :
    IsFiniteMeasureOnCompacts (recoveredPostStop a ha s c hc S v b) := by
  unfold recoveredPostStop
  split_ifs
  · infer_instance
  · let : IsFiniteMeasureOnCompacts (recoveredMass a ha s c hc (S b+v) b) := radonLimit_finite _
    infer_instance

lemma recoveredPostStop_compact_stronglyAdapted (a : ℝ) (ha : 1/4<a)
    (s : ℕ→Finset ℕ) (c : ℕ→ℕ→ℝ) (hc : ∀k j,j∈s k→0≤c k j)
    {S : GDriver→ℝ≥0∞} (hS : IsStoppingTime rawFiltration S) (f : C_c(UpperPlane,ℝ)) :
    StronglyAdapted (afterStopFiltration hS)
      (fun t : ℝ≥0 => fun b => ∫z,f z∂recoveredPostStop a ha s c hc S t b) := by
  intro t
  let : MeasurableSpace GDriver := (afterStopFiltration hS) t
  let K : Kernel GDriver UpperPlane := ⟨recoveredPostStop a ha s c hc S t,
    recoveredPostStop_raw_measurable a ha s c hc hS t⟩
  exact f.continuous.stronglyMeasurable.integral_kernel (κ:=K)

end SLEExactGauge.LoewnerRestart
end
end
 

 
section
 

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology CompactlySupported
open scoped NNReal ENNReal
namespace SLEExactGauge.MassVersions
variable {Ω X : Type*} [MeasurableSpace Ω]
    [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]

theorem ae_finiteOnCompacts_of_average (K : Kernel Ω X) (W : Measure Ω)
    [IsFiniteMeasureOnCompacts (K ∘ₘ W)] :
    ∀ᵐ ω ∂W, IsFiniteMeasureOnCompacts (K ω) := by
  let C := CompactExhaustion.choice X
  have hn (n : ℕ) : ∀ᵐ ω ∂W, K ω (C n)<∞ := by
    apply ae_lt_top (K.measurable_coe (C.isCompact n).measurableSet)
    rw [←Measure.bind_apply (C.isCompact n).measurableSet K.aemeasurable]
    exact (C.isCompact n).measure_lt_top.ne
  filter_upwards [ae_all_iff.mpr hn] with ω hω
  constructor
  intro A hA
  obtain ⟨n,hn⟩ := C.exists_superset_of_isCompact hA
  exact (measure_mono hn).trans_lt (hω n)

omit [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X] in
lemma compact_eval_integrable_of_average [T2Space X] [LocallyCompactSpace X]
    [SecondCountableTopology X] (K : Kernel Ω X) (W : Measure Ω)
    [IsFiniteMeasureOnCompacts (K ∘ₘ W)] (f : C_c(X,ℝ)) :
    Integrable (fun ω => ∫x,f x∂K ω) W := by
  have hi : Integrable f (K ∘ₘ W) := f.integrable
  rw [Measure.comp_eq_comp_const_apply] at hi
  exact hi.integral_comp

lemma ae_compact_integrable_of_average (K : Kernel Ω X) (W : Measure Ω)
    [IsFiniteMeasureOnCompacts (K ∘ₘ W)] :
    ∀ᵐ ω ∂W, ∀f : C_c(X,ℝ), Integrable f (K ω) := by
  filter_upwards [ae_finiteOnCompacts_of_average K W] with ω hω f
  let := hω
  exact f.integrable

end SLEExactGauge.MassVersions
end
end
 

 
section
 

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology CompactlySupported
open scoped Classical NNReal ENNReal
namespace SLEExactGauge.LoewnerRestart
open FlowIdentification ExactSLEMain ExactSLEGreen ExactSLEGenerator MassVersions
open TraceRestriction TraceMassContinuity TraceMassIntegration

lemma recoveredPostStop_terminal_le (a : ℝ) (ha : 1/4<a)
    (s : ℕ→Finset ℕ) (c : ℕ→ℕ→ℝ) (hc : ∀k j,j∈s k→0≤c k j)
    (S : GDriver→ℝ≥0∞) (b : GDriver) :
    recoveredPostStop a ha s c hc S ∞ b≤recoveredMass a ha s c hc ∞ b := by
  unfold recoveredPostStop
  split_ifs
  · exact bot_le
  · simp only [add_top]
    exact Measure.restrict_le_self

lemma recoveredPostStop_terminal_integrable (a : ℝ) (ha : 1/4<a)
    (s : ℕ→Finset ℕ) (c : ℕ→ℕ→ℝ) (hc : ∀k j,j∈s k→0≤c k j)
    (W : Measure GDriver)
    (hmean : recoveredMass a ha s c hc ∞ ∘ₘ W=initialGreenMeasure a)
    {S : GDriver→ℝ≥0∞} (hS : IsStoppingTime rawFiltration S) (f : C_c(UpperPlane,ℝ)) :
    Integrable (fun b => ∫z,f z∂recoveredPostStop a ha s c hc S ∞ b) W := by
  let K : Kernel GDriver UpperPlane := ⟨recoveredPostStop a ha s c hc S ∞,
    recoveredPostStop_terminal_measurable a ha s c hc hS⟩
  have hle : K ∘ₘ W ≤ initialGreenMeasure a := by
    rw [←hmean]
    apply Measure.le_iff.mpr
    intro A hA
    rw [Measure.bind_apply hA K.aemeasurable,
      Measure.bind_apply hA (recoveredMass_measurable a ha s c hc ∞).aemeasurable]
    exact lintegral_mono (fun b => (recoveredPostStop_terminal_le a ha s c hc S b) A)
  let : IsFiniteMeasureOnCompacts (K ∘ₘ W) :=
    ⟨fun A hA => (hle A).trans_lt hA.measure_lt_top⟩
  exact compact_eval_integrable_of_average K W f

lemma recoveredPostStop_zero_of_convergence (a : ℝ) (ha : 1/4<a)
    (s : ℕ→Finset ℕ) (c : ℕ→ℕ→ℝ) (hc : ∀k j,j∈s k→0≤c k j)
    (hs : ∀k j,j∈s k→k≤j) (S : GDriver→ℝ≥0∞) (b : GDriver)
    (hconv : ∀v : ℝ≥0∞, ∀f : C_c(UpperPlane,ℝ), Tendsto
      (fun k => ∑j∈s k,c k j*∫z,f z∂actualUpperMass a
        (Real.exp (-2*a*(j+1))) v b)
      atTop (𝓝 (∫z,f z∂recoveredMass a ha s c hc v b))) :
    recoveredPostStop a ha s c hc S 0 b=0 := by
  unfold recoveredPostStop
  split_ifs with hb
  · rfl
  · rw [add_zero,←ENNReal.coe_toNNReal hb]
    let : IsFiniteMeasureOnCompacts (recoveredMass a ha s c hc (S b).toNNReal b) :=
      radonLimit_finite _
    apply Measure.restrict_eq_zero.mpr
    exact actual_limit_past_hull_support a ha s c hs b (S b).toNNReal _
      (hconv (S b).toNNReal)

 

theorem recoveredPostStop_path_properties (κ : ℝ) (hκ : 0<κ) (hκ8 : κ<8)
    (W : Measure GDriver) (s : ℕ→Finset ℕ) (c : ℕ→ℕ→ℝ)
    (hc : ∀k j,j∈s k→0≤c k j) (hs : ∀k j,j∈s k→k≤j)
    (hpath : ∀ᵐ b ∂W, TraceMassFacts κ (driverHomeomorph.symm b)
      (fun v => recoveredMass (Target.a κ) (a_gt_quarter hκ hκ8) s c hc v b))
    (hconv : ∀ᵐ b ∂W, ∀v : ℝ≥0∞, ∀f : C_c(UpperPlane,ℝ), Tendsto
      (fun k => ∑j∈s k,c k j*∫z,f z∂actualUpperMass (Target.a κ)
        (Real.exp (-2*(Target.a κ)*(j+1))) v b)
      atTop (𝓝 (∫z,f z∂recoveredMass (Target.a κ) (a_gt_quarter hκ hκ8) s c hc v b)))
    (S : GDriver→ℝ≥0∞) :
    let ν := recoveredPostStop (Target.a κ) (a_gt_quarter hκ hκ8) s c hc S
    ∀ᵐ b ∂W, ν 0 b=0 ∧ Monotone (fun v => ν v b) ∧
      (∀f : C_c(UpperPlane,ℝ), Continuous (fun t : ℝ≥0 => ∫z,f z∂ν t b) ∧
        Tendsto (fun t : ℝ≥0 => ∫z,f z∂ν t b) atTop (𝓝 (∫z,f z∂ν ∞ b))) := by
  intro ν
  let a := Target.a κ
  have ha : 1/4<a := a_gt_quarter hκ hκ8
  let μ := recoveredMass a ha s c hc
  filter_upwards [hpath,hconv] with b hp hcv
  refine ⟨recoveredPostStop_zero_of_convergence a ha s c hc hs S b hcv,?_,?_⟩
  · intro v w hvw
    change (if S b=∞ then 0 else (μ (S b+v) b).restrict _ )≤
      if S b=∞ then 0 else (μ (S b+w) b).restrict _
    split_ifs
    · exact le_rfl
    · exact Measure.restrict_mono le_rfl (hp.monotone (add_le_add le_rfl hvw))
  · by_cases hb : S b=∞
    · have he (v : ℝ≥0∞) : ν v b=0 := by simp only [ν,recoveredPostStop,hb,ite_true]
      simp only [he,integral_zero_measure]
      exact fun _ => ⟨continuous_const,tendsto_const_nhds⟩
    · let A : Set UpperPlane := {z | alive a b.1 (S b).toNNReal z.1}
      have hA : MeasurableSet A := measurableSet_alive_spatial a b _
      have he (t : ℝ≥0) : ν t b=(μ (((S b).toNNReal+t : ℝ≥0) : ℝ≥0∞) b).restrict A := by
        simp only [ν,recoveredPostStop,ite_eq_right hb,μ,ENNReal.coe_add,ENNReal.coe_toNNReal hb,A,a]
      have het : ν ∞ b=(μ ∞ b).restrict A := by
        simp only [ν,recoveredPostStop,ite_eq_right hb,add_top,μ,A,a]
      change TraceMassFacts κ (driverHomeomorph.symm b) (fun v => μ v b) at hp
      let := hp.atomless
      let : IsFiniteMeasureOnCompacts (μ ∞ b) := radonLimit_finite _
      have hγ := continuous_internalTrace hκ _ hp.continuous_trace
      have hfull : ∀ᵐ z ∂μ ∞ b, z.1∈range (internalTrace κ (driverHomeomorph.symm b)) := by
        filter_upwards [hp.firstVisit_finite] with z hz
        exact (firstVisit_lt_top_iff _ _ _).mp hz
      have hshift : Tendsto (fun t : ℝ≥0 => (S b).toNNReal+t) atTop atTop := by
        apply tendsto_atTop.mpr
        intro u
        filter_upwards [eventually_ge_atTop u] with t ht
        exact ht.trans (le_add_self)
      intro f
      simp_rw [he,het,hp.restriction]
      exact ⟨(continuous_integral_restrict_visited (μ ∞ b) _ measurable_subtype_coe
        Subtype.val_injective _ hγ hA f f.integrable).comp (continuous_const.add continuous_id),
        (tendsto_integral_restrict_visited_atTop (μ ∞ b) _ measurable_subtype_coe _
          hγ hfull hA f f.integrable).comp hshift⟩

end SLEExactGauge.LoewnerRestart
end
end
 

 
section
 

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology CompactlySupported
open scoped Classical NNReal ENNReal
namespace SLEExactGauge.LoewnerRestart
open FlowIdentification ExactSLEMain ExactSLEGreen ExactSLEGenerator MassVersions

lemma restartPush_integral (a : ℝ) (ha : 1/4<a) (b : GDriver) (s : ℝ≥0)
    (μ : Measure UpperPlane) {f : UpperPlane→ℝ} (hf : Measurable f) :
    (∫z,f z∂restartPush a (lt_trans (by norm_num) ha) b s μ)=
      ∫w,(restartWeight a b s w).toReal*f (inverseUpper a (lt_trans (by norm_num) ha) b s w)∂μ := by
  have hJ := (continuous_inverseUpper a (lt_trans (by norm_num) ha) b s).measurable
  rw [restartPush,integral_map hJ.aemeasurable hf.aestronglyMeasurable,
    integral_withDensity_eq_integral_toReal_smul (restartWeight_measurable a ha b s)
      (Eventually.of_forall (fun w => lt_top_iff_ne_top.mpr (restartWeight_ne_top a b s w)))]
  rfl

lemma integrable_restartPush_iff (a : ℝ) (ha : 1/4<a) (b : GDriver) (s : ℝ≥0)
    (μ : Measure UpperPlane) {f : UpperPlane→ℝ} (hf : Measurable f) :
    Integrable f (restartPush a (lt_trans (by norm_num) ha) b s μ) ↔
      Integrable (fun w => (restartWeight a b s w).toReal*
        f (inverseUpper a (lt_trans (by norm_num) ha) b s w)) μ := by
  have hJ := (continuous_inverseUpper a (lt_trans (by norm_num) ha) b s).measurable
  rw [restartPush,integrable_map_measure hf.aestronglyMeasurable hJ.aemeasurable,
    integrable_withDensity_iff_integrable_smul' (restartWeight_measurable a ha b s)
      (Eventually.of_forall (fun w => lt_top_iff_ne_top.mpr (restartWeight_ne_top a b s w)))]
  rfl

lemma restartPush_mono (a : ℝ) (ha : 0<a) (b : GDriver) (s : ℝ≥0)
    {μ ν : Measure UpperPlane} (h : μ≤ν) :
    restartPush a ha b s μ≤restartPush a ha b s ν := by
  apply Measure.map_mono _ (continuous_inverseUpper a ha b s).measurable
  apply Measure.le_iff.mpr
  intro A hA
  rw [withDensity_apply _ hA,withDensity_apply _ hA]
  exact lintegral_mono' (Measure.restrict_mono le_rfl h) le_rfl

lemma ae_restartAt {W : Measure GDriver}
    (hW : IsBrownianReal (fun t (b : GDriver) => b.1 t) W)
    {S : GDriver→ℝ≥0∞} (hS : IsStoppingTime rawFiltration S)
    {p : GDriver→Prop} (hp : ∀ᵐ b ∂W, p b) :
    ∀ᵐ b ∂W, S b≠∞ → p (restartAt S b) := by
  apply (ae_restrict_iff' (hS.measurable' (measurableSet_singleton ∞)).compl).mp
  apply ae_of_ae_map (measurable_restartAt hS).aemeasurable
  have he := map_restartAt_restrict hW hS (A:=univ) MeasurableSet.univ
  rw [univ_inter] at he
  change ∀ᵐ b ∂(W.restrict {b | S b≠∞}).map (restartAt S), p b
  rw [he]
  exact Measure.ae_smul_measure hp _

 

theorem restartCandidateKernel_terminal_regular (a : ℝ) (ha : 1/4<a)
    (μ : Kernel GDriver UpperPlane) [IsSFiniteKernel μ] (W : Measure GDriver)
    (hW : IsBrownianReal (fun t (b : GDriver) => b.1 t) W)
    (hμ : μ ∘ₘ W=initialGreenMeasure a)
    (S : GDriver→ℝ≥0∞) (hS : IsStoppingTime rawFiltration S) :
    (∀ᵐ b ∂W, IsFiniteMeasureOnCompacts (restartCandidateKernel a ha μ S hS b) ∧
      (restartCandidateKernel a ha μ S hS b).Regular) ∧
    ∀f : C_c(UpperPlane,ℝ), Integrable
      (fun b => ∫z,f z∂restartCandidateKernel a ha μ S hS b) W := by
  let K := restartCandidateKernel a ha μ S hS
  have hav : K ∘ₘ W ≤ initialGreenMeasure a :=
    restartCandidateKernel_average_le_initial a ha μ W hW hμ S hS
  let : IsFiniteMeasureOnCompacts (K ∘ₘ W) := ⟨fun A hA =>
    (hav A).trans_lt hA.measure_lt_top⟩
  refine ⟨?_,compact_eval_integrable_of_average K W⟩
  filter_upwards [ae_finiteOnCompacts_of_average K W] with b hb
  let := hb
  exact ⟨hb,inferInstance⟩

end SLEExactGauge.LoewnerRestart
end
end
 

 
section
 

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology CompactlySupported
open scoped Classical NNReal ENNReal
namespace SLEExactGauge.LoewnerRestart
open FlowIdentification ExactSLEMain ExactSLEGreen ExactSLEGenerator MassVersions TraceRestriction
open TraceMassContinuity TraceMassIntegration

lemma continuous_restartPush_visited (a : ℝ) (ha : 1/4<a) (b : GDriver) (s : ℝ≥0)
    (ν : Measure UpperPlane) [NullSingletonClass ν] (γ : ℝ≥0→ℂ) (hγ : Continuous γ)
    {f : UpperPlane→ℝ} (hf : Measurable f)
    (hfi : Integrable f (restartPush a (lt_trans (by norm_num) ha) b s ν)) :
    Continuous (fun t : ℝ≥0 => ∫z,f z∂restartPush a (lt_trans (by norm_num) ha)
      b s (ν.restrict (visited (fun z : UpperPlane => z.1) γ t))) := by
  simp_rw [restartPush_integral a ha b s _ hf]
  exact continuous_integral_visited ν _ measurable_subtype_coe Subtype.val_injective γ hγ _
    ((integrable_restartPush_iff a ha b s ν hf).mp hfi)

lemma tendsto_restartPush_visited_atTop (a : ℝ) (ha : 1/4<a) (b : GDriver) (s : ℝ≥0)
    (ν : Measure UpperPlane) (γ : ℝ≥0→ℂ) (hγ : Continuous γ)
    (hfull : ∀ᵐ z ∂ν, z.1∈range γ) {f : UpperPlane→ℝ} (hf : Measurable f)
    (hfi : Integrable f (restartPush a (lt_trans (by norm_num) ha) b s ν)) :
    Tendsto (fun t : ℝ≥0 => ∫z,f z∂restartPush a (lt_trans (by norm_num) ha)
      b s (ν.restrict (visited (fun z : UpperPlane => z.1) γ t))) atTop
      (𝓝 (∫z,f z∂restartPush a (lt_trans (by norm_num) ha) b s ν)) := by
  simp_rw [restartPush_integral a ha b s _ hf]
  exact tendsto_integral_visited_atTop ν _ measurable_subtype_coe γ hγ hfull _
    ((integrable_restartPush_iff a ha b s ν hf).mp hfi)

 

theorem recoveredRestart_path_properties (κ : ℝ) (hκ : 0<κ) (hκ8 : κ<8)
    (W : Measure GDriver) (hW : IsBrownianReal (fun t (b : GDriver) => b.1 t) W)
    (s : ℕ→Finset ℕ) (c : ℕ→ℕ→ℝ) (hc : ∀k j,j∈s k→0≤c k j)
    (hmean : recoveredMass (Target.a κ) (a_gt_quarter hκ hκ8) s c hc ∞ ∘ₘ W=
      initialGreenMeasure (Target.a κ))
    (hpath : ∀ᵐ b ∂W, TraceMassFacts κ (driverHomeomorph.symm b)
      (fun v => recoveredMass (Target.a κ) (a_gt_quarter hκ hκ8) s c hc v b))
    {S : GDriver→ℝ≥0∞} (hS : IsStoppingTime rawFiltration S) :
    let ν := recoveredRestart (Target.a κ) (a_gt_quarter hκ hκ8) s c hc S
    (∀f : C_c(UpperPlane,ℝ), Integrable (fun b => ∫z,f z∂ν ∞ b) W) ∧
    (∀ᵐ b ∂W, (∀v, IsFiniteMeasureOnCompacts (ν v b) ∧ (ν v b).Regular) ∧
      ν 0 b=0 ∧ Monotone (fun v => ν v b) ∧
      (∀f : C_c(UpperPlane,ℝ), Continuous (fun t : ℝ≥0 => ∫z,f z∂ν t b) ∧
        Tendsto (fun t : ℝ≥0 => ∫z,f z∂ν t b) atTop (𝓝 (∫z,f z∂ν ∞ b)))) := by
  intro ν
  let a := Target.a κ
  have ha : 1/4<a := a_gt_quarter hκ hκ8
  let μ := recoveredMass a ha s c hc
  let K : Kernel GDriver UpperPlane := ⟨μ ∞,recoveredMass_measurable a ha s c hc ∞⟩
  let (b : GDriver) : IsFiniteMeasureOnCompacts (K b) := radonLimit_finite _
  have : IsSFiniteKernel K := isSFiniteKernel_of_locally_finite K
  have hreg := restartCandidateKernel_terminal_regular a ha K W hW hmean S hS
  have hreg' : ∀ᵐ b ∂W, IsFiniteMeasureOnCompacts (ν ∞ b) ∧ (ν ∞ b).Regular := hreg.1
  refine ⟨hreg.2,?_⟩
  filter_upwards [hreg',ae_restartAt hW hS hpath] with b hr hp
  have hν (v : ℝ≥0∞) : ν v b=if S b=∞ then 0 else restartPush a
      (lt_trans (by norm_num) ha) b (S b).toNNReal (μ v (restartAt S b)) := rfl
  by_cases hb : S b=∞
  · have he (v : ℝ≥0∞) : ν v b=0 := by simp only [hν,hb,ite_true]
    simp only [he,integral_zero_measure]
    exact ⟨fun _ => ⟨inferInstance,inferInstance⟩,True.intro,monotone_const,
      fun _ => ⟨continuous_const,tendsto_const_nhds⟩⟩
  · have hp := hp hb
    change TraceMassFacts κ (driverHomeomorph.symm (restartAt S b)) (fun v => μ v (restartAt S b)) at hp
    have he (v : ℝ≥0∞) : ν v b=restartPush a (lt_trans (by norm_num) ha)
        b (S b).toNNReal (μ v (restartAt S b)) := by simp only [hν,ite_eq_right hb]
    have hmono : Monotone (fun v => ν v b) := by
      intro v w hvw
      change ν v b≤ν w b
      rw [he,he]
      exact restartPush_mono _ _ _ _ (hp.monotone hvw)
    have hdom (v : ℝ≥0∞) : ν v b≤ν ∞ b := hmono le_top
    have hlocal (v : ℝ≥0∞) : IsFiniteMeasureOnCompacts (ν v b) := by
      let := hr.1
      exact ⟨fun A hA => ((hdom v) A).trans_lt hA.measure_lt_top⟩
    refine ⟨fun v => ⟨hlocal v,?_⟩,?_,hmono,?_⟩
    · let := hlocal v
      infer_instance
    · rw [he]
      simp only [μ,recoveredMass_zero a ha s c hc]
      simp only [restartPush,withDensity_zero_left,Measure.map_zero]
    · intro f
      let := hr.1
      let := hp.atomless
      have hfi : Integrable f (restartPush a (lt_trans (by norm_num) ha) b
          (S b).toNNReal (μ ∞ (restartAt S b))) := by rw [←he]; exact f.integrable
      have hγ := continuous_internalTrace hκ _ hp.continuous_trace
      have hfull : ∀ᵐ z ∂μ ∞ (restartAt S b), z.1∈range (internalTrace κ (driverHomeomorph.symm (restartAt S b))) := by
        filter_upwards [hp.firstVisit_finite] with z hz
        exact (firstVisit_lt_top_iff _ _ _).mp hz
      simp_rw [he,hp.restriction]
      exact ⟨continuous_restartPush_visited a ha b _ _ _ hγ f.continuous.measurable hfi,
        tendsto_restartPush_visited_atTop a ha b _ _ _ hγ hfull f.continuous.measurable hfi⟩

end SLEExactGauge.LoewnerRestart
end
end
 

 
section
 

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical ENNReal
namespace SLEExactGauge.MassVersions

lemma random_restrict_test_lintegral {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (W : Measure Ω) (K : Ω→Measure X) (D : Ω→Set X)
    (hD : ∀ω,MeasurableSet (D ω)) {B : Set Ω} (hB : MeasurableSet B) (f : X→ℝ≥0∞) :
    (∫⁻ω,∫⁻x,(if ω∈B then (D ω).indicator f x else 0)∂K ω∂W)=
      ∫⁻ω in B,∫⁻x,f x∂(K ω).restrict (D ω)∂W := by
  rw [←lintegral_indicator hB]
  apply lintegral_congr
  intro ω
  by_cases hω : ω∈B
  · simp only [ite_eq_left hω,indicator_of_mem hω]
    exact lintegral_indicator (hD ω) f
  · simp only [ite_eq_right hω,indicator_of_notMem hω,lintegral_zero]

lemma conditional_random_restrict_on {Ω X : Type*} [mΩ : MeasurableSpace Ω]
    [MeasurableSpace X] {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    (W : @Measure Ω mΩ) (K L R : Ω→Measure X)
    (hcond : ∀H : Ω×X→ℝ≥0∞, Measurable[m.prod (inferInstance : MeasurableSpace X)] H →
      (∫⁻ω,∫⁻x,H (ω,x)∂K ω∂W)=(∫⁻ω,∫⁻x,H (ω,x)∂L ω∂W)+
        ∫⁻ω,∫⁻x,H (ω,x)∂ R ω∂W)
    (D : Ω→Set X) (hD : MeasurableSet[m.prod (inferInstance : MeasurableSpace X)]
      {p : Ω×X | p.2∈D p.1}) {B : Set Ω} (hB : MeasurableSet[m] B)
    {f : X→ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ω in B,∫⁻x,f x∂(K ω).restrict (D ω)∂W)=
      (∫⁻ω in B,∫⁻x,f x∂(L ω).restrict (D ω)∂W)+
      ∫⁻ω in B,∫⁻x,f x∂(R ω).restrict (D ω)∂W := by
  let F : Ω×X→ℝ≥0∞ := fun p => if p.2∈D p.1 then f p.2 else 0
  have hF : Measurable[m.prod (inferInstance : MeasurableSpace X)] F :=
    Measurable.ite hD (hf.comp measurable_snd) measurable_const
  let H : Ω×X→ℝ≥0∞ := fun p => if p.1∈B then F p else 0
  have hH : Measurable[m.prod (inferInstance : MeasurableSpace X)] H :=
    Measurable.ite (hB.preimage measurable_fst) hF measurable_const
  have hsec (ω : Ω) : MeasurableSet (D ω) := by
    exact hD.preimage (measurable_const.prodMk measurable_id)
  have he (M : Ω→Measure X) : (∫⁻ω,∫⁻x,H (ω,x)∂M ω∂W)=
      ∫⁻ω in B,∫⁻x,f x∂(M ω).restrict (D ω)∂W := by
    change (∫⁻ω,∫⁻x,(if ω∈B then (D ω).indicator f x else 0)∂M ω∂W)=_
    exact @random_restrict_test_lintegral Ω X mΩ _ W M D hsec B (hm B hB) f
  simpa only [he] using hcond H hH

end SLEExactGauge.MassVersions
end
end

end OAI
