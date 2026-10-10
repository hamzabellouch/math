import Mathlib
import OAI.Probability.SLE.MomentGauge
import OAI.Probability.SLEGauge.OptionalGreen
import OAI.Probability.SLEGauge.TerminalExhaustion
import OAI.Probability.SLEGauge.TraceRestriction

namespace OAI

/-! Hausdorff gauges, Loewner evolution and trace measures. -/

section
 

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology CompactlySupported
open scoped NNReal ENNReal symmDiff
namespace SLEExactGauge.TraceMassContinuity
open FlowIdentification ExactSLEMain ExactSLEGenerator ExactSLEGreen
open TraceMassIntegration TraceRestriction TraceLevelLocalization MassVersions
open GermPositivity

 

theorem actual_raw_mass_trace (κ : ℝ) (hκ : 0<κ) (hκ8 : κ<8)
    (W : Measure TDriver) (hW : Target.IsWiener W)
    (t : ℕ→ℝ≥0∞) (hD : Dense {u : ℝ≥0 | ∃i,t i=u})
    (idx : ℕ→ℕ) (hidx : ∀n : ℕ,t (idx n)=(n:ℝ≥0))
    (is : ℕ→ℕ) (his : ∀n : ℕ,t (is n)=(smallTime n:ℝ≥0∞))
    (j : ℕ) (hj : t j=∞) :
    ∃ (s : ℕ → Finset ℕ) (c : ℕ → ℕ → ℝ)
      (hc : ∀ k j, j∈s k → 0≤c k j),
      (∀ k j, j∈s k → k≤j) ∧ (∀ k, ∑ j∈s k, c k j=1) ∧
      let μ := recoveredMass (Target.a κ) (a_gt_quarter hκ hκ8) s c hc
      (∀ v b, IsFiniteMeasureOnCompacts (μ v b) ∧ (μ v b).Regular) ∧
      (∀ b, μ 0 b=0) ∧
      (∀ v, Measurable (μ v)) ∧
      IsProgressive rawFiltration (fun v : ℝ≥0 => μ v) ∧
      (∀ i (f : C_c(UpperPlane,ℝ)) (m : ℕ),
        MemLp (fun b => ∫z,f z∂μ (t i) b) (m : ℝ≥0∞) (W.map driverHomeomorph)) ∧
      (∀ i (K : Set UpperPlane), IsCompact K → ∀ m : ℕ,
        MemLp (fun b => (μ (t i) b K).toReal) (m : ℝ≥0∞) (W.map driverHomeomorph)) ∧
      (∀ i (f : C_c(UpperPlane,ℝ)),
        Tendsto (fun k => eLpNorm (fun b =>
          (∑ j∈s k, c k j * ∫z,f z∂actualUpperMass (Target.a κ) (Real.exp (-2*(Target.a κ)*(j+1))) (t i) b)
            - ∫z,f z∂μ (t i) b) 1 (W.map driverHomeomorph)) atTop (𝓝 0)) ∧
      (∀ i, t i=∞ → μ (t i) ∘ₘ (W.map driverHomeomorph)=initialGreenMeasure (Target.a κ)) ∧
      (∀ i j (v : ℝ≥0), t i=v → t j=∞ →
        ∀ H : ExactSLEGenerator.Driver × UpperPlane → ℝ≥0∞,
        Measurable[(rawFiltration v).prod (inferInstance : MeasurableSpace UpperPlane)] H →
        (∫⁻b, ∫⁻z, H (b,z) ∂μ (t j) b ∂(W.map driverHomeomorph)) = (∫⁻b, ∫⁻z, H (b,z) ∂μ (t i) b ∂(W.map driverHomeomorph)) +
          ∫⁻b, ∫⁻z, H (b,z) * ENNReal.ofReal (survivingGreen (Target.a κ) v b z.1) ∂upperArea ∂(W.map driverHomeomorph)) ∧
      ∀ᵐ b ∂W,
        ContinuousOn (Target.trace κ b) (Ici 0) ∧
        NullSingletonClass (μ ∞ (driverHomeomorph b)) ∧
        (∀v : ℝ≥0, μ v (driverHomeomorph b)=
          (μ ∞ (driverHomeomorph b)).restrict
            (visited (fun z : UpperPlane => z.1) (internalTrace κ b) v)) ∧
        (∀v : ℝ≥0∞, ∀f : C_c(UpperPlane,ℝ), Tendsto
          (fun k => ∑j∈s k,c k j*∫z,f z∂actualUpperMass (Target.a κ)
            (Real.exp (-2*(Target.a κ)*(j+1))) v (driverHomeomorph b))
          atTop (𝓝 (∫z,f z∂μ v (driverHomeomorph b)))) ∧
        (∀A : Set UpperPlane, MeasurableSet A → Tendsto
          (fun n : ℕ => μ (n:ℝ≥0) (driverHomeomorph b) A)
          atTop (𝓝 (μ ∞ (driverHomeomorph b) A))) ∧
        (∀K : Set UpperPlane, IsCompact K → Tendsto
          (fun n : ℕ => (μ ∞ (driverHomeomorph b)-μ (n:ℝ≥0) (driverHomeomorph b)) K)
          atTop (𝓝 0)) ∧
        (∀v : ℝ≥0∞, 0<v → 0<μ v (driverHomeomorph b) univ) ∧
        (∀v : ℝ≥0∞, 0<v → ∃K : Set UpperPlane, IsCompact K ∧
          0<μ v (driverHomeomorph b) K ∧ μ v (driverHomeomorph b) K<∞) := by
  have hBW := brownian_map_driver W hW
  have : IsProbabilityMeasure (W.map driverHomeomorph) := hBW.isGaussianProcess.isProbabilityMeasure
  obtain ⟨s,c,hc,hs,hsum,hμ,hzero,hmeas,hprog,hmom,hcompact,hL1,hmean,hH,hconv⟩ :=
    actual_raw_mass_positive (Target.a κ) (a_gt_quarter hκ hκ8)
      (W.map driverHomeomorph) hBW t idx hidx is his j hj
  let μ := recoveredMass (Target.a κ) (a_gt_quarter hκ hκ8) s c hc
  let K := CompactExhaustion.choice UpperPlane
  let q := (4*Target.a κ-1)/2
  have hq : 0<q := by dsimp [q]; linarith [a_gt_quarter hκ hκ8]
  have hqp : q<4*Target.a κ-1 := by dsimp [q]; linarith [a_gt_quarter hκ hκ8]
  have hang := convexAngularMass_liminf_finite (Target.a κ) q (a_gt_quarter hκ hκ8)
    hq hqp (W.map driverHomeomorph) hBW K K.isCompact s c hc hsum
  refine ⟨s,c,hc,hs,hsum,hμ,hzero,hmeas,hprog,hmom,hcompact,hL1,hmean,hH,?_⟩
  filter_upwards [ae_of_ae_map measurable_driverHomeomorph.aemeasurable hconv,
    ae_of_ae_map measurable_driverHomeomorph.aemeasurable hang,
    angularRegular_ae hκ hκ8 hW, LiteralTrace.trace_regular_all_times hκ hκ8 hW]
    with b hb hba hbr hbt
  rcases hb with ⟨horder,hvague,hatom,hpast,hfuture,haccount,he,hx,hk,hpos,hposK⟩
  have hcont : ContinuousOn (Target.trace κ b) (Ici 0) := by
    simpa only [trace_eq_literal] using hbt.2.1
  have hγ := continuous_internalTrace hκ b hcont
  have h0D : (0:ℝ≥0)∈{u : ℝ≥0 | ∃i,t i=u} := ⟨idx 0,by simpa using hidx 0⟩
  let (u : ℝ≥0∞) : IsFiniteMeasureOnCompacts (μ u (driverHomeomorph b)) := (hμ _ _).1
  let (u : ℝ≥0∞) : (μ u (driverHomeomorph b)).Regular := (hμ _ _).2
  let : NullSingletonClass (μ ∞ (driverHomeomorph b)) := by simpa only [hj] using hatom j
  have hrestrict (i : ℕ) (u : ℝ≥0) (hi : t i=u) :
      μ u (driverHomeomorph b)=(μ ∞ (driverHomeomorph b)).restrict
        (visited (fun z : UpperPlane => z.1) (internalTrace κ b) u) := by
    have hle : μ u (driverHomeomorph b)≤μ ∞ (driverHomeomorph b) := by
      simpa only [hi,hj] using horder i j (by rw [hj]; exact le_top)
    apply restriction_of_complementary_support _ _ hle _
      (measurableSet_visited _ measurable_subtype_coe _ hγ u)
    · rw [visited_internalTrace hκ]
      exact actual_limit_past_trace_support κ hκ hκ8 q hq s c hc hs b hbr hcont K hba u
        (μ u (driverHomeomorph b)) (by
          intro f
          simpa only [hi] using hvague i f)
    · rw [visited_internalTrace hκ]
      have hf := hfuture i j (hi ▸ ENNReal.coe_ne_top) hj
      simp only [hi,hj,ENNReal.toNNReal_coe] at hf
      have hp := past_trace_subset_dead hκ b hbt.1 (t := (u:ℝ)/κ) (by positivity)
      have hu : (κ*((u:ℝ)/κ)).toNNReal=u := by
        rw [mul_div_cancel₀ _ hκ.ne',Real.toNNReal_coe]
      rw [hu] at hp
      exact measure_mono_null (fun z hz => hp hz) hf
  have hdc (u : ℝ≥0) (hu : u∈{u : ℝ≥0 | ∃i,t i=u}) (f : C_c(UpperPlane,ℝ)) :
      Tendsto (fun k => ∑j∈s k,c k j*∫z,f z∂actualUpperMass (Target.a κ)
          (Real.exp (-2*(Target.a κ)*(j+1))) u (driverHomeomorph b))
        atTop (𝓝 (∫z in visited (fun z : UpperPlane => z.1) (internalTrace κ b) u,
          f z∂μ ∞ (driverHomeomorph b))) := by
    obtain ⟨i,hi⟩ := hu
    have hv := hvague i f
    change Tendsto _ atTop (𝓝 (∫z,f z∂μ (t i) (driverHomeomorph b))) at hv
    rw [hi,hrestrict i u hi] at hv
    exact hv
  have hall := recoveredMass_all_times κ hκ (a_gt_quarter hκ hκ8) s c hc b hcont
    (μ ∞ (driverHomeomorph b)) _ hD h0D hdc
  have hvall := actualMass_tendsto_all_times κ hκ (a_gt_quarter hκ hκ8) s c hc b hcont
    (μ ∞ (driverHomeomorph b)) _ hD h0D hdc
  change ∀v : ℝ≥0, μ v (driverHomeomorph b)=
    (μ ∞ (driverHomeomorph b)).restrict
      (visited (fun z : UpperPlane => z.1) (internalTrace κ b) v) at hall
  have hmono : Monotone (fun u : ℝ≥0∞ => μ u (driverHomeomorph b)) := by
    intro u v huv
    change μ u (driverHomeomorph b)≤μ v (driverHomeomorph b)
    induction v using ENNReal.recTopCoe with
    | top =>
      induction u using ENNReal.recTopCoe with
      | top => exact le_rfl
      | coe u => rw [hall u]; exact Measure.restrict_le_self
    | coe v =>
      have hu : u≠∞ := ne_top_of_le_ne_top ENNReal.coe_ne_top huv
      rw [←ENNReal.coe_toNNReal hu,hall,hall]
      exact Measure.restrict_mono (visited_mono _ _ (by
        apply ENNReal.coe_le_coe.mp
        simpa only [ENNReal.coe_toNNReal hu] using huv)) le_rfl
  have hp (u : ℝ≥0∞) (hu : 0<u) : 0<μ u (driverHomeomorph b) univ := by
    have hlim : Tendsto (fun n => (smallTime n:ℝ≥0∞)) atTop (𝓝 0) :=
      ENNReal.continuous_coe.tendsto 0 |>.comp tendsto_smallTime
    obtain ⟨n,hn⟩ := (hlim.eventually (gt_mem_nhds hu)).exists
    have hnpos : 0<μ (smallTime n) (driverHomeomorph b) univ := by
      simpa only [his] using hpos (is n) (by rw [his]; exact_mod_cast smallTime_pos n)
    exact hnpos.trans_le (Measure.le_iff'.mp (hmono hn.le) univ)
  refine ⟨hcont,inferInstance,hall,?_,hx,hk,hp,?_⟩
  · intro u
    induction u using ENNReal.recTopCoe with
    | top => intro f; simpa only [hj] using hvague j f
    | coe u =>
      intro f
      change Tendsto _ atTop (𝓝 (∫z,f z∂μ u (driverHomeomorph b)))
      rw [hall u]
      exact hvall u f
  · intro u hu
    obtain ⟨A,-,hA,hpA⟩ := isOpen_univ.exists_lt_isCompact (hp u hu)
    exact ⟨A,hA,hpA,hA.measure_lt_top⟩

end SLEExactGauge.TraceMassContinuity
end
end
 

 
section
 

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology CompactlySupported
open scoped NNReal ENNReal

namespace ExactSLEGreen
open ExactSLEGenerator ExactSLEMain SLEExactGauge.MassVersions

lemma stoppedSurvivingGreen_spatial_measurable (a : ℝ) (ha : 1/4 < a)
    (S : ExactSLEGenerator.Driver → ℝ≥0∞) (hS : IsStoppingTime rawFiltration S)
    (b : ExactSLEGenerator.Driver) :
    Measurable (fun z : UpperPlane => stoppedSurvivingGreen a (S b) b z.1) :=
  (stoppedSurvivingGreen_joint_measurable a ha S hS).comp
    (measurable_const.prodMk measurable_id)

 
def stoppedSurvivingKernel (a : ℝ) (_ha : 1/4 < a)
    (S : ExactSLEGenerator.Driver → ℝ≥0∞) (_hS : IsStoppingTime rawFiltration S) :
    Kernel ExactSLEGenerator.Driver UpperPlane :=
  (Kernel.const ExactSLEGenerator.Driver upperArea).withDensity
    (fun b z => ENNReal.ofReal (stoppedSurvivingGreen a (S b) b z.1))

instance stoppedSurvivingKernel_sfinite (a : ℝ) (ha : 1/4 < a)
    (S : ExactSLEGenerator.Driver → ℝ≥0∞) (hS : IsStoppingTime rawFiltration S) :
    IsSFiniteKernel (stoppedSurvivingKernel a ha S hS) :=
  Kernel.IsSFiniteKernel.withDensity _ (fun _ _ => ENNReal.ofReal_ne_top)

lemma stoppedSurvivingKernel_apply (a : ℝ) (ha : 1/4 < a)
    (S : ExactSLEGenerator.Driver → ℝ≥0∞) (hS : IsStoppingTime rawFiltration S)
    (b : ExactSLEGenerator.Driver) :
    stoppedSurvivingKernel a ha S hS b = upperArea.withDensity
      (fun z => ENNReal.ofReal (stoppedSurvivingGreen a (S b) b z.1)) :=
  Kernel.withDensity_apply _ (stoppedSurvivingGreen_joint_measurable a ha S hS).ennreal_ofReal b

lemma stoppedSurvivingKernel_raw_measurable (a : ℝ) (ha : 1/4 < a)
    (S : ExactSLEGenerator.Driver → ℝ≥0∞) (hS : IsStoppingTime rawFiltration S) :
    Measurable[hS.measurableSpace] (stoppedSurvivingKernel a ha S hS) := by
  let : MeasurableSpace ExactSLEGenerator.Driver := hS.measurableSpace
  apply Measure.measurable_of_measurable_coe
  intro A hA
  simp_rw [stoppedSurvivingKernel_apply, withDensity_apply _ hA]
  exact (stoppedSurvivingGreen_raw_joint a ha S hS).ennreal_ofReal.lintegral_prod_right'

lemma stoppedSurvivingGreen_lintegral_le_initial (a : ℝ) (ha : 1/4 < a)
    (W : Measure ExactSLEGenerator.Driver) [IsProbabilityMeasure W]
    (hW : IsBrownianReal (fun t (b : ExactSLEGenerator.Driver) => b.1 t) W)
    (S : ExactSLEGenerator.Driver → ℝ≥0∞) (hS : IsStoppingTime rawFiltration S)
    (z : UpperPlane) :
    (∫⁻b, ENNReal.ofReal (stoppedSurvivingGreen a (S b) b z.1) ∂W) ≤
      ENNReal.ofReal (initialGreen a z) := by
  obtain ⟨hi,hb⟩ := survivingGreen_optional_bound a ha W hW z S hS
  rw [← ofReal_integral_eq_lintegral_ofReal hi
    (Eventually.of_forall (fun b => stoppedSurvivingGreen_nonneg a (S b) b z.1))]
  exact ENNReal.ofReal_le_ofReal hb

 

theorem stoppedSurvivingKernel_average_le_initial (a : ℝ) (ha : 1/4 < a)
    (W : Measure ExactSLEGenerator.Driver) [IsProbabilityMeasure W]
    (hW : IsBrownianReal (fun t (b : ExactSLEGenerator.Driver) => b.1 t) W)
    (S : ExactSLEGenerator.Driver → ℝ≥0∞) (hS : IsStoppingTime rawFiltration S) :
    stoppedSurvivingKernel a ha S hS ∘ₘ W ≤ initialGreenMeasure a := by
  apply Measure.le_iff.mpr
  intro A hA
  rw [Measure.bind_apply hA (Kernel.aemeasurable _)]
  simp_rw [stoppedSurvivingKernel_apply, withDensity_apply _ hA]
  rw [lintegral_lintegral_swap
    (stoppedSurvivingGreen_joint_measurable a ha S hS).ennreal_ofReal.aemeasurable]
  change (∫⁻z in A, ∫⁻b, ENNReal.ofReal (stoppedSurvivingGreen a (S b) b z.1) ∂W ∂upperArea) ≤
    (initialGreenMeasure a) A
  rw [initialGreenMeasure,withDensity_apply _ hA]
  exact lintegral_mono (stoppedSurvivingGreen_lintegral_le_initial a ha W hW S hS)

lemma stoppedSurvivingKernel_average_finiteOnCompacts (a : ℝ) (ha : 1/4 < a)
    (W : Measure ExactSLEGenerator.Driver) [IsProbabilityMeasure W]
    (hW : IsBrownianReal (fun t (b : ExactSLEGenerator.Driver) => b.1 t) W)
    (S : ExactSLEGenerator.Driver → ℝ≥0∞) (hS : IsStoppingTime rawFiltration S) :
    IsFiniteMeasureOnCompacts (stoppedSurvivingKernel a ha S hS ∘ₘ W) := by
  constructor
  intro K hK
  exact ((stoppedSurvivingKernel_average_le_initial a ha W hW S hS) K).trans_lt
    hK.measure_lt_top

lemma stoppedSurvivingKernel_compact_eval (a : ℝ) (ha : 1/4 < a)
    (S : ExactSLEGenerator.Driver → ℝ≥0∞) (hS : IsStoppingTime rawFiltration S)
    (b : ExactSLEGenerator.Driver) (f : C_c(UpperPlane,ℝ)) :
    (∫z, f z ∂stoppedSurvivingKernel a ha S hS b) =
      ∫z, f z * stoppedSurvivingGreen a (S b) b z.1 ∂upperArea := by
  rw [stoppedSurvivingKernel_apply, integral_withDensity_eq_integral_toReal_smul]
  · simp only [ENNReal.toReal_ofReal (stoppedSurvivingGreen_nonneg _ _ _ _), smul_eq_mul, mul_comm]
  · exact (stoppedSurvivingGreen_spatial_measurable a ha S hS b).ennreal_ofReal
  · exact Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)

lemma stoppedSurvivingKernel_compact_ae_integrable (a : ℝ) (ha : 1/4 < a)
    (W : Measure ExactSLEGenerator.Driver) [IsProbabilityMeasure W]
    (hW : IsBrownianReal (fun t (b : ExactSLEGenerator.Driver) => b.1 t) W)
    (S : ExactSLEGenerator.Driver → ℝ≥0∞) (hS : IsStoppingTime rawFiltration S)
    (f : C_c(UpperPlane,ℝ)) :
    ∀ᵐ b ∂W, Integrable f (stoppedSurvivingKernel a ha S hS b) := by
  have := stoppedSurvivingKernel_average_finiteOnCompacts a ha W hW S hS
  have hf : Integrable f (stoppedSurvivingKernel a ha S hS ∘ₘ W) := f.integrable
  exact (Measure.integrable_comp_iff f.continuous.measurable.aestronglyMeasurable).mp hf |>.1

lemma stoppedSurvivingKernel_compact_mean_integrable (a : ℝ) (ha : 1/4 < a)
    (W : Measure ExactSLEGenerator.Driver) [IsProbabilityMeasure W]
    (hW : IsBrownianReal (fun t (b : ExactSLEGenerator.Driver) => b.1 t) W)
    (S : ExactSLEGenerator.Driver → ℝ≥0∞) (hS : IsStoppingTime rawFiltration S)
    (f : C_c(UpperPlane,ℝ)) :
    Integrable (fun b => ∫z, f z ∂stoppedSurvivingKernel a ha S hS b) W := by
  have := stoppedSurvivingKernel_average_finiteOnCompacts a ha W hW S hS
  have hf : Integrable f (stoppedSurvivingKernel a ha S hS ∘ₘ W) := f.integrable
  rw [Measure.comp_eq_comp_const_apply] at hf
  exact hf.integral_comp

end ExactSLEGreen
end
end
 

 
section
 

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology CompactlySupported
open scoped Classical NNReal ENNReal

namespace ExactSLEGreen
open ExactSLEGenerator ExactSLEMain SLEExactGauge.MassVersions

 
def unhitMassDensity (a q : ℝ) (t : ℝ≥0∞) (b : ExactSLEGenerator.Driver)
    (z : UpperPlane) : ℝ :=
  Real.exp (-alpha a*Real.log 2) *
    (if t < radialTime a b.1 z.1 (z.1.im*q)
      then radialWeight a b.1 z.1 (z.1.im*q) else 0)

lemma unhitMassDensity_nonneg (a : ℝ) (ha : 1/4<a) (q : ℝ)
    (hq : 0<q) (hq1 : q≤1) (t : ℝ≥0∞) (b : ExactSLEGenerator.Driver) (z : UpperPlane) :
    0 ≤ unhitMassDensity a q t b z := by
  have hn := (radialWeight_bound a ha z.1 z.2 _ (mul_pos z.2 hq)
    (mul_le_of_le_one_right z.2.le hq1) b).1
  unfold unhitMassDensity
  split_ifs <;> positivity

lemma timeMassDensity_add_unhit (a q : ℝ) (t : ℝ≥0∞)
    (b : ExactSLEGenerator.Driver) (z : UpperPlane) :
    timeMassDensity a q ∞ b z.1 = timeMassDensity a q t b z.1 +
      ENNReal.ofReal (unhitMassDensity a q t b z) := by
  have he : 2*z.1.im*q/2=z.1.im*q := by ring
  by_cases hh : radialTime a b.1 z.1 (z.1.im*q)≤t
  · simp only [timeMassDensity, le_top, ite_true, ite_eq_left hh, unhitMassDensity,
      ite_eq_right (not_lt.mpr hh), mul_zero, ENNReal.ofReal_zero, add_zero]
  · simp only [timeMassDensity, le_top, ite_true, ite_eq_right hh, unhitMassDensity,
      ite_eq_left (lt_of_not_ge hh), massDensity, ite_eq_left z.2, fullRadialDensity, he, zero_add]

lemma unhitMassDensity_joint_measurable (a : ℝ) (ha : 1/4<a) (q : ℝ)
    (hq : 0<q) (hq1 : q≤1) (S : ExactSLEGenerator.Driver → ℝ≥0∞)
    (hS : IsStoppingTime rawFiltration S) :
    Measurable (fun p : ExactSLEGenerator.Driver × UpperPlane =>
      unhitMassDensity a q (S p.1) p.1 p.2) := by
  have hmS : Measurable (fun p : ExactSLEGenerator.Driver × UpperPlane => S p.1) :=
    hS.measurable'.comp measurable_fst
  have hmT := joint_radialTime_measurable a ha q hq hq1
  have hmW := joint_radialWeight_measurable a ha q hq hq1
  exact (hmW.ite (measurableSet_lt hmS hmT) measurable_const).const_mul _

lemma unhitMassDensity_integrable (a : ℝ) (ha : 1/4<a)
    (W : Measure ExactSLEGenerator.Driver) [IsProbabilityMeasure W]
    (hW : IsBrownianReal (fun t (b : ExactSLEGenerator.Driver) => b.1 t) W)
    (q : ℝ) (hq : 0<q) (hq1 : q≤1)
    (S : ExactSLEGenerator.Driver → ℝ≥0∞) (hS : IsStoppingTime rawFiltration S)
    (z : UpperPlane) : Integrable (fun b => unhitMassDensity a q (S b) b z) W :=
  (stoppedRadialTerminal_integrable a ha W hW z _ (mul_pos z.2 hq)
    (mul_le_of_le_one_right z.2.le hq1) S hS).const_mul _

lemma unhitMassDensity_conditional (a : ℝ) (ha : 1/4<a)
    (W : Measure ExactSLEGenerator.Driver) [IsProbabilityMeasure W]
    (hW : IsBrownianReal (fun t (b : ExactSLEGenerator.Driver) => b.1 t) W)
    (q : ℝ) (hq : 0<q) (hq1 : q≤1)
    (S : ExactSLEGenerator.Driver → ℝ≥0∞) (hS : IsStoppingTime rawFiltration S)
    (z : UpperPlane) (U : Set ExactSLEGenerator.Driver)
    (hU : MeasurableSet[hS.measurableSpace] U) :
    (∫b in U, unhitMassDensity a q (S b) b z ∂W) =
      ∫b in U, stoppedRemainingDensity a q (S b) b z.1 ∂W := by
  simp only [unhitMassDensity,stoppedRemainingDensity_eq a q _ _ _ z.2,
    integral_const_mul]
  congr 1
  exact (radial_conditional_weight_all W hW a ha z.1 z.2 _
    (mul_pos z.2 hq) (mul_le_of_le_one_right z.2.le hq1) S hS U hU).2

lemma unhitMassDensity_lintegral_conditional (a : ℝ) (ha : 1/4<a)
    (W : Measure ExactSLEGenerator.Driver) [IsProbabilityMeasure W]
    (hW : IsBrownianReal (fun t (b : ExactSLEGenerator.Driver) => b.1 t) W)
    (q : ℝ) (hq : 0<q) (hq1 : q≤1)
    (S : ExactSLEGenerator.Driver → ℝ≥0∞) (hS : IsStoppingTime rawFiltration S)
    (z : UpperPlane) (U : Set ExactSLEGenerator.Driver)
    (hU : MeasurableSet[hS.measurableSpace] U) :
    (∫⁻b in U, ENNReal.ofReal (unhitMassDensity a q (S b) b z) ∂W) =
      ∫⁻b in U, ENNReal.ofReal (stoppedRemainingDensity a q (S b) b z.1) ∂W := by
  rw [← ofReal_integral_eq_lintegral_ofReal
      (unhitMassDensity_integrable a ha W hW q hq hq1 S hS z).restrict
      (Eventually.of_forall (fun b => unhitMassDensity_nonneg a ha q hq hq1 (S b) b z)),
    ← ofReal_integral_eq_lintegral_ofReal
      (stoppedRemainingDensity_mean_bound a ha W hW z q hq hq1 S hS).1.restrict
      (Eventually.of_forall (fun b => stoppedRemainingDensity_nonneg a q (S b) b z.1)),
    unhitMassDensity_conditional a ha W hW q hq hq1 S hS z U hU]

def unhitMassKernel (a q : ℝ) (S : ExactSLEGenerator.Driver → ℝ≥0∞) :
    Kernel ExactSLEGenerator.Driver UpperPlane :=
  (Kernel.const ExactSLEGenerator.Driver upperArea).withDensity
    (fun b z => ENNReal.ofReal (unhitMassDensity a q (S b) b z))

def stoppedRemainingKernel (a q : ℝ) (S : ExactSLEGenerator.Driver → ℝ≥0∞) :
    Kernel ExactSLEGenerator.Driver UpperPlane :=
  (Kernel.const ExactSLEGenerator.Driver upperArea).withDensity
    (fun b z => ENNReal.ofReal (stoppedRemainingDensity a q (S b) b z.1))

instance unhitMassKernel_sfinite (a q : ℝ) (S : ExactSLEGenerator.Driver → ℝ≥0∞) :
    IsSFiniteKernel (unhitMassKernel a q S) :=
  Kernel.IsSFiniteKernel.withDensity _ (fun _ _ => ENNReal.ofReal_ne_top)

instance stoppedRemainingKernel_sfinite (a q : ℝ) (S : ExactSLEGenerator.Driver → ℝ≥0∞) :
    IsSFiniteKernel (stoppedRemainingKernel a q S) :=
  Kernel.IsSFiniteKernel.withDensity _ (fun _ _ => ENNReal.ofReal_ne_top)

lemma unhitMassKernel_apply (a : ℝ) (ha : 1/4<a) (q : ℝ) (hq : 0<q) (hq1 : q≤1)
    (S : ExactSLEGenerator.Driver → ℝ≥0∞) (hS : IsStoppingTime rawFiltration S)
    (b : ExactSLEGenerator.Driver) :
    unhitMassKernel a q S b = upperArea.withDensity
      (fun z => ENNReal.ofReal (unhitMassDensity a q (S b) b z)) :=
  Kernel.withDensity_apply _ (unhitMassDensity_joint_measurable a ha q hq hq1 S hS).ennreal_ofReal b

lemma stoppedRemainingKernel_apply (a : ℝ) (ha : 1/4<a) (q : ℝ) (hq : 0<q) (hq1 : q≤1)
    (S : ExactSLEGenerator.Driver → ℝ≥0∞) (hS : IsStoppingTime rawFiltration S)
    (b : ExactSLEGenerator.Driver) :
    stoppedRemainingKernel a q S b = upperArea.withDensity
      (fun z => ENNReal.ofReal (stoppedRemainingDensity a q (S b) b z.1)) :=
  Kernel.withDensity_apply _ (stoppedRemainingDensity_joint_measurable a ha q hq hq1 S hS).ennreal_ofReal b

lemma stoppedRemainingKernel_raw_measurable (a : ℝ) (ha : 1/4<a)
    (q : ℝ) (hq : 0<q) (hq1 : q≤1)
    (S : ExactSLEGenerator.Driver → ℝ≥0∞) (hS : IsStoppingTime rawFiltration S) :
    Measurable[hS.measurableSpace] (stoppedRemainingKernel a q S) := by
  let : MeasurableSpace ExactSLEGenerator.Driver := hS.measurableSpace
  apply Measure.measurable_of_measurable_coe
  intro A hA
  simp_rw [stoppedRemainingKernel_apply a ha q hq hq1 S hS, withDensity_apply _ hA]
  exact (stoppedRemainingDensity_raw_joint a ha q hq hq1 S hS).ennreal_ofReal.lintegral_prod_right'

 

theorem unhitMassKernel_conditional_average (a : ℝ) (ha : 1/4<a)
    (W : Measure ExactSLEGenerator.Driver) [IsProbabilityMeasure W]
    (hW : IsBrownianReal (fun t (b : ExactSLEGenerator.Driver) => b.1 t) W)
    (q : ℝ) (hq : 0<q) (hq1 : q≤1)
    (S : ExactSLEGenerator.Driver → ℝ≥0∞) (hS : IsStoppingTime rawFiltration S)
    (U : Set ExactSLEGenerator.Driver) (hU : MeasurableSet[hS.measurableSpace] U) :
    unhitMassKernel a q S ∘ₘ W.restrict U =
      stoppedRemainingKernel a q S ∘ₘ W.restrict U := by
  apply Measure.ext
  intro A hA
  rw [Measure.bind_apply hA (Kernel.aemeasurable _),
    Measure.bind_apply hA (Kernel.aemeasurable _)]
  simp_rw [unhitMassKernel_apply a ha q hq hq1 S hS,
    stoppedRemainingKernel_apply a ha q hq hq1 S hS, withDensity_apply _ hA]
  calc
    _ = ∫⁻z in A, ∫⁻b in U, ENNReal.ofReal (unhitMassDensity a q (S b) b z) ∂W ∂upperArea :=
      lintegral_lintegral_swap
        (unhitMassDensity_joint_measurable a ha q hq hq1 S hS).ennreal_ofReal.aemeasurable
    _ = ∫⁻z in A, ∫⁻b in U, ENNReal.ofReal (stoppedRemainingDensity a q (S b) b z.1) ∂W ∂upperArea :=
      lintegral_congr (fun z =>
        unhitMassDensity_lintegral_conditional a ha W hW q hq hq1 S hS z U hU)
    _ = _ := (lintegral_lintegral_swap
        (stoppedRemainingDensity_joint_measurable a ha q hq hq1 S hS).ennreal_ofReal.aemeasurable).symm

lemma stoppedRemainingKernel_le_surviving (a : ℝ) (ha : 1/4<a)
    (q : ℝ) (hq : 0<q) (hq1 : q≤1)
    (S : ExactSLEGenerator.Driver → ℝ≥0∞) (hS : IsStoppingTime rawFiltration S)
    (b : ExactSLEGenerator.Driver) :
    stoppedRemainingKernel a q S b ≤ stoppedSurvivingKernel a ha S hS b := by
  rw [stoppedRemainingKernel_apply a ha q hq hq1 S hS,
    stoppedSurvivingKernel_apply]
  apply withDensity_mono
  exact Eventually.of_forall (fun z => ENNReal.ofReal_le_ofReal
    (stoppedRemainingDensity_le_surviving a q (S b) b z.1 z.2))

lemma stoppedRemainingKernel_average_le_surviving (a : ℝ) (ha : 1/4<a)
    (q : ℝ) (hq : 0<q) (hq1 : q≤1)
    (S : ExactSLEGenerator.Driver → ℝ≥0∞) (hS : IsStoppingTime rawFiltration S)
    (W : Measure ExactSLEGenerator.Driver) :
    stoppedRemainingKernel a q S ∘ₘ W ≤ stoppedSurvivingKernel a ha S hS ∘ₘ W := by
  apply Measure.le_iff.mpr
  intro A hA
  rw [Measure.bind_apply hA (Kernel.aemeasurable _),
    Measure.bind_apply hA (Kernel.aemeasurable _)]
  exact lintegral_mono (fun b => (stoppedRemainingKernel_le_surviving a ha q hq hq1 S hS b) A)

lemma stoppedRemainingKernel_average_finiteOnCompacts (a : ℝ) (ha : 1/4<a)
    (W : Measure ExactSLEGenerator.Driver) [IsProbabilityMeasure W]
    (hW : IsBrownianReal (fun t (b : ExactSLEGenerator.Driver) => b.1 t) W)
    (q : ℝ) (hq : 0<q) (hq1 : q≤1)
    (S : ExactSLEGenerator.Driver → ℝ≥0∞) (hS : IsStoppingTime rawFiltration S) :
    IsFiniteMeasureOnCompacts (stoppedRemainingKernel a q S ∘ₘ W) := by
  constructor
  intro K hK
  exact ((stoppedRemainingKernel_average_le_surviving a ha q hq hq1 S hS W).trans
    (stoppedSurvivingKernel_average_le_initial a ha W hW S hS) K).trans_lt hK.measure_lt_top

lemma unhitMassKernel_average_finiteOnCompacts (a : ℝ) (ha : 1/4<a)
    (W : Measure ExactSLEGenerator.Driver) [IsProbabilityMeasure W]
    (hW : IsBrownianReal (fun t (b : ExactSLEGenerator.Driver) => b.1 t) W)
    (q : ℝ) (hq : 0<q) (hq1 : q≤1)
    (S : ExactSLEGenerator.Driver → ℝ≥0∞) (hS : IsStoppingTime rawFiltration S) :
    IsFiniteMeasureOnCompacts (unhitMassKernel a q S ∘ₘ W) := by
  have he := unhitMassKernel_conditional_average a ha W hW q hq hq1 S hS univ MeasurableSet.univ
  rw [Measure.restrict_univ] at he
  rw [he]
  exact stoppedRemainingKernel_average_finiteOnCompacts a ha W hW q hq hq1 S hS

 

theorem unhitMassKernel_random_test (a : ℝ) (ha : 1/4<a)
    (W : Measure ExactSLEGenerator.Driver) [IsProbabilityMeasure W]
    (hW : IsBrownianReal (fun t (b : ExactSLEGenerator.Driver) => b.1 t) W)
    (q : ℝ) (hq : 0<q) (hq1 : q≤1)
    (S : ExactSLEGenerator.Driver → ℝ≥0∞) (hS : IsStoppingTime rawFiltration S)
    (H : ExactSLEGenerator.Driver × UpperPlane → ℝ≥0∞)
    (hH : Measurable[hS.measurableSpace.prod (inferInstance : MeasurableSpace UpperPlane)] H) :
    (∫⁻b, ∫⁻z, H (b,z) ∂unhitMassKernel a q S b ∂W) =
      ∫⁻b, ∫⁻z, H (b,z) ∂stoppedRemainingKernel a q S b ∂W := by
  have := unhitMassKernel_average_finiteOnCompacts a ha W hW q hq hq1 S hS
  have := stoppedRemainingKernel_average_finiteOnCompacts a ha W hW q hq hq1 S hS
  apply conditional_lintegral_eq_of_average_finite _ _ W _ hS.measurableSpace_le
  · intro U hU f
    have := average_restrict_finite (unhitMassKernel a q S) W U
    have := average_restrict_finite (stoppedRemainingKernel a q S) W U
    rw [← average_compact_eval_of_average_finite,
      ← average_compact_eval_of_average_finite,
      unhitMassKernel_conditional_average a ha W hW q hq hq1 S hS U hU]
  · exact hH

end ExactSLEGreen
end
end

end OAI
