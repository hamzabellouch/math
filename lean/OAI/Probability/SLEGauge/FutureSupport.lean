import Mathlib
import OAI.Probability.SLE.MomentGauge
import OAI.Probability.SLEGauge.RadialRestart
import OAI.Probability.SLEGauge.RadonKernels

namespace OAI

/-! Hausdorff gauges, Loewner evolution and trace measures. -/

section
open MeasureTheory ProbabilityTheory Filter Set Topology CompactlySupported
open scoped NNReal ENNReal

namespace SLEExactGauge.MassVersions

variable {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    [SecondCountableTopology X] [BorelSpace X]

 

theorem random_set_sub_null_of_compact_means (μ ν : Kernel Ω X)
    [∀ ω, IsFiniteMeasureOnCompacts (μ ω)] [∀ ω, IsFiniteMeasureOnCompacts (ν ω)]
    (W : Measure Ω) [IsFiniteMeasureOnCompacts (ν ∘ₘ W)]
    (D : Set (Ω × X)) (hD : MeasurableSet D)
    (hle : ∀ᵐ ω ∂W, μ ω≤ν ω)
    (he : ∀ K : Set X, IsCompact K →
      (∫⁻ω, ν ω ({x | (ω,x)∈D}∩K) ∂W) = ∫⁻ω, μ ω ({x | (ω,x)∈D}∩K) ∂W) :
    ∀ᵐ ω ∂W, (ν ω-μ ω) {x | (ω,x)∈D}=0 := by
  have := isSFiniteKernel_of_locally_finite μ
  have := isSFiniteKernel_of_locally_finite ν
  let K := CompactExhaustion.choice X
  have hfinite (n : ℕ) : (∫⁻ω, ν ω ({x | (ω,x)∈D}∩K n) ∂W)<∞ :=
    lt_of_le_of_lt (lintegral_mono (fun ω => measure_mono inter_subset_right)) (by
      rw [← Measure.bind_apply (K.isCompact n).measurableSet ν.aemeasurable]
      exact (K.isCompact n).measure_lt_top)
  have heq (n : ℕ) : (fun ω => μ ω ({x | (ω,x)∈D}∩K n)) =ᵐ[W]
      (fun ω => ν ω ({x | (ω,x)∈D}∩K n)) := by
    apply ae_eq_of_ae_le_of_lintegral_le
    · filter_upwards [hle] with ω hω
      exact hω _
    · rw [← he (K n) (K.isCompact n)]
      exact (hfinite n).ne
    · exact (Kernel.measurable_kernel_prodMk_left
        (hD.inter (measurable_snd (K.isCompact n).measurableSet))).aemeasurable
    · exact (he (K n) (K.isCompact n)).le
  filter_upwards [hle,ae_all_iff.mpr heq] with ω hω heω
  have hsec : MeasurableSet {x | (ω,x)∈D} := measurable_prodMk_left hD
  have hnull (n : ℕ) : (ν ω-μ ω) ({x | (ω,x)∈D}∩K n)=0 := by
    have : IsFiniteMeasure ((μ ω).restrict (K n)) :=
      ⟨by simpa only [Measure.restrict_apply_univ] using (K.isCompact n).measure_lt_top (μ := μ ω)⟩
    rw [← Measure.restrict_apply hsec,
      Measure.restrict_sub_eq_restrict_sub_restrict (K.isCompact n).measurableSet,
      Measure.sub_apply hsec (Measure.restrict_mono Subset.rfl hω),
      Measure.restrict_apply hsec,Measure.restrict_apply hsec,heω n,tsub_self]
  have heU : (⋃ n, {x | (ω,x)∈D}∩K n)={x | (ω,x)∈D} := by
    rw [← inter_iUnion,K.iUnion_eq,inter_univ]
  rw [← heU]
  exact measure_iUnion_null hnull

end SLEExactGauge.MassVersions

namespace ExactSLEGreen
open ExactSLEGenerator ExactSLEMain SLEExactGauge.MassVersions

lemma survivingGreen_eq_zero_iff (a : ℝ) (t : ℝ≥0)
    (b : ExactSLEGenerator.Driver) (z : ℂ) :
    survivingGreen a t b z=0 ↔ ¬alive a b.1 t z := by
  unfold survivingGreen
  split_ifs with h <;> simp [h,physicalGreen,Real.exp_ne_zero]

 

lemma deadSet_raw_measurable (a : ℝ) (ha : 1/4<a) (t : ℝ≥0) :
    MeasurableSet[(rawFiltration t).prod (inferInstance : MeasurableSpace UpperPlane)]
      {p : ExactSLEGenerator.Driver × UpperPlane | ¬alive a p.1.1 t p.2.1} := by
  have h := (actual_surviving_green a ha t).1 (measurableSet_singleton (0 : ℝ))
  change MeasurableSet[(rawFiltration t).prod (inferInstance : MeasurableSpace UpperPlane)]
    {p : ExactSLEGenerator.Driver × UpperPlane | survivingGreen a t p.1 p.2.1=0} at h
  simpa only [survivingGreen_eq_zero_iff] using h

 

theorem conditional_future_support (a : ℝ) (ha : 1/4<a)
    (W : Measure ExactSLEGenerator.Driver) [IsProbabilityMeasure W]
    (hW : IsBrownianReal (fun t (b : ExactSLEGenerator.Driver) => b.1 t) W)
    (t : ℝ≥0) (μ ν : Kernel ExactSLEGenerator.Driver UpperPlane)
    [∀ b, IsFiniteMeasureOnCompacts (μ b)] [∀ b, IsFiniteMeasureOnCompacts (ν b)]
    (hμ : ∀ f : C_c(UpperPlane,ℝ), Integrable (fun b => ∫z, f z ∂μ b) W)
    (hν : ∀ f : C_c(UpperPlane,ℝ), Integrable (fun b => ∫z, f z ∂ν b) W)
    (hle : ∀ᵐ b ∂W, μ b≤ν b)
    (he : ∀ f : C_c(UpperPlane,ℝ), ∀ U : Set ExactSLEGenerator.Driver,
      MeasurableSet[rawFiltration t] U →
      (∫b in U, (∫z,f z∂ν b)-(∫z,f z∂μ b) ∂W) =
        ∫b in U, (∫z,f z*survivingGreen a t b z.1 ∂upperArea) ∂W) :
    ∀ᵐ b ∂W, (ν b-μ b) {z : UpperPlane | ¬alive a b.1 t z.1}=0 := by
  let D : Set (ExactSLEGenerator.Driver × UpperPlane) :=
    {p | ¬alive a p.1.1 t p.2.1}
  have hD := deadSet_raw_measurable a ha t
  have hD₀ : MeasurableSet D := prod_sigma_le (rawFiltration.le t) _ _ hD
  have := average_finiteOnCompacts ν W hν
  apply random_set_sub_null_of_compact_means μ ν W D hD₀ hle
  intro K hK
  let E : Set (ExactSLEGenerator.Driver × UpperPlane) := D∩Prod.snd ⁻¹' K
  have hE : MeasurableSet[(rawFiltration t).prod (inferInstance : MeasurableSpace UpperPlane)] E :=
    hD.inter (measurable_snd hK.measurableSet)
  have hE₀ : MeasurableSet E := prod_sigma_le (rawFiltration.le t) _ _ hE
  let H : ExactSLEGenerator.Driver × UpperPlane → ℝ≥0∞ := E.indicator (fun _ => 1)
  have hH : Measurable[(rawFiltration t).prod (inferInstance : MeasurableSpace UpperPlane)] H :=
    measurable_const.indicator hE
  have hid := compact_conditional_to_random_tests a ha W hW t μ ν hμ hν he H hH
  have hev (ρ : Measure UpperPlane) (b : ExactSLEGenerator.Driver) :
      (∫⁻z, H (b,z) ∂ρ)=ρ ({z | (b,z)∈D}∩K) := by
    have hh := lintegral_indicator_const_comp (μ:=ρ)
      ((measurable_const (a:=b)).prodMk measurable_id) hE₀ (1 : ℝ≥0∞)
    have hs : (fun z : UpperPlane => (b,id z)) ⁻¹' E = {z | (b,z)∈D}∩K := by
      ext z
      rfl
    rw [hs, one_mul] at hh
    exact hh
  have hz (b : ExactSLEGenerator.Driver) (z : UpperPlane) :
      H (b,z)*ENNReal.ofReal (survivingGreen a t b z.1)=0 := by
    by_cases h : (b,z)∈E
    · rw [(survivingGreen_eq_zero_iff a t b z.1).mpr h.1,ENNReal.ofReal_zero,mul_zero]
    · simp only [H,indicator_of_notMem h,zero_mul]
  simpa only [hev,hz,lintegral_zero,add_zero] using hid

end ExactSLEGreen
end
 

 
section
open MeasureTheory ProbabilityTheory Filter Set Topology CompactlySupported
open scoped NNReal ENNReal
namespace ExactSLEGreen
open ExactSLEGenerator ExactSLEMain SLEExactGauge.MassVersions

 
lemma radialTime_ne_zero (a : ℝ) (ha : 0<a) (q : ℝ) (hq : 0<q) (hq1 : q<1)
    (b : ExactSLEGenerator.Driver) (z : ℂ) (hz : 0<z.im) :
    radialTime a b.1 z (z.im*q) ≠ 0 := by
  intro he
  have hh := (radialTime_attained a ha z hz (z.im*q) (mul_pos hz hq)
    (mul_le_of_le_one_right hz.le hq1.le) b (by rw [he]; exact ENNReal.zero_ne_top)).2
  rw [he,ENNReal.toNNReal_zero,actualState_zero ha b hz] at hh
  simp only [physicalRadius,Y_apply,J_apply,neg_zero,Real.exp_zero,mul_one] at hh
  nlinarith

lemma actualUpperMass_zero (a : ℝ) (ha : 0<a) (q : ℝ) (hq : 0<q) (hq1 : q<1)
    (b : ExactSLEGenerator.Driver) : actualUpperMass a q 0 b=0 := by
  have hz (z : UpperPlane) : timeMassDensity a q 0 b z.1=0 := by
    simp only [timeMassDensity,le_zero_iff,ite_eq_right (radialTime_ne_zero a ha q hq hq1 b z.1 z.2)]
  ext A hA
  simp [actualUpperMass,hz]

lemma level_step_lt_one (a : ℝ) (ha : 1/4<a) (j : ℕ) :
    Real.exp (-2*a*((j:ℝ)+1))<1 := by
  apply Real.exp_lt_one_iff.mpr
  have ha0 : 0<a := by linarith
  have hj : (0:ℝ)≤j := Nat.cast_nonneg _
  nlinarith

 

theorem recoveredMass_zero (a : ℝ) (ha : 1/4 < a)
    (s : ℕ → Finset ℕ) (c : ℕ → ℕ → ℝ) (hc : ∀ k j, j∈s k → 0≤c k j)
    (b : ExactSLEGenerator.Driver) : recoveredMass a ha s c hc 0 b=0 := by
  apply radonLimit_eq
  intro f
  simp only [actualMassFunctionals_apply, actualUpperMass_zero a (by linarith)
    _ (Real.exp_pos _) (level_step_lt_one a ha _),integral_zero_measure,mul_zero,Finset.sum_const_zero]
  exact tendsto_const_nhds

end ExactSLEGreen
end
 

 
section
open MeasureTheory ProbabilityTheory Filter Set Topology CompactlySupported
open scoped NNReal ENNReal

namespace SLEExactGauge.MassVersions

variable {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] [BorelSpace X]

 

theorem compact_mass_memLp (μ : Kernel Ω X)
    [∀ ω, IsFiniteMeasureOnCompacts (μ ω)] (W : Measure Ω) (p : ℝ≥0∞)
    (hp : ∀ f : C_c(X,ℝ), MemLp (fun ω => ∫x, f x ∂μ ω) p W)
    (K : Set X) (hK : IsCompact K) :
    MemLp (fun ω => (μ ω K).toReal) p W := by
  obtain ⟨g,hg1,-,hgc,hg01⟩ := exists_continuous_one_zero_of_isCompact
    hK isClosed_empty (disjoint_empty K)
  let f : C_c(X,ℝ) := ⟨g,hgc⟩
  apply (hp f).mono'
    ((μ.measurable_coe hK.measurableSet).ennreal_toReal.aestronglyMeasurable)
  apply Eventually.of_forall
  intro ω
  rw [Real.norm_of_nonneg ENNReal.toReal_nonneg]
  have hpos : 0≤∫x,f x∂μ ω := integral_nonneg (fun x => (hg01 x).1)
  exact ENNReal.toReal_le_of_le_ofReal hpos
    (f.integrable.measure_le_integral (Eventually.of_forall (fun x => (hg01 x).1))
      (fun x hx => le_of_eq ((hg1 hx).symm)))

end SLEExactGauge.MassVersions
end
 

 
section
open MeasureTheory ProbabilityTheory Filter Set Topology CompactlySupported
open scoped NNReal ENNReal
namespace ExactSLEGreen
open ExactSLEGenerator ExactSLEMain SLEExactGauge.MassVersions

noncomputable def initialGreen (a : ℝ) (z : UpperPlane) : ℝ :=
  Real.exp (-alpha a*Real.log 2)*physicalGreen a (z.1,0)

lemma initialGreen_pos (a : ℝ) (z : UpperPlane) : 0 < initialGreen a z :=
  mul_pos (Real.exp_pos _) (Real.exp_pos _)

lemma initialGreen_continuous (a : ℝ) : Continuous (initialGreen a) := by
  have hc : Continuous (fun z : UpperPlane => (z.1,(0:ℝ))) :=
    continuous_subtype_val.prodMk continuous_const
  have hg : Continuous (fun z : UpperPlane => physicalGreen a (z.1,0)) := by
    apply continuous_iff_continuousAt.mpr
    intro z
    exact (hasFDerivAt_physicalGreen a (z.1,0) z.2).continuousAt.comp (f := fun z : UpperPlane => (z.1,(0:ℝ))) hc.continuousAt
  exact continuous_const.mul hg

 
noncomputable def initialGreenMeasure (a : ℝ) : Measure UpperPlane :=
  upperArea.withDensity (fun z => ENNReal.ofReal (initialGreen a z))

lemma initialGreenMeasure_compact_integrable (a : ℝ) (f : C_c(UpperPlane,ℝ)) :
    Integrable f (initialGreenMeasure a) := by
  rw [initialGreenMeasure,integrable_withDensity_iff_integrable_smul'
    (initialGreen_continuous a).measurable.ennreal_ofReal
    (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (initialGreen_pos a _).le,smul_eq_mul]
  let g : C_c(UpperPlane,ℝ) := ⟨⟨fun z => initialGreen a z*f z,
    (initialGreen_continuous a).mul f.continuous⟩, f.hasCompactSupport.mul_left⟩
  exact g.integrable

instance initialGreenMeasure_finite (a : ℝ) : IsFiniteMeasureOnCompacts (initialGreenMeasure a) :=
  finiteOnCompacts_of_integrable_tests _ (initialGreenMeasure_compact_integrable a)

lemma initialGreenMeasure_compact_eval (a : ℝ) (f : C_c(UpperPlane,ℝ)) :
    (∫z,f z∂initialGreenMeasure a) = ∫z, f z*initialGreen a z∂upperArea := by
  rw [initialGreenMeasure,integral_withDensity_eq_integral_toReal_smul]
  · simp only [ENNReal.toReal_ofReal (initialGreen_pos a _).le,smul_eq_mul,mul_comm]
  · exact (initialGreen_continuous a).measurable.ennreal_ofReal
  · exact Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)

 

theorem initialGreenMeasure_eq_average (a : ℝ)
    (μ : Kernel ExactSLEGenerator.Driver UpperPlane)
    [∀ b, IsFiniteMeasureOnCompacts (μ b)] (W : Measure ExactSLEGenerator.Driver)
    (hμ : ∀ f : C_c(UpperPlane,ℝ), Integrable (fun b => ∫z,f z∂μ b) W)
    (he : ∀ f : C_c(UpperPlane,ℝ), (∫b, (∫z,f z∂μ b) ∂W)=∫z, f z*initialGreen a z∂upperArea) :
    μ ∘ₘ W=initialGreenMeasure a := by
  have := average_finiteOnCompacts μ W hμ
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  rw [average_compact_eval μ W hμ,initialGreenMeasure_compact_eval,he]

 

theorem terminal_null_of_area_null (a : ℝ)
    (μ : Kernel ExactSLEGenerator.Driver UpperPlane)
    [∀ b, IsFiniteMeasureOnCompacts (μ b)] (W : Measure ExactSLEGenerator.Driver)
    (he : μ ∘ₘ W=initialGreenMeasure a) (A : Set UpperPlane)
    (hA : MeasurableSet A) (hz : upperArea A=0) : ∀ᵐ b ∂W, μ b A=0 := by
  apply (lintegral_eq_zero_iff (μ.measurable_coe hA)).mp
  rw [← Measure.bind_apply hA μ.aemeasurable,he]
  exact withDensity_absolutelyContinuous _ _ hz

end ExactSLEGreen
end
 

 
section
 

open MeasureTheory ProbabilityTheory Filter Set
open scoped Classical NNReal ENNReal Topology

namespace ExactSLEGreen
open ExactSLEGenerator ExactSLEMain

lemma remainingMassDensity_mean_antitone (a : ℝ) (ha : 1/4 < a)
    (W : Measure ExactSLEGenerator.Driver) [IsProbabilityMeasure W]
    (hW : IsBrownianReal (fun t (b : ExactSLEGenerator.Driver) => b.1 t) W)
    (z : UpperPlane) (q : ℝ) (hq : 0 < q) (hq1 : q ≤ 1) :
    Antitone (fun t : ℝ≥0 => ∫ b, remainingMassDensity a q t b z.1 ∂W) := by
  let ρ := z.1.im * q
  have hρ : 0 < ρ := mul_pos z.2 hq
  have hr : ρ ≤ z.1.im := mul_le_of_le_one_right z.2.le hq1
  let K : ℝ≥0 → ExactSLEGenerator.Driver → ℝ := fun t b =>
    if (t : ℝ≥0∞) < radialTime a b.1 z.1 ρ then radialWeight a b.1 z.1 ρ else 0
  have hK (t : ℝ≥0) : Integrable (K t) W := by
    have hm : MeasurableSet {b : ExactSLEGenerator.Driver |
        (t : ℝ≥0∞) < radialTime a b.1 z.1 ρ} := by
      have hle : MeasurableSet {b : ExactSLEGenerator.Driver |
          radialTime a b.1 z.1 ρ ≤ (t : ℝ≥0∞)} := rawFiltration.le t _
        ((radialTime_stopping a (by linarith) z.1 z.2 ρ hρ hr).measurableSet_le t)
      simpa only [compl_ofPred, not_le] using hle.compl
    apply ((radialWeight_mean W hW a ha z.1 z.2 ρ hρ hr).1.indicator hm).congr
    filter_upwards [] with b
    simp only [K, indicator_apply, mem_ofPred_eq]
  have hmean (t : ℝ≥0) : (∫b, remainingMassDensity a q t b z.1 ∂W) =
      Real.exp (-alpha a*Real.log 2) * ∫b, K t b ∂W := by
    have H := (radial_conditional_weight W hW a ha z.1 z.2 ρ hρ hr
      (fun _ => t) (isStoppingTime_const rawFiltration t) univ MeasurableSet.univ).2
    simp only [setIntegral_univ] at H
    simp only [remainingMassDensity,ite_eq_left z.2,integral_const_mul]
    rw [← H]
  intro s t hst
  dsimp only
  rw [hmean,hmean]
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  apply integral_mono (hK t) (hK s)
  intro b
  have hn := (radialWeight_bound a ha z.1 z.2 ρ hρ hr b).1
  have hst' : (s : ℝ≥0∞) ≤ t := ENNReal.coe_le_coe.mpr hst
  dsimp only [K]
  split_ifs with ht hs hs
  · exact le_rfl
  · exact False.elim (hs (hst'.trans_lt ht))
  · exact hn
  · exact le_rfl

lemma survivingGreen_mean_antitone (a : ℝ) (ha : 1/4 < a)
    (W : Measure ExactSLEGenerator.Driver) [IsProbabilityMeasure W]
    (hW : IsBrownianReal (fun t (b : ExactSLEGenerator.Driver) => b.1 t) W)
    (z : UpperPlane) :
    Antitone (fun t : ℝ≥0 => ∫b, survivingGreen a t b z.1 ∂W) := by
  let q : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hq (n : ℕ) : 0 < q n ∧ q n ≤ 1 := by
    constructor
    · exact div_pos zero_lt_one (by positivity)
    · apply div_le_one_of_le₀ (by linarith [Nat.cast_nonneg (α := ℝ) n]) (by positivity)
  have hq0 : Tendsto q atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hlim (t : ℝ≥0) :
      Tendsto (fun n => ∫b, remainingMassDensity a (q n) t b z.1 ∂W) atTop
        (𝓝 (∫b, survivingGreen a t b z.1 ∂W)) := by
    apply tendsto_integral_of_dominated_convergence (fun b => survivingGreen a t b z.1)
    · intro n
      exact (remainingMassDensity_mean_bound a ha W hW (q n) (hq n).1 (hq n).2 t z.1 z.2).1.aestronglyMeasurable
    · exact (actual_surviving_green a ha t).2.2 W hW z.1 z.2 |>.1
    · intro n
      filter_upwards [] with b
      rw [Real.norm_of_nonneg (remainingMassDensity_nonneg a (q n) t b z.1)]
      exact remainingMassDensity_le_surviving a (q n) t b z.1 z.2
    · exact Eventually.of_forall (fun b => remaining_to_surviving a ha t q hq hq0 b z.1 z.2)
  intro s t hst
  exact le_of_tendsto_of_tendsto' (hlim t) (hlim s) (fun n =>
    remainingMassDensity_mean_antitone a ha W hW z (q n) (hq n).1 (hq n).2 hst)

lemma survivingGreen_eq_killed (a : ℝ) (t : ℝ≥0)
    (b : ExactSLEGenerator.Driver) (z : UpperPlane) :
    survivingGreen a t b z.1 = Real.exp (-alpha a * Real.log 2) *
      killedObservable a z (physicalGreen a) t b := by
  unfold survivingGreen killedObservable
  split_ifs <;> simp only [mul_zero]

lemma physicalGreen_measurable (a : ℝ) : Measurable (physicalGreen a) := by
  unfold physicalGreen logGreen Q X Y J
  fun_prop

lemma killedGreen_nonneg (a : ℝ) (z : UpperPlane) (t : ℝ≥0) (b : ExactSLEGenerator.Driver) :
    0 ≤ killedObservable a z (physicalGreen a) t b :=
  killedObservable_nonneg a z (physicalGreen a) (fun _ _ => (Real.exp_pos _).le) t b

lemma killedGreen_integrable (a : ℝ) (ha : 1/4 < a)
    (W : Measure ExactSLEGenerator.Driver) [IsProbabilityMeasure W]
    (hW : IsBrownianReal (fun t (b : ExactSLEGenerator.Driver) => b.1 t) W)
    (z : UpperPlane) (t : ℝ≥0) :
    Integrable (killedObservable a z (physicalGreen a) t) W := by
  have h := (actual_surviving_green a ha t).2.2 W hW z.1 z.2 |>.1
  simpa only [survivingGreen_eq_killed,integrable_const_mul_iff (isUnit_iff_ne_zero.mpr (Real.exp_ne_zero _))] using h

lemma killedGreen_mean_antitone (a : ℝ) (ha : 1/4 < a)
    (W : Measure ExactSLEGenerator.Driver) [IsProbabilityMeasure W]
    (hW : IsBrownianReal (fun t (b : ExactSLEGenerator.Driver) => b.1 t) W)
    (z : UpperPlane) :
    Antitone (fun t : ℝ≥0 => ∫b, killedObservable a z (physicalGreen a) t b ∂W) := by
  intro s t hst
  have h := survivingGreen_mean_antitone a ha W hW z hst
  simpa only [survivingGreen_eq_killed,integral_const_mul,
    mul_le_mul_iff_right₀ (Real.exp_pos _)] using h

lemma killedGreen_lintegral_antitone (a : ℝ) (ha : 1/4 < a)
    (W : Measure ExactSLEGenerator.Driver) [IsProbabilityMeasure W]
    (hW : IsBrownianReal (fun t (b : ExactSLEGenerator.Driver) => b.1 t) W)
    (z : UpperPlane) :
    Antitone (fun t : ℝ≥0 => ∫⁻b, ENNReal.ofReal
      (killedObservable a z (physicalGreen a) t b) ∂W) := by
  intro s t hst
  dsimp only
  rw [← ofReal_integral_eq_lintegral_ofReal (killedGreen_integrable a ha W hW z t)
    (Eventually.of_forall (killedGreen_nonneg a z t)),
    ← ofReal_integral_eq_lintegral_ofReal (killedGreen_integrable a ha W hW z s)
    (Eventually.of_forall (killedGreen_nonneg a z s))]
  exact ENNReal.ofReal_le_ofReal (killedGreen_mean_antitone a ha W hW z hst)

end ExactSLEGreen
end

end OAI
