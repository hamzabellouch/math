import Mathlib
import OAI.Probability.SLE.MomentGauge
import OAI.Probability.SLEGauge.RadialMeasurability

namespace OAI

/-! Hausdorff gauges, Loewner evolution and trace measures. -/

section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
open scoped Topology
open Set
open MeasureTheory Filter
open scoped NNReal Topology
open MeasureTheory Filter Set Metric Function ODE
open MeasureTheory ProbabilityTheory Filter Set
open Filter
open Filter Set
open MeasureTheory Set
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open MeasureTheory
open scoped Classical
open MeasureTheory ProbabilityTheory Filter Set Metric Function
open scoped NNReal ENNReal Topology
open scoped ENNReal
open Filter Topology
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Metric Function
open scoped NNReal ENNReal Topology
open MeasureTheory Filter Topology Set CompactlySupported
open scoped NNReal ENNReal
namespace ExactSLEGreen
open MeasureTheory ProbabilityTheory Filter Set Topology CompactlySupported
open ExactSLEGenerator ExactSLEMain ExactSLEMassExtraction
open scoped NNReal ENNReal
lemma actualUpperMass_finiteOnCompacts (a : ℝ) (ha : 1/4<a) (q : ℝ) (hq : 0<q) (hq1 : q≤1)
    (t : ℝ≥0∞) (b : ExactSLEGenerator.Driver) :
    IsFiniteMeasureOnCompacts (actualUpperMass a q t b) := by
  constructor
  intro K hK
  obtain ⟨c,hc,hcz⟩ := upper_compact_lower K hK
  have hm : Measurable (fun z : UpperPlane => timeMassDensity a q t b z.1) :=
    (timeMassDensity_measurable a ha q hq hq1 t).comp
      (measurable_const.prodMk measurable_subtype_coe)
  rw [actualUpperMass,withDensity_apply _ hK.measurableSet]
  apply lt_of_le_of_lt (setLIntegral_mono' hK.measurableSet
    (fun z hz => timeMassDensity_local_bound a ha q hq hq1 t b c hc z.1 (hcz z hz)))
  rw [lintegral_const]
  apply ENNReal.mul_lt_top ENNReal.ofReal_lt_top
  rw [Measure.restrict_apply_univ]
  rw [upperArea,upper_embedding.comap_apply]
  exact (hK.image continuous_subtype_val).measure_lt_top

noncomputable def upperExtension (f : C_c(UpperPlane, ℝ)) : ℂ → ℝ :=
  Function.extend Subtype.val f 0

lemma upperExtension_apply (f : C_c(UpperPlane, ℝ)) (z : UpperPlane) :
    upperExtension f z.1=f z := Subtype.val_injective.extend_apply _ _ _

lemma upperExtension_measurable (f : C_c(UpperPlane, ℝ)) : Measurable (upperExtension f) :=
  upper_embedding.measurable_extend f.continuous.measurable measurable_const

lemma upperExtension_zero (f : C_c(UpperPlane, ℝ)) (z : ℂ)
    (hz : z∉Subtype.val '' tsupport f) : upperExtension f z=0 := by
  by_cases h : 0<z.im
  · rw [show z = (⟨z,h⟩ : UpperPlane).1 from rfl, upperExtension_apply]
    exact image_eq_zero_of_notMem_tsupport (fun H => hz ⟨⟨z,h⟩,H,rfl⟩)
  · apply Function.extend_apply'
    rintro ⟨w,rfl⟩
    exact h w.2

lemma actualUpperMass_eval (a : ℝ) (ha : 1/4<a) (q : ℝ) (hq : 0<q) (hq1 : q≤1)
    (t : ℝ≥0∞) (b : ExactSLEGenerator.Driver) (f : C_c(UpperPlane, ℝ)) :
    (∫ z, f z ∂actualUpperMass a q t b) =
      actualMassEval a q t (Subtype.val '' tsupport f) (upperExtension f) b := by
  have hm : Measurable (fun z : UpperPlane => timeMassDensity a q t b z.1) :=
    (timeMassDensity_measurable a ha q hq hq1 t).comp (measurable_const.prodMk measurable_subtype_coe)
  rw [actualUpperMass,integral_withDensity_eq_integral_toReal_smul hm
    (Filter.Eventually.of_forall (fun z => timeMassDensity_finite a q t b z.1))]
  simp only [smul_eq_mul]
  simp_rw [← upperExtension_apply f]
  rw [upperArea]
  trans ∫ z in {z : ℂ | 0<z.im}, (timeMassDensity a q t b z).toReal * upperExtension f z
  · exact integral_subtype_comap (μ := (volume : Measure ℂ)) upperPlane_open.measurableSet
      (fun z : ℂ => (timeMassDensity a q t b z).toReal * upperExtension f z)
  · rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz => ?_)]
    unfold actualMassEval
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz => ?_)]
    · apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun z => mul_comm _ _)
    · rw [upperExtension_zero f z hz,zero_mul]
    · rw [upperExtension_zero f z (by rintro ⟨w,hw,rfl⟩; exact hz w.2), mul_zero]

lemma upperExtension_bounded (f : C_c(UpperPlane, ℝ)) :
    ∃ B : ℝ, 0≤B ∧ ∀ z∈Subtype.val '' tsupport f, ‖upperExtension f z‖≤B := by
  obtain ⟨B,hB⟩ := f.hasCompactSupport.exists_bound_of_continuousOn f.continuous.continuousOn
  refine ⟨max B 0, le_max_right _ _, ?_⟩
  rintro z ⟨w,hw,rfl⟩
  rw [upperExtension_apply]
  exact (hB w hw).trans (le_max_left _ _)

noncomputable def positive_mass_combination
    (μ : ℕ → Measure UpperPlane) (hμ : ∀ j, IsFiniteMeasureOnCompacts (μ j))
    (s : Finset ℕ) (c : ℕ → ℝ) (hc : ∀ j∈s,0≤c j) : C_c(UpperPlane, ℝ) →ₚ[ℝ] ℝ := by
  letI := hμ
  exact PositiveLinearMap.mk₀
    (∑ j∈s, c j • (CompactlySupportedContinuousMap.integralPositiveLinearMap (μ j)).toLinearMap)
    (by
      intro f hf
      simp only [LinearMap.sum_apply,LinearMap.smul_apply,
        smul_eq_mul]
      exact Finset.sum_nonneg (fun j hj => mul_nonneg (hc j hj) (integral_nonneg hf)))

lemma positive_mass_combination_apply
    (μ : ℕ → Measure UpperPlane) (hμ : ∀ j, IsFiniteMeasureOnCompacts (μ j))
    (s : Finset ℕ) (c : ℕ → ℝ) (hc : ∀ j∈s,0≤c j) (f : C_c(UpperPlane, ℝ)) :
    positive_mass_combination μ hμ s c hc f = ∑ j∈s, c j * ∫z, f z∂μ j := by
  change (∑ j∈s, c j • (CompactlySupportedContinuousMap.integralPositiveLinearMap (μ j)).toLinearMap) f = _
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  rfl
theorem actual_radon_mass_extraction (a : ℝ) (ha : 1/4<a)
    (W : Measure ExactSLEGenerator.Driver) [IsProbabilityMeasure W]
    (hW : IsBrownianReal (fun t (b : ExactSLEGenerator.Driver) => b.1 t) W)
    (t : ℕ → ℝ≥0∞) :
    ∃ (s : ℕ → Finset ℕ) (coeff : ℕ → ℕ → ℝ),
      (∀ k j, j∈s k → k≤j) ∧ (∀ k j, j∈s k → 0≤coeff k j) ∧
      (∀ k, ∑ j∈s k, coeff k j=1) ∧
      ∀ᵐ b ∂W, ∃ μ : ℕ → Measure UpperPlane,
        (∀ i, IsFiniteMeasureOnCompacts (μ i) ∧ (μ i).Regular) ∧
        ∀ i (f : C_c(UpperPlane, ℝ)),
          Tendsto (fun k => ∑ j∈s k, coeff k j *
            ∫ z, f z ∂actualUpperMass a (Real.exp (-2*a*(j+1))) (t i) b)
            atTop (𝓝 (∫ z, f z ∂μ i))
    := by
  classical
  obtain ⟨tests,htests⟩ := determining_tests_radon_limit UpperPlane
  let F : ℕ → C_c(UpperPlane, ℝ) := fun i => tests (Nat.unpair i).2
  let K : ℕ → Set ℂ := fun i => Subtype.val '' tsupport (F i)
  have hK (i : ℕ) : IsCompact (K i) := (F i).hasCompactSupport.image continuous_subtype_val
  choose c hc hcz using fun i => upper_compact_lower (tsupport (F i)) (F i).hasCompactSupport
  have hcK (i : ℕ) (z : ℂ) (hz : z∈K i) : c i≤2*z.im := by
    obtain ⟨w,hw,rfl⟩ := hz
    exact hcz i w hw
  obtain ⟨X,s,coeff,v,hX,hs,hcoeff,hsum,hconv,hae⟩ := actual_common_mass_extraction a ha W hW
    K (fun i => (hK i).measurableSet) (fun i => (hK i).isBounded) c hc hcK
    (fun i => upperExtension (F i)) (fun i => upperExtension_measurable (F i))
    (fun i => upperExtension_bounded (F i)) (fun i => t (Nat.unpair i).1)
  refine ⟨s,coeff,hs,hcoeff,hsum,?_⟩
  let q := fun j : ℕ => Real.exp (-2*a*(j+1))
  have hq (j : ℕ) : 0<q j := Real.exp_pos _
  have hq1 (j : ℕ) : q j≤1 := by
    apply Real.exp_le_one_iff.mpr
    have ha0 : 0<a := by linarith
    have hj : (0:ℝ)≤j := Nat.cast_nonneg _
    nlinarith
  filter_upwards [hae] with b hb
  let hμ (i j : ℕ) := actualUpperMass_finiteOnCompacts a ha (q j) (hq j) (hq1 j) (t i) b
  let L : ℕ → ℕ → (C_c(UpperPlane, ℝ) →ₚ[ℝ] ℝ) := fun i k =>
    positive_mass_combination (fun j => actualUpperMass a (q j) (t i) b)
      (hμ i) (s k) (coeff k) (hcoeff k)
  have hi (i : ℕ) : ∃ μ : Measure UpperPlane, IsFiniteMeasureOnCompacts μ ∧ μ.Regular ∧
      ∀ f : C_c(UpperPlane, ℝ), Tendsto (fun k => L i k f) atTop (𝓝 (∫z,f z∂μ)) := by
    apply htests (L i)
    intro n
    refine ⟨v (Nat.pair i n) b, ?_⟩
    have h := hb (Nat.pair i n)
    simpa only [L,positive_mass_combination_apply,actualUpperMass_eval a ha _ (hq _) (hq1 _),
      F,K,Nat.unpair_pair] using h
  choose μ hμlim using hi
  refine ⟨μ,fun i => ⟨(hμlim i).1,(hμlim i).2.1⟩,fun i f => ?_⟩
  simpa only [L,positive_mass_combination_apply] using (hμlim i).2.2 f

end ExactSLEGreen

namespace ExactSLEGreen
open MeasureTheory ProbabilityTheory Filter Set Topology CompactlySupported
open ExactSLEGenerator ExactSLEMain ExactSLEMassExtraction
open scoped NNReal ENNReal

lemma radon_le_of_positive_integrals {X : Type*} [TopologicalSpace X] [T2Space X]
    [LocallyCompactSpace X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
    (μ ν : Measure X) [μ.Regular] [ν.Regular]
    (h : ∀ f : C_c(X, ℝ), (∀ x, 0≤f x) → ∫x,f x∂μ ≤ ∫x,f x∂ν) : μ≤ν := by
  let A := CompactlySupportedContinuousMap.integralPositiveLinearMap μ
  let B := CompactlySupportedContinuousMap.integralPositiveLinearMap ν
  let D : C_c(X, ℝ) →ₚ[ℝ] ℝ := PositiveLinearMap.mk₀ (B.toLinearMap-A.toLinearMap)
    (fun f hf => sub_nonneg.mpr (h f hf))
  let δ := RealRMK.rieszMeasure D
  let : TopologicalSpace.PseudoMetrizableSpace X := inferInstance
  let : SigmaCompactSpace X := inferInstance
  let : IsFiniteMeasureOnCompacts δ := inferInstance
  let : IsFiniteMeasureOnCompacts (μ+δ) := ⟨fun K hK => by
    rw [Measure.add_apply]
    exact ENNReal.add_lt_top.mpr ⟨hK.measure_lt_top,hK.measure_lt_top⟩⟩
  have he : μ+δ=ν := by
    apply Measure.ext_of_integral_eq_on_compactlySupported
    intro f
    rw [integral_add_measure f.integrable f.integrable]
    have hd : ∫x,f x∂δ=∫x,f x∂ν-∫x,f x∂μ := by
      exact RealRMK.integral_rieszMeasure D f
    rw [hd]
    ring
  rw [←he]
  exact le_add_of_nonneg_right bot_le

lemma actualUpperMass_mono_time (a q : ℝ) (b : ExactSLEGenerator.Driver) :
    Monotone (fun t => actualUpperMass a q t b) := by
  intro s t hst
  apply withDensity_mono
  filter_upwards [] with z
  unfold timeMassDensity
  split_ifs with hs ht
  · exact le_rfl
  · exact False.elim (ht (hs.trans hst))
  · exact bot_le
  · exact le_rfl

lemma ordered_radon_limits
    (a : ℝ) (ha : 1/4<a) (b : ExactSLEGenerator.Driver) (t : ℕ → ℝ≥0∞)
    (s : ℕ → Finset ℕ) (coeff : ℕ → ℕ → ℝ) (hc : ∀ k j, j∈s k → 0≤coeff k j)
    (μ : ℕ → Measure UpperPlane)
    (hμ : ∀ i, IsFiniteMeasureOnCompacts (μ i) ∧ (μ i).Regular)
    (hlim : ∀ i (f : C_c(UpperPlane, ℝ)),
      Tendsto (fun k => ∑ j∈s k, coeff k j *
          ∫z,f z∂actualUpperMass a (Real.exp (-2*a*(j+1))) (t i) b)
        atTop (𝓝 (∫z,f z∂μ i))) :
    ∀ i j, t i≤t j → μ i≤μ j := by
  intro i j ht
  let := (hμ i).1
  let := (hμ j).1
  let := (hμ i).2
  let := (hμ j).2
  apply radon_le_of_positive_integrals
  intro f hf
  apply le_of_tendsto_of_tendsto' (hlim i f) (hlim j f)
  intro k
  apply Finset.sum_le_sum
  intro n hn
  apply mul_le_mul_of_nonneg_left _ (hc k n hn)
  have hq1 : Real.exp (-2*a*(n+1))≤1 := by
    apply Real.exp_le_one_iff.mpr
    have ha0 : 0<a := by linarith
    have hn0 : (0:ℝ)≤n := Nat.cast_nonneg _
    nlinarith
  let := actualUpperMass_finiteOnCompacts a ha _ (Real.exp_pos _) hq1 (t j) b
  exact integral_mono_measure (actualUpperMass_mono_time a _ b ht)
    (Filter.Eventually.of_forall hf) f.integrable

lemma actualUpperMass_eval_measurable (a : ℝ) (ha : 1/4<a) (q : ℝ)
    (hq : 0<q) (hq1 : q≤1) (t : ℝ≥0∞) (f : C_c(UpperPlane, ℝ)) :
    Measurable (fun b => ∫z,f z∂actualUpperMass a q t b) := by
  simp_rw [actualUpperMass_eval a ha q hq hq1]
  exact actualMassEval_measurable a ha q hq hq1 t _ _ (upperExtension_measurable f)

 

theorem actual_ordered_radon_extraction (a : ℝ) (ha : 1/4<a)
    (W : Measure ExactSLEGenerator.Driver) [IsProbabilityMeasure W]
    (hW : IsBrownianReal (fun t (b : ExactSLEGenerator.Driver) => b.1 t) W)
    (t : ℕ → ℝ≥0∞) :
    ∃ (s : ℕ → Finset ℕ) (coeff : ℕ → ℕ → ℝ)
      (μ : ExactSLEGenerator.Driver → ℕ → Measure UpperPlane),
      (∀ k j, j∈s k → k≤j) ∧ (∀ k j, j∈s k → 0≤coeff k j) ∧
      (∀ k, ∑ j∈s k, coeff k j=1) ∧
      (∀ b i, IsFiniteMeasureOnCompacts (μ b i) ∧ (μ b i).Regular) ∧
      (∀ i (f : C_c(UpperPlane, ℝ)),
        AEStronglyMeasurable (fun b => ∫ z, f z ∂μ b i) W) ∧
      ∀ᵐ b ∂W,
        (∀ i j, t i ≤ t j → μ b i ≤ μ b j) ∧
        (∀ i (f : C_c(UpperPlane, ℝ)),
          Tendsto (fun k => ∑ j∈s k, coeff k j *
            ∫ z, f z ∂actualUpperMass a (Real.exp (-2*a*(j+1))) (t i) b)
            atTop (𝓝 (∫ z, f z ∂μ b i)))
 := by
  classical
  obtain ⟨s,c,hs,hc,hsum,h⟩ := actual_radon_mass_extraction a ha W hW t
  let P (b : ExactSLEGenerator.Driver) (μ : ℕ → Measure UpperPlane) : Prop :=
    (∀ i, IsFiniteMeasureOnCompacts (μ i) ∧ (μ i).Regular) ∧
    ∀ i (f : C_c(UpperPlane, ℝ)),
      Tendsto (fun k => ∑ j∈s k, c k j *
        ∫z,f z∂actualUpperMass a (Real.exp (-2*a*(j+1))) (t i) b)
        atTop (𝓝 (∫z,f z∂μ i))
  let μ : ExactSLEGenerator.Driver → ℕ → Measure UpperPlane := fun b =>
    if H : ∃ ν, P b ν then H.choose else fun _ => 0
  have hμ (b) (i) : IsFiniteMeasureOnCompacts (μ b i) ∧ (μ b i).Regular := by
    dsimp [μ]
    split_ifs with H
    · exact H.choose_spec.1 i
    · exact ⟨inferInstance,inferInstance⟩
  have hae : ∀ᵐ b ∂W, P b (μ b) := by
    filter_upwards [h] with b hb
    dsimp [μ]
    rw [dite_eq_left hb]
    exact hb.choose_spec
  refine ⟨s,c,μ,hs,hc,hsum,hμ,?_,?_⟩
  · intro i f
    apply aestronglyMeasurable_of_tendsto_ae atTop
      (f := fun k b => ∑ j∈s k, c k j *
        ∫z,f z∂actualUpperMass a (Real.exp (-2*a*(j+1))) (t i) b)
    · intro k
      suffices H : AEStronglyMeasurable (∑ j∈s k, fun b => c k j *
          ∫z,f z∂actualUpperMass a (Real.exp (-2*a*(j+1))) (t i) b) W by
        convert H using 1
        funext b
        simp only [Finset.sum_apply]
      apply Finset.aestronglyMeasurable_sum
      intro j hj
      have hq1 : Real.exp (-2*a*(j+1))≤1 := by
        apply Real.exp_le_one_iff.mpr
        have ha0 : 0<a := by linarith
        have hj0 : (0:ℝ)≤j := Nat.cast_nonneg _
        nlinarith
      exact (actualUpperMass_eval_measurable a ha _ (Real.exp_pos _) hq1 (t i) f).aestronglyMeasurable.const_mul _
    · filter_upwards [hae] with b hb
      exact hb.2 i f
  · filter_upwards [hae] with b hb
    exact ⟨ordered_radon_limits a ha b t s c hc (μ b) hb.1 hb.2,hb.2⟩

end ExactSLEGreen

namespace ExactSLEGreen
open MeasureTheory ProbabilityTheory Filter Set Topology CompactlySupported
open ExactSLEGenerator ExactSLEMain ExactSLEMassExtraction
open scoped NNReal ENNReal

lemma actualMassEval_Lp_bound (a : ℝ) (ha : 1/4<a)
    (W : Measure ExactSLEGenerator.Driver) [IsProbabilityMeasure W]
    (hW : IsBrownianReal (fun t (b : ExactSLEGenerator.Driver) => b.1 t) W)
    (m : ℕ) (hm : 1 ≤ m)
    (K : Set ℂ) (hK : MeasurableSet K) (hKb : Bornology.IsBounded K)
    (c : ℝ) (hc : 0<c) (hcK : ∀ z, z∈K → c≤2*z.im)
    (f : ℂ → ℝ) (hf : Measurable f) (hfB : ∃ B : ℝ, 0≤B ∧ ∀ z∈K, ‖f z‖≤B) :
    ∃ C : ℝ≥0∞, C<∞ ∧ ∀ q : ℝ, 0<q → q≤1 → ∀ t : ℝ≥0∞,
      MemLp (actualMassEval a q t K f) (m : ℝ≥0∞) W ∧ eLpNorm (actualMassEval a q t K f) (m : ℝ≥0∞) W ≤ C := by
  obtain ⟨C,hC,hCb⟩ := actual_mass_moment_bound a ha m
  obtain ⟨hAfin,hB⟩ := hCb W hW K hK hKb c hc hcK (fun z => ‖f z‖) hf.norm
    (fun _ _ => norm_nonneg _) hfB
  let A := ∫⁻ x : Fin m → ℂ, (∏ i, ENNReal.ofReal ‖f (x i)‖)*
    ExactSLEKernel.kernel (alpha a) c x ∂Measure.pi (fun _ => volume.restrict K)
  let D := (ENNReal.ofReal C*A)^(1/(m:ℝ))
  have hD : D<∞ := ENNReal.rpow_lt_top_of_nonneg (by positivity) (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hAfin).ne
  refine ⟨D,hD,?_⟩
  intro q hq hq1 t
  have hnorm : eLpNorm (actualMassEval a q t K f) (m : ℝ≥0∞) W≤D := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by exact_mod_cast (Nat.ne_zero_of_lt hm))
      (by simp) (actualMassEval_measurable a ha q hq hq1 t K f hf).aestronglyMeasurable]
    rw [ENNReal.toReal_natCast]
    apply ENNReal.rpow_le_rpow _ (by positivity)
    calc
      _ ≤ ∫⁻ b, (∫⁻ z in K, ENNReal.ofReal ‖f z‖*massDensity a q b z)^m ∂W := by
        apply lintegral_mono
        intro b
        change ‖actualMassEval a q t K f b‖ₑ^(m:ℝ) ≤
          (∫⁻ z in K, ENNReal.ofReal ‖f z‖*massDensity a q b z)^m
        rw [ENNReal.rpow_natCast]
        exact pow_le_pow_left' (actualMassEval_enorm_bound a q t K f b) m
      _ ≤ _ := hB q hq hq1
  exact ⟨hnorm.trans_lt hD,hnorm⟩

lemma convex_eLpNorm_bound {Ω : Type*} [MeasurableSpace Ω] (W : Measure Ω)
    (p C : ℝ≥0∞) (hp : 1≤p) (s : Finset ℕ) (c : ℕ → ℝ)
    (hc : ∀ j∈s, 0≤c j) (hsum : ∑ j∈s,c j=1)
    (F : ℕ → Ω → ℝ) (_hF : ∀ j∈s, AEStronglyMeasurable (F j) W)
    (hbound : ∀ j∈s, eLpNorm (F j) p W≤C) :
    eLpNorm (fun b => ∑ j∈s,c j*F j b) p W≤C := by
  have he : (fun b => ∑ j∈s,c j*F j b) = ∑ j∈s,c j • F j := by
    funext b
    simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  rw [he]
  calc
    _ ≤ ∑ j∈s,eLpNorm (c j • F j) p W :=
      eLpNorm_sum_le hp
    _ = ∑ j∈s,ENNReal.ofReal (c j)*eLpNorm (F j) p W := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [eLpNorm_const_smul,←ofReal_norm,Real.norm_eq_abs,abs_of_nonneg (hc j hj)]
    _ ≤ ∑ j∈s,ENNReal.ofReal (c j)*C := by
      apply Finset.sum_le_sum
      intro j hj
      gcongr
      exact hbound j hj
    _ = C := by
      rw [←Finset.sum_mul,←ENNReal.ofReal_sum_of_nonneg hc,hsum,ENNReal.ofReal_one,one_mul]

lemma actualUpperMass_Lp_bound (a : ℝ) (ha : 1/4<a)
    (W : Measure ExactSLEGenerator.Driver) [IsProbabilityMeasure W]
    (hW : IsBrownianReal (fun t (b : ExactSLEGenerator.Driver) => b.1 t) W)
    (m : ℕ) (hm : 1 ≤ m) (f : C_c(UpperPlane, ℝ)) :
    ∃ C : ℝ≥0∞, C<∞ ∧ ∀ q : ℝ, 0<q → q≤1 → ∀ t : ℝ≥0∞,
      MemLp (fun b => ∫z,f z∂actualUpperMass a q t b) (m : ℝ≥0∞) W ∧
      eLpNorm (fun b => ∫z,f z∂actualUpperMass a q t b) (m : ℝ≥0∞) W ≤ C := by
  let K := Subtype.val '' tsupport f
  have hK : IsCompact K := f.hasCompactSupport.image continuous_subtype_val
  obtain ⟨c,hc,hcz⟩ := upper_compact_lower (tsupport f) f.hasCompactSupport
  have hcK (z : ℂ) (hz : z∈K) : c≤2*z.im := by
    obtain ⟨w,hw,rfl⟩ := hz
    exact hcz w hw
  obtain ⟨C,hC,h⟩ := actualMassEval_Lp_bound a ha W hW m hm K hK.measurableSet hK.isBounded
    c hc hcK (upperExtension f) (upperExtension_measurable f) (upperExtension_bounded f)
  refine ⟨C,hC,fun q hq hq1 t => ?_⟩
  simpa only [actualUpperMass_eval a ha q hq hq1] using h q hq hq1 t

lemma actual_radon_limit_memLp (a : ℝ) (ha : 1/4<a)
    (W : Measure ExactSLEGenerator.Driver) [IsProbabilityMeasure W]
    (hW : IsBrownianReal (fun t (b : ExactSLEGenerator.Driver) => b.1 t) W)
    (t : ℝ≥0∞) (s : ℕ → Finset ℕ) (coeff : ℕ → ℕ → ℝ)
    (hc : ∀ k j, j∈s k → 0≤coeff k j) (hsum : ∀ k, ∑ j∈s k,coeff k j=1)
    (μ : ExactSLEGenerator.Driver → Measure UpperPlane)
    (f : C_c(UpperPlane, ℝ))
    (hlim : ∀ᵐ b ∂W, Tendsto (fun k => ∑ j∈s k,coeff k j *
      ∫z,f z∂actualUpperMass a (Real.exp (-2*a*(j+1))) t b) atTop (𝓝 (∫z,f z∂μ b)))
    (m : ℕ) : MemLp (fun b => ∫z,f z∂μ b) (m : ℝ≥0∞) W := by
  let q (j : ℕ) := Real.exp (-2*a*(j+1))
  have hq (j : ℕ) : 0<q j := Real.exp_pos _
  have hq1 (j : ℕ) : q j≤1 := by
    apply Real.exp_le_one_iff.mpr
    have ha0 : 0<a := by linarith
    have hj0 : (0:ℝ)≤j := Nat.cast_nonneg _
    nlinarith
  let F : ℕ → ExactSLEGenerator.Driver → ℝ := fun k b =>
    ∑ j∈s k,coeff k j * ∫z,f z∂actualUpperMass a (q j) t b
  have hF (k : ℕ) : AEStronglyMeasurable (F k) W := by
    have H := Finset.aestronglyMeasurable_sum (μ := W) (s k) (fun j hj =>
      (actualUpperMass_eval_measurable a ha (q j) (hq j) (hq1 j) t f).aestronglyMeasurable.const_mul (coeff k j))
    convert H using 1
    funext b
    simp only [F,Finset.sum_apply]
  have hmeas : AEStronglyMeasurable (fun b => ∫z,f z∂μ b) W :=
    aestronglyMeasurable_of_tendsto_ae atTop hF hlim
  by_cases hm : m=0
  · simpa [hm] using (memLp_zero_iff_aestronglyMeasurable.mpr hmeas)
  have hmpos : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm
  obtain ⟨C,hC,hCb⟩ := actualUpperMass_Lp_bound a ha W hW m hmpos f
  have hbound (k : ℕ) : eLpNorm (F k) (m : ℝ≥0∞) W≤C :=
    convex_eLpNorm_bound W _ C (by exact_mod_cast hmpos) (s k) (coeff k) (hc k) (hsum k)
      (fun j b => ∫z,f z∂actualUpperMass a (q j) t b)
      (fun j hj => (hCb (q j) (hq j) (hq1 j) t).1.aestronglyMeasurable)
      (fun j hj => (hCb (q j) (hq j) (hq1 j) t).2)
  exact (Lp.eLpNorm_le_of_ae_tendsto (Filter.Eventually.of_forall hbound) hF hmeas hlim).trans_lt hC

 

end ExactSLEGreen
end
end

end OAI
