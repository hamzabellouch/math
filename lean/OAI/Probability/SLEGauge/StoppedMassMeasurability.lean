import Mathlib
import OAI.Probability.SLE.MomentGauge
import OAI.Probability.SLEGauge.StoppedFiniteMass

namespace OAI

/-! Hausdorff gauges, Loewner evolution and trace measures. -/

section
 

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology CompactlySupported
open scoped Classical NNReal ENNReal

namespace ExactSLEGenerator

 
def stoppedPastDriver (S : Driver → ℝ≥0∞) (b : Driver) : Driver :=
  if S b = ∞ then b else pastDriver (S b).toNNReal b

lemma stoppedPastDriver_apply (S : Driver → ℝ≥0∞) (b : Driver) (t : ℝ≥0) :
    (stoppedPastDriver S b).1 t = b.1 (ExactSLEGreen.capTime S t b) := by
  by_cases hb : S b = ∞
  · simp [stoppedPastDriver,hb,ExactSLEGreen.capTime]
  · rw [stoppedPastDriver,ite_eq_right hb]
    change b.1 (min t (S b).toNNReal) = b.1 (ExactSLEGreen.capTime S t b)
    congr 1
    unfold ExactSLEGreen.capTime
    conv_rhs => rw [← ENNReal.coe_toNNReal hb]
    simp only [← ENNReal.coe_min,ENNReal.toNNReal_coe,min_comm]

lemma stoppedPastDriver_measurable (S : Driver → ℝ≥0∞)
    (hS : IsStoppingTime rawFiltration S) :
    Measurable[hS.measurableSpace] (stoppedPastDriver S) := by
  have : PolishSpace Driver := (isClosed_eq (continuous_eval_const 0) continuous_const).polishSpace
  obtain ⟨u,hu⟩ := TopologicalSpace.exists_dense_seq (α := ℝ≥0)
  let e : Driver → (ℕ → ℝ) := fun b n => b.1 (u n)
  have hec : Continuous e := continuous_pi fun n =>
    (continuous_eval_const (u n)).comp continuous_subtype_val
  have hei : Function.Injective e := by
    intro b c h
    apply Subtype.ext
    apply DFunLike.coe_injective
    exact hu.equalizer b.1.continuous c.1.continuous h
  apply hec.measurableEmbedding hei |>.measurable_comp_iff.mp
  have hA : StronglyAdapted rawFiltration (fun t (b : Driver) => b.1 t) :=
    Filtration.stronglyAdapted_natural driver_eval_measurable
  have hP := hA.isStronglyProgressive_of_continuous (fun b => b.1.continuous)
  have hval (n : ℕ) : Measurable[hS.measurableSpace]
      (fun b => b.1 (ExactSLEGreen.capTime S (u n) b)) := by
    have h := (measurable_stoppedValue hP (ExactSLEGreen.capTime_stopping S hS (u n))).mono
      (ExactSLEGreen.stopped_cap_measurable S hS (u n)) le_rfl
    exact h
  let : MeasurableSpace Driver := hS.measurableSpace
  apply measurable_pi_iff.mpr
  intro n
  simpa only [Function.comp_apply,e,stoppedPastDriver_apply] using hval n

end ExactSLEGenerator

namespace ExactSLEGreen
open ExactSLEGenerator ExactSLEMain SLEExactGauge.MassVersions

lemma timeMassDensity_stoppedPastDriver (a : ℝ) (ha : 0<a)
    (q : ℝ) (hq : 0<q) (hq1 : q≤1)
    (S : ExactSLEGenerator.Driver → ℝ≥0∞) (b : ExactSLEGenerator.Driver) (z : ℂ) :
    timeMassDensity a q (S b) b z =
      timeMassDensity a q (S b) (stoppedPastDriver S b) z := by
  by_cases hb : S b=∞
  · simp [stoppedPastDriver,hb]
  · conv_lhs => rw [← ENNReal.coe_toNNReal hb]
    conv_rhs => rw [← ENNReal.coe_toNNReal hb]
    apply timeMassDensity_driver_congr a ha q hq hq1
    intro t ht
    simpa only [stoppedPastDriver,ite_eq_right hb] using
      (pastDriver_eq (S b).toNNReal b t ht).symm

 
theorem timeMassDensity_stopping_raw_joint (a : ℝ) (ha : 1/4<a)
    (q : ℝ) (hq : 0<q) (hq1 : q≤1)
    (S : ExactSLEGenerator.Driver → ℝ≥0∞) (hS : IsStoppingTime rawFiltration S) :
    letI : MeasurableSpace ExactSLEGenerator.Driver := hS.measurableSpace
    Measurable (fun p : ExactSLEGenerator.Driver × ℂ =>
      timeMassDensity a q (S p.1) p.1 p.2) := by
  have hp : @Measurable (ExactSLEGenerator.Driver × ℂ)
      ((ℝ≥0∞ × ExactSLEGenerator.Driver) × ℂ)
      (hS.measurableSpace.prod inferInstance) inferInstance
      (fun p => ((S p.1,stoppedPastDriver S p.1),p.2)) := by
    exact ((hS.measurable.comp (@measurable_fst _ _ hS.measurableSpace inferInstance)).prodMk
      ((stoppedPastDriver_measurable S hS).comp
        (@measurable_fst _ _ hS.measurableSpace inferInstance))).prodMk
        (@measurable_snd _ _ hS.measurableSpace inferInstance)
  have hm := (timeMassDensity_joint_measurable a ha q hq hq1).comp hp
  let : MeasurableSpace ExactSLEGenerator.Driver := hS.measurableSpace
  have hm' : Measurable (fun p : ExactSLEGenerator.Driver × ℂ =>
      timeMassDensity a q (S p.1) (stoppedPastDriver S p.1) p.2) := hm
  convert hm' using 1
  funext p
  exact timeMassDensity_stoppedPastDriver a (by linarith) q hq hq1 S p.1 p.2

lemma actualUpperMass_stopping_raw_measurable (a : ℝ) (ha : 1/4<a)
    (q : ℝ) (hq : 0<q) (hq1 : q≤1)
    (S : ExactSLEGenerator.Driver → ℝ≥0∞) (hS : IsStoppingTime rawFiltration S) :
    Measurable[hS.measurableSpace] (fun b => actualUpperMass a q (S b) b) := by
  have hM := timeMassDensity_stopping_raw_joint a ha q hq hq1 S hS
  let : MeasurableSpace ExactSLEGenerator.Driver := hS.measurableSpace
  have hm : Measurable (fun p : ExactSLEGenerator.Driver × UpperPlane =>
      timeMassDensity a q (S p.1) p.1 p.2.1) :=
    hM.comp (measurable_fst.prodMk (measurable_subtype_coe.comp measurable_snd))
  apply Measure.measurable_of_measurable_coe
  intro A hA
  simp only [actualUpperMass,withDensity_apply _ hA]
  exact hm.lintegral_prod_right'

lemma actualUpperMass_stopping_eval_raw_measurable (a : ℝ) (ha : 1/4<a)
    (q : ℝ) (hq : 0<q) (hq1 : q≤1)
    (S : ExactSLEGenerator.Driver → ℝ≥0∞) (hS : IsStoppingTime rawFiltration S)
    (f : C_c(UpperPlane,ℝ)) :
    Measurable[hS.measurableSpace] (fun b => ∫z, f z ∂actualUpperMass a q (S b) b) := by
  simp_rw [actualUpperMass_eval a ha q hq hq1]
  have hD := timeMassDensity_stopping_raw_joint a ha q hq hq1 S hS
  let : MeasurableSpace ExactSLEGenerator.Driver := hS.measurableSpace
  have hm : Measurable (fun p : ExactSLEGenerator.Driver × ℂ =>
      upperExtension f p.2*(timeMassDensity a q (S p.1) p.1 p.2).toReal) :=
    ((upperExtension_measurable f).comp measurable_snd).mul hD.ennreal_toReal
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

lemma actualUpperMass_stopping_eval_measurable (a : ℝ) (ha : 1/4<a)
    (q : ℝ) (hq : 0<q) (hq1 : q≤1)
    (S : ExactSLEGenerator.Driver → ℝ≥0∞) (hS : IsStoppingTime rawFiltration S)
    (f : C_c(UpperPlane,ℝ)) :
    Measurable (fun b => ∫z, f z ∂actualUpperMass a q (S b) b) :=
  (actualUpperMass_stopping_eval_raw_measurable a ha q hq hq1 S hS f).mono
    hS.measurableSpace_le le_rfl

 

theorem recoveredMass_stopping_raw_measurable (a : ℝ) (ha : 1/4<a)
    (s : ℕ → Finset ℕ) (c : ℕ → ℕ → ℝ) (hc : ∀ k j, j∈s k → 0≤c k j)
    (S : ExactSLEGenerator.Driver → ℝ≥0∞) (hS : IsStoppingTime rawFiltration S) :
    Measurable[hS.measurableSpace] (fun b => recoveredMass a ha s c hc (S b) b) := by
  apply @measurable_radonLimit _ _ _ _ _ _ _ _ hS.measurableSpace
  intro k f
  simp_rw [actualMassFunctionals_apply]
  apply Finset.measurable_sum
  intro j hj
  exact measurable_const.mul (actualUpperMass_stopping_eval_raw_measurable a ha _ (Real.exp_pos _)
    (level_step_le_one a ha j) S hS f)

lemma recoveredMass_stopping_measurable (a : ℝ) (ha : 1/4<a)
    (s : ℕ → Finset ℕ) (c : ℕ → ℕ → ℝ) (hc : ∀ k j, j∈s k → 0≤c k j)
    (S : ExactSLEGenerator.Driver → ℝ≥0∞) (hS : IsStoppingTime rawFiltration S) :
    Measurable (fun b => recoveredMass a ha s c hc (S b) b) :=
  (recoveredMass_stopping_raw_measurable a ha s c hc S hS).mono hS.measurableSpace_le le_rfl

end ExactSLEGreen
end
end
 

 
section
 

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology CompactlySupported
open scoped Classical NNReal ENNReal
namespace ExactSLEGreen
open ExactSLEGenerator ExactSLEMain ExactSLEMassExtraction SLEExactGauge.MassVersions

lemma actual_stopped_radon_limit_memLp (a : ℝ) (ha : 1/4<a)
    (W : Measure ExactSLEGenerator.Driver) [IsProbabilityMeasure W]
    (hW : IsBrownianReal (fun t (b : ExactSLEGenerator.Driver) => b.1 t) W)
    (S : ExactSLEGenerator.Driver → ℝ≥0∞) (hS : IsStoppingTime rawFiltration S) (s : ℕ → Finset ℕ) (coeff : ℕ → ℕ → ℝ)
    (hc : ∀ k j, j∈s k → 0≤coeff k j) (hsum : ∀ k, ∑ j∈s k,coeff k j=1)
    (μ : ExactSLEGenerator.Driver → Measure UpperPlane)
    (f : C_c(UpperPlane, ℝ))
    (hlim : ∀ᵐ b ∂W, Tendsto (fun k => ∑ j∈s k,coeff k j *
      ∫z,f z∂actualUpperMass a (Real.exp (-2*a*(j+1))) (S b) b) atTop (𝓝 (∫z,f z∂μ b)))
    (m : ℕ) : MemLp (fun b => ∫z,f z∂μ b) (m : ℝ≥0∞) W := by
  let q (j : ℕ) := Real.exp (-2*a*(j+1))
  have hq (j : ℕ) : 0<q j := Real.exp_pos _
  have hq1 (j : ℕ) : q j≤1 := by
    apply Real.exp_le_one_iff.mpr
    have ha0 : 0<a := by linarith
    have hj0 : (0:ℝ)≤j := Nat.cast_nonneg _
    nlinarith
  let F : ℕ → ExactSLEGenerator.Driver → ℝ := fun k b =>
    ∑ j∈s k,coeff k j * ∫z,f z∂actualUpperMass a (q j) (S b) b
  have hF (k : ℕ) : AEStronglyMeasurable (F k) W := by
    have H := Finset.aestronglyMeasurable_sum (μ := W) (s k) (fun j hj =>
      (actualUpperMass_stopping_eval_measurable a ha (q j) (hq j) (hq1 j) S hS f).aestronglyMeasurable.const_mul (coeff k j))
    convert H using 1
    funext b
    simp only [F,Finset.sum_apply]
  have hmeas : AEStronglyMeasurable (fun b => ∫z,f z∂μ b) W :=
    aestronglyMeasurable_of_tendsto_ae atTop hF hlim
  by_cases hm : m=0
  · simpa [hm] using (memLp_zero_iff_aestronglyMeasurable.mpr hmeas)
  have hmpos : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm
  obtain ⟨C,hC,hCb⟩ := actualUpperMass_stopped_Lp_bound a ha W hW m hmpos f
  have hbound (k : ℕ) : eLpNorm (F k) (m : ℝ≥0∞) W≤C :=
    convex_eLpNorm_bound W _ C (by exact_mod_cast hmpos) (s k) (coeff k) (hc k) (hsum k)
      (fun j b => ∫z,f z∂actualUpperMass a (q j) (S b) b)
      (fun j hj => (hCb (q j) (hq j) (hq1 j) S hS).1.aestronglyMeasurable)
      (fun j hj => (hCb (q j) (hq j) (hq1 j) S hS).2)
  exact (Lp.eLpNorm_le_of_ae_tendsto (Filter.Eventually.of_forall hbound) hF hmeas hlim).trans_lt hC

lemma actual_stopped_radon_limit_L1 (a : ℝ) (ha : 1/4<a)
    (W : Measure ExactSLEGenerator.Driver) [IsProbabilityMeasure W]
    (hW : IsBrownianReal (fun t (b : ExactSLEGenerator.Driver) => b.1 t) W)
    (S : ExactSLEGenerator.Driver → ℝ≥0∞) (hS : IsStoppingTime rawFiltration S) (q : ℕ → ℝ) (hq : ∀ j,0<q j) (hq1 : ∀ j,q j≤1)
    (s : ℕ → Finset ℕ) (coeff : ℕ → ℕ → ℝ)
    (hc : ∀ k j,j∈s k→0≤coeff k j) (hsum : ∀ k,∑j∈s k,coeff k j=1)
    (μ : ExactSLEGenerator.Driver → Measure UpperPlane) (f : C_c(UpperPlane,ℝ))
    (hlim : ∀ᵐ b∂W, Tendsto (fun k => ∑j∈s k,coeff k j*
      ∫z,f z∂actualUpperMass a (q j) (S b) b) atTop (𝓝 (∫z,f z∂μ b))) :
    Tendsto (fun k => eLpNorm (fun b => (∑j∈s k,coeff k j*
      ∫z,f z∂actualUpperMass a (q j) (S b) b)-(∫z,f z∂μ b)) 1 W) atTop (𝓝 0) := by
  let F := fun k b => ∑j∈s k,coeff k j*∫z,f z∂actualUpperMass a (q j) (S b) b
  have hF (k : ℕ) : AEStronglyMeasurable (F k) W := by
    have H := Finset.aestronglyMeasurable_sum (μ := W) (s k) (fun j hj =>
      (actualUpperMass_stopping_eval_measurable a ha (q j) (hq j) (hq1 j) S hS f).aestronglyMeasurable.const_mul (coeff k j))
    convert H using 1
    funext b
    simp only [F,Finset.sum_apply]
  obtain ⟨C,hC,hCb⟩ := actualUpperMass_stopped_Lp_bound a ha W hW 2 (by norm_num) f
  have hbound (k : ℕ) : eLpNorm (F k) 2 W≤C :=
    convex_eLpNorm_bound W _ C (by norm_num) (s k) (coeff k) (hc k) (hsum k)
      (fun j b => ∫z,f z∂actualUpperMass a (q j) (S b) b)
      (fun j hj => (hCb (q j) (hq j) (hq1 j) S hS).1.aestronglyMeasurable)
      (fun j hj => (hCb (q j) (hq j) (hq1 j) S hS).2)
  have hg2 : MemLp (fun b => ∫z,f z∂μ b) 2 W :=
    (Lp.eLpNorm_le_of_ae_tendsto (Filter.Eventually.of_forall hbound) hF
      (aestronglyMeasurable_of_tendsto_ae atTop hF hlim) hlim).trans_lt hC
  have hg := hg2.mono_exponent (by norm_num : (1:ℝ≥0∞)≤2)
  exact tendsto_Lp_finite_of_tendsto_ae le_rfl (by simp) hF (by simpa using hg)
    (unifIntegrable_of_L2_bound W F hF C hC hbound) hlim

end ExactSLEGreen
end
end
 

 
section
 

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology CompactlySupported
open scoped Classical NNReal ENNReal
namespace ExactSLEGreen
open ExactSLEGenerator ExactSLEMain ExactSLEMassExtraction SLEExactGauge.MassVersions

lemma actual_stopped_radon_mass_extraction (a : ℝ) (ha : 1/4<a)
    (W : Measure ExactSLEGenerator.Driver) [IsProbabilityMeasure W]
    (hW : IsBrownianReal (fun t (b : ExactSLEGenerator.Driver) => b.1 t) W)
    (S : ℕ → ExactSLEGenerator.Driver → ℝ≥0∞)
    (hS : ∀ i, IsStoppingTime rawFiltration (S i)) :
    ∃ (s : ℕ → Finset ℕ) (c : ℕ → ℕ → ℝ),
      (∀ k j, j∈s k → k≤j) ∧ (∀ k j, j∈s k → 0≤c k j) ∧
      (∀ k, ∑ j∈s k,c k j=1) ∧
      ∀ᵐ b ∂W, ∃ μ : ℕ → Measure UpperPlane,
        (∀ i, IsFiniteMeasureOnCompacts (μ i) ∧ (μ i).Regular) ∧
        ∀ i (f : C_c(UpperPlane,ℝ)),
          Tendsto (fun k => ∑ j∈s k,c k j *
            ∫z,f z∂actualUpperMass a (Real.exp (-2*a*(j+1))) (S i b) b)
            atTop (𝓝 (∫z,f z∂μ i)) := by
  obtain ⟨tests,htests⟩ := determining_tests_radon_limit UpperPlane
  let F : ℕ → C_c(UpperPlane,ℝ) := fun i => tests (Nat.unpair i).2
  choose C hC hBound using fun i => actualUpperMass_stopped_Lp_bound a ha W hW 2 (by norm_num) (F i)
  let q := fun j : ℕ => Real.exp (-2*a*(j+1))
  have hq (j : ℕ) : 0<q j := Real.exp_pos _
  have hq1 (j : ℕ) : q j≤1 := level_step_le_one a ha j
  let A : ℕ → ℕ → ExactSLEGenerator.Driver → ℝ := fun j i b =>
    ∫z,F i z∂actualUpperMass a (q j) (S (Nat.unpair i).1 b) b
  have hLp (j i : ℕ) : MemLp (A j i) 2 W := by
    simpa only [Nat.cast_ofNat] using
      (hBound i (q j) (hq j) (hq1 j) (S (Nat.unpair i).1) (hS _)).1
  let X := fun j i => (hLp j i).toLp (A j i)
  have hX (i : ℕ) : ∃ B : ℝ, ∀ j, ‖X j i‖≤B := by
    refine ⟨(C i).toReal,fun j => ?_⟩
    rw [Lp.norm_toLp]
    exact ENNReal.toReal_mono (hC i).ne
      (hBound i (q j) (hq j) (hq1 j) (S (Nat.unpair i).1) (hS _)).2
  obtain ⟨s,c,v,hs,hc,hsum,-,hae⟩ := common_L2_convex_tails W X hX
  have he : ∀ᵐ b ∂W, ∀ j i, X j i b=A j i b :=
    ae_all_iff.mpr (fun j => ae_all_iff.mpr (fun i => (hLp j i).coeFn_toLp))
  refine ⟨s,c,hs,hc,hsum,?_⟩
  filter_upwards [hae,he] with b hb heq
  let L (i k : ℕ) : C_c(UpperPlane,ℝ) →ₚ[ℝ] ℝ :=
    actualMassFunctionals a ha s c hc (S i b) b k
  have hi (i : ℕ) : ∃ μ : Measure UpperPlane, IsFiniteMeasureOnCompacts μ ∧ μ.Regular ∧
      ∀ f : C_c(UpperPlane,ℝ), Tendsto (fun k => L i k f) atTop (𝓝 (∫z,f z∂μ)) := by
    apply htests (L i)
    intro n
    refine ⟨v (Nat.pair i n) b,?_⟩
    have h := hb (Nat.pair i n)
    simpa only [heq,A,F,L,actualMassFunctionals_apply,Nat.unpair_pair] using h
  choose μ hμ using hi
  refine ⟨μ,fun i => ⟨(hμ i).1,(hμ i).2.1⟩,fun i f => ?_⟩
  simpa only [L,actualMassFunctionals_apply] using (hμ i).2.2 f

 

theorem actual_raw_stopped_extraction (a : ℝ) (ha : 1/4<a)
    (W : Measure ExactSLEGenerator.Driver) [IsProbabilityMeasure W]
    (hW : IsBrownianReal (fun t (b : ExactSLEGenerator.Driver) => b.1 t) W)
    (S : ℕ → ExactSLEGenerator.Driver → ℝ≥0∞)
    (hS : ∀ i, IsStoppingTime rawFiltration (S i)) :
    ∃ (s : ℕ → Finset ℕ) (c : ℕ → ℕ → ℝ)
      (hc : ∀ k j,j∈s k → 0≤c k j),
      (∀ k j,j∈s k → k≤j) ∧ (∀ k,∑ j∈s k,c k j=1) ∧
      let μ := recoveredMass a ha s c hc
      (∀ t b, IsFiniteMeasureOnCompacts (μ t b) ∧ (μ t b).Regular) ∧
      IsProgressive rawFiltration (fun t : ℝ≥0 => μ t) ∧
      (∀ i, Measurable[(hS i).measurableSpace] (fun b => μ (S i b) b)) ∧
      (∀ i (f : C_c(UpperPlane,ℝ)) (m : ℕ),
        MemLp (fun b => ∫z,f z∂μ (S i b) b) (m : ℝ≥0∞) W) ∧
      (∀ i (f : C_c(UpperPlane,ℝ)),
        Tendsto (fun k => eLpNorm (fun b =>
          (∑ j∈s k,c k j * ∫z,f z∂actualUpperMass a (Real.exp (-2*a*(j+1))) (S i b) b)
            - ∫z,f z∂μ (S i b) b) 1 W) atTop (𝓝 0)) ∧
      ∀ᵐ b ∂W,
        (∀ i j,S i b≤S j b → μ (S i b) b≤μ (S j b) b) ∧
        (∀ i (f : C_c(UpperPlane,ℝ)),
          Tendsto (fun k => ∑ j∈s k,c k j *
            ∫z,f z∂actualUpperMass a (Real.exp (-2*a*(j+1))) (S i b) b)
            atTop (𝓝 (∫z,f z∂μ (S i b) b))) := by
  obtain ⟨s,c,hs,hc,hsum,h⟩ := actual_stopped_radon_mass_extraction a ha W hW S hS
  let μ := recoveredMass a ha s c hc
  have hμ (t : ℝ≥0∞) (b : ExactSLEGenerator.Driver) :
      IsFiniteMeasureOnCompacts (μ t b) ∧ (μ t b).Regular :=
    ⟨radonLimit_finite _,radonLimit_regular _⟩
  have hlim : ∀ᵐ b ∂W, ∀ i (f : C_c(UpperPlane,ℝ)),
      Tendsto (fun k => ∑ j∈s k,c k j *
        ∫z,f z∂actualUpperMass a (Real.exp (-2*a*(j+1))) (S i b) b)
        atTop (𝓝 (∫z,f z∂μ (S i b) b)) := by
    filter_upwards [h] with b hb
    obtain ⟨ν,hν,hconv⟩ := hb
    have he (i : ℕ) : μ (S i b) b=ν i := by
      have := (hν i).2
      apply radonLimit_eq
      intro f
      simpa only [actualMassFunctionals_apply] using hconv i f
    intro i f
    rw [he i]
    exact hconv i f
  refine ⟨s,c,hc,hs,hsum,hμ,recoveredMass_progressive a ha s c hc,?_,?_,?_,?_⟩
  · exact fun i => recoveredMass_stopping_raw_measurable a ha s c hc (S i) (hS i)
  · intro i f m
    exact actual_stopped_radon_limit_memLp a ha W hW (S i) (hS i) s c hc hsum
      (fun b => μ (S i b) b) f (hlim.mono (fun b hb => hb i f)) m
  · intro i f
    exact actual_stopped_radon_limit_L1 a ha W hW (S i) (hS i)
      (fun j => Real.exp (-2*a*(j+1))) (fun j => Real.exp_pos _)
      (level_step_le_one a ha) s c hc hsum (fun b => μ (S i b) b) f
      (hlim.mono (fun b hb => hb i f))
  · filter_upwards [hlim] with b hb
    exact ⟨ordered_radon_limits a ha b (fun i => S i b) s c hc (fun i => μ (S i b) b)
      (fun i => hμ (S i b) b) hb,hb⟩

end ExactSLEGreen
end
end
 

 
section
 

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology CompactlySupported
open scoped Classical NNReal ENNReal
namespace ExactSLEGreen
open ExactSLEGenerator ExactSLEMain ExactSLEMassExtraction SLEExactGauge.MassVersions

lemma actual_stopped_limit_compact_conditional (a : ℝ) (ha : 1/4<a)
    (W : Measure ExactSLEGenerator.Driver) [IsProbabilityMeasure W]
    (hW : IsBrownianReal (fun t (b : ExactSLEGenerator.Driver) => b.1 t) W)
    (S : ExactSLEGenerator.Driver → ℝ≥0∞) (hS : IsStoppingTime rawFiltration S)
    (s : ℕ → Finset ℕ) (c : ℕ → ℕ → ℝ)
    (hs : ∀ k j,j∈s k → k≤j) (hc : ∀ k j,j∈s k → 0≤c k j)
    (hsum : ∀ k,∑ j∈s k,c k j=1)
    (μ ν : ExactSLEGenerator.Driver → Measure UpperPlane) (f : C_c(UpperPlane,ℝ))
    (hμ : ∀ᵐ b ∂W, Tendsto (fun k => ∑ j∈s k,c k j *
      ∫z,f z∂actualUpperMass a (Real.exp (-2*a*(j+1))) (S b) b)
      atTop (𝓝 (∫z,f z∂μ b)))
    (hν : ∀ᵐ b ∂W, Tendsto (fun k => ∑ j∈s k,c k j *
      ∫z,f z∂actualUpperMass a (Real.exp (-2*a*(j+1))) ∞ b)
      atTop (𝓝 (∫z,f z∂ν b)))
    (U : Set ExactSLEGenerator.Driver) (hU : MeasurableSet[hS.measurableSpace] U) :
    (∫b in U,(∫z,f z∂ν b)-(∫z,f z∂μ b) ∂W) =
      ∫b in U,(∫z : UpperPlane,f z*stoppedSurvivingGreen a (S b) b z.1 ∂upperArea) ∂W := by
  let q := fun j : ℕ => Real.exp (-2*a*(j+1))
  have hq (j : ℕ) : 0<q j := Real.exp_pos _
  have hq1 (j : ℕ) : q j≤1 := level_step_le_one a ha j
  have hq0 : Tendsto q atTop (𝓝 0) := mass_levels_tendsto_zero a (by linarith)
  have htop : IsStoppingTime rawFiltration (fun _ : ExactSLEGenerator.Driver => ∞) :=
    fun t => by simp
  have hiμ : Integrable (fun b => ∫z,f z∂μ b) W := by
    have := actual_stopped_radon_limit_memLp a ha W hW S hS s c hc hsum μ f hμ 1
    exact this.integrable (by norm_num)
  have hiν : Integrable (fun b => ∫z,f z∂ν b) W := by
    have := actual_stopped_radon_limit_memLp a ha W hW (fun _ => ∞) htop s c hc hsum ν f hν 1
    exact this.integrable (by norm_num)
  let F := fun k b => ∑ j∈s k,c k j * ∫z,f z∂actualUpperMass a (q j) (S b) b
  let E := fun k b => ∑ j∈s k,c k j * ∫z,f z∂actualUpperMass a (q j) ∞ b
  have hiF (k : ℕ) : Integrable (F k) W :=
    integrable_finsetSum (s k) (fun j hj =>
      (actualUpperMass_stopped_eval_integrable a ha W hW (q j) (hq j) (hq1 j) S hS f).const_mul (c k j))
  have hiE (k : ℕ) : Integrable (E k) W :=
    integrable_finsetSum (s k) (fun j hj =>
      (actualUpperMass_stopped_eval_integrable a ha W hW (q j) (hq j) (hq1 j) (fun _ => ∞) htop f).const_mul (c k j))
  have hF := setIntegral_tendsto_of_L1 W F (fun b => ∫z,f z∂μ b) hiF hiμ
    (actual_stopped_radon_limit_L1 a ha W hW S hS q hq hq1 s c hc hsum μ f hμ) U
  have hE := setIntegral_tendsto_of_L1 W E (fun b => ∫z,f z∂ν b) hiE hiν
    (actual_stopped_radon_limit_L1 a ha W hW (fun _ => ∞) htop q hq hq1 s c hc hsum ν f hν) U
  have hpot := actualUpperMass_stopped_convex_potential_limit a ha W hW q
    (fun j => ⟨hq j,hq1 j⟩) hq0 s c hs hc hsum S hS f U hU
  have he (k : ℕ) : (∫b in U, E k b ∂W)-(∫b in U, F k b ∂W) =
      ∫b in U,∑ j∈s k,c k j*((∫z,f z∂actualUpperMass a (q j) ∞ b)-
        (∫z,f z∂actualUpperMass a (q j) (S b) b)) ∂W := by
    rw [←integral_sub (hiE k).restrict (hiF k).restrict]
    congr 1
    funext b
    simp only [E,F,mul_sub,Finset.sum_sub_distrib]
  rw [integral_sub hiν.restrict hiμ.restrict]
  exact tendsto_nhds_unique (hE.sub hF) (by simpa only [he] using hpot)

 

theorem stopped_compact_conditional_to_random_tests (a : ℝ) (ha : 1/4<a)
    (W : Measure ExactSLEGenerator.Driver) [IsProbabilityMeasure W]
    (hW : IsBrownianReal (fun t (b : ExactSLEGenerator.Driver) => b.1 t) W)
    (S : ExactSLEGenerator.Driver → ℝ≥0∞) (hS : IsStoppingTime rawFiltration S)
    (μ ν : Kernel ExactSLEGenerator.Driver UpperPlane)
    [∀ b, IsFiniteMeasureOnCompacts (μ b)] [∀ b, IsFiniteMeasureOnCompacts (ν b)]
    (hμ : ∀ f : C_c(UpperPlane,ℝ), Integrable (fun b => ∫z,f z∂μ b) W)
    (hν : ∀ f : C_c(UpperPlane,ℝ), Integrable (fun b => ∫z,f z∂ν b) W)
    (he : ∀ f : C_c(UpperPlane,ℝ), ∀ U : Set ExactSLEGenerator.Driver,
      MeasurableSet[hS.measurableSpace] U →
      (∫b in U,(∫z,f z∂ν b)-(∫z,f z∂μ b) ∂W) =
        ∫b in U,(∫z : UpperPlane,f z*stoppedSurvivingGreen a (S b) b z.1 ∂upperArea) ∂W)
    (H : ExactSLEGenerator.Driver × UpperPlane → ℝ≥0∞)
    (hH : Measurable[hS.measurableSpace.prod (inferInstance : MeasurableSpace UpperPlane)] H) :
    (∫⁻b,∫⁻z,H (b,z) ∂ν b ∂W) = (∫⁻b,∫⁻z,H (b,z) ∂μ b ∂W) +
      ∫⁻b,∫⁻z,H (b,z)*ENNReal.ofReal (stoppedSurvivingGreen a (S b) b z.1) ∂upperArea ∂W := by
  have := isSFiniteKernel_of_locally_finite μ
  have := isSFiniteKernel_of_locally_finite ν
  have := average_finiteOnCompacts μ W hμ
  have := average_finiteOnCompacts ν W hν
  have := stoppedSurvivingKernel_average_finiteOnCompacts a ha W hW S hS
  have : IsFiniteMeasureOnCompacts ((μ+stoppedSurvivingKernel a ha S hS) ∘ₘ W) := by
    rw [SLEExactGauge.MassVersions.average_add]
    constructor
    intro K hK
    rw [Measure.add_apply]
    exact ENNReal.add_lt_top.mpr ⟨hK.measure_lt_top,hK.measure_lt_top⟩
  have hidentity := conditional_lintegral_eq_of_average_finite ν
    (μ+stoppedSurvivingKernel a ha S hS) W hS.measurableSpace hS.measurableSpace_le ?_ H hH
  · rw [hidentity]
    have hH₀ : Measurable H := hH.mono (prod_sigma_le hS.measurableSpace_le _) le_rfl
    have heval (b : ExactSLEGenerator.Driver) :
        (∫⁻z,H (b,z) ∂(μ+stoppedSurvivingKernel a ha S hS) b) =
          (∫⁻z,H (b,z) ∂μ b)+
            ∫⁻z,H (b,z)*ENNReal.ofReal (stoppedSurvivingGreen a (S b) b z.1) ∂upperArea := by
      have hHb : Measurable (fun z : UpperPlane => H (b,z)) :=
        hH₀.comp ((measurable_const (a:=b)).prodMk measurable_id)
      rw [add_apply,lintegral_add_measure,stoppedSurvivingKernel_apply]
      congr 1
      exact (lintegral_withDensity_eq_lintegral_mul upperArea
        (stoppedSurvivingGreen_spatial_measurable a ha S hS b).ennreal_ofReal hHb).trans
          (lintegral_congr (fun _ => mul_comm _ _))
    simp_rw [heval]
    rw [lintegral_add_left]
    exact hH₀.lintegral_kernel_prod_right'
  · intro U hU f
    have hadd : (fun b => ∫z,f z∂(μ+stoppedSurvivingKernel a ha S hS) b) =ᵐ[W]
        (fun b => (∫z,f z∂μ b)+(∫z,f z∂stoppedSurvivingKernel a ha S hS b)) := by
      filter_upwards [stoppedSurvivingKernel_compact_ae_integrable a ha W hW S hS f] with b hb
      exact integral_add_measure f.integrable hb
    rw [integral_congr_ae (ae_restrict_of_ae hadd),
      integral_add (hμ f).restrict (stoppedSurvivingKernel_compact_mean_integrable a ha W hW S hS f).restrict]
    have hf := he f U hU
    rw [integral_sub (hν f).restrict (hμ f).restrict] at hf
    simp_rw [stoppedSurvivingKernel_compact_eval]
    linarith

end ExactSLEGreen

namespace ExactSLEGreen
open ExactSLEGenerator ExactSLEMain SLEExactGauge.MassVersions

 

theorem stopped_conditional_future_support (a : ℝ) (ha : 1/4<a)
    (W : Measure ExactSLEGenerator.Driver) [IsProbabilityMeasure W]
    (hW : IsBrownianReal (fun t (b : ExactSLEGenerator.Driver) => b.1 t) W)
    (S : ExactSLEGenerator.Driver → ℝ≥0∞) (hS : IsStoppingTime rawFiltration S)
    (μ ν : Kernel ExactSLEGenerator.Driver UpperPlane)
    [∀ b, IsFiniteMeasureOnCompacts (μ b)] [∀ b, IsFiniteMeasureOnCompacts (ν b)]
    (hμ : ∀ f : C_c(UpperPlane,ℝ), Integrable (fun b => ∫z,f z∂μ b) W)
    (hν : ∀ f : C_c(UpperPlane,ℝ), Integrable (fun b => ∫z,f z∂ν b) W)
    (hle : ∀ᵐ b ∂W, μ b≤ν b)
    (he : ∀ f : C_c(UpperPlane,ℝ), ∀ U : Set ExactSLEGenerator.Driver,
      MeasurableSet[hS.measurableSpace] U →
      (∫b in U,(∫z,f z∂ν b)-(∫z,f z∂μ b) ∂W) =
        ∫b in U,(∫z : UpperPlane,f z*stoppedSurvivingGreen a (S b) b z.1 ∂upperArea) ∂W) :
    ∀ᵐ b ∂W, (ν b-μ b) {z : UpperPlane | stoppedSurvivingGreen a (S b) b z.1=0}=0 := by
  let D : Set (ExactSLEGenerator.Driver × UpperPlane) :=
    {p | stoppedSurvivingGreen a (S p.1) p.1 p.2.1=0}
  have hD : MeasurableSet[hS.measurableSpace.prod (inferInstance : MeasurableSpace UpperPlane)] D :=
    (stoppedSurvivingGreen_raw_joint a ha S hS) (measurableSet_singleton (0 : ℝ))
  have hD₀ : MeasurableSet D := prod_sigma_le hS.measurableSpace_le _ _ hD
  have := average_finiteOnCompacts ν W hν
  apply random_set_sub_null_of_compact_means μ ν W D hD₀ hle
  intro K hK
  let E := D∩Prod.snd ⁻¹' K
  have hE : MeasurableSet[hS.measurableSpace.prod (inferInstance : MeasurableSpace UpperPlane)] E :=
    hD.inter (measurable_snd hK.measurableSet)
  have hE₀ : MeasurableSet E := prod_sigma_le hS.measurableSpace_le _ _ hE
  let H : ExactSLEGenerator.Driver × UpperPlane → ℝ≥0∞ := E.indicator (fun _ => 1)
  have hH : Measurable[hS.measurableSpace.prod (inferInstance : MeasurableSpace UpperPlane)] H :=
    measurable_const.indicator hE
  have hid := stopped_compact_conditional_to_random_tests a ha W hW S hS μ ν hμ hν he H hH
  have hev (ρ : Measure UpperPlane) (b : ExactSLEGenerator.Driver) :
      (∫⁻z,H (b,z) ∂ρ)=ρ ({z | (b,z)∈D}∩K) := by
    have hh := lintegral_indicator_const_comp (μ:=ρ)
      ((measurable_const (a:=b)).prodMk measurable_id) hE₀ (1 : ℝ≥0∞)
    have hs : (fun z : UpperPlane => (b,id z)) ⁻¹' E={z | (b,z)∈D}∩K := by
      ext z; rfl
    rw [hs,one_mul] at hh
    exact hh
  have hz (b : ExactSLEGenerator.Driver) (z : UpperPlane) :
      H (b,z)*ENNReal.ofReal (stoppedSurvivingGreen a (S b) b z.1)=0 := by
    by_cases h : (b,z)∈E
    · rw [show stoppedSurvivingGreen a (S b) b z.1=0 from h.1,ENNReal.ofReal_zero,mul_zero]
    · simp only [H,indicator_of_notMem h,zero_mul]
  simpa only [hev,hz,lintegral_zero,add_zero] using hid

end ExactSLEGreen
end
end

end OAI
