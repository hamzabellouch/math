import Mathlib
import OAI.Probability.SLE.MomentGauge
import OAI.Probability.SLEGauge.FutureSupport

namespace OAI

/-! Hausdorff gauges, Loewner evolution and trace measures. -/

section
 

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Classical NNReal ENNReal Topology

namespace ExactSLEGreen
open ExactSLEGenerator ExactSLEMain

 

def stoppedSurvivingGreen (a : ℝ) (t : ℝ≥0∞)
    (b : ExactSLEGenerator.Driver) (z : ℂ) : ℝ :=
  if t = ∞ then 0 else survivingGreen a t.toNNReal b z

 
def stoppedRemainingDensity (a q : ℝ) (t : ℝ≥0∞)
    (b : ExactSLEGenerator.Driver) (z : ℂ) : ℝ :=
  if t = ∞ then 0 else remainingMassDensity a q t.toNNReal b z

lemma stoppedSurvivingGreen_nonneg (a : ℝ) (t : ℝ≥0∞)
    (b : ExactSLEGenerator.Driver) (z : ℂ) :
    0 ≤ stoppedSurvivingGreen a t b z := by
  unfold stoppedSurvivingGreen
  split_ifs
  · exact le_rfl
  · exact survivingGreen_nonneg _ _ _ _

lemma stoppedRemainingDensity_nonneg (a q : ℝ) (t : ℝ≥0∞)
    (b : ExactSLEGenerator.Driver) (z : ℂ) :
    0 ≤ stoppedRemainingDensity a q t b z := by
  unfold stoppedRemainingDensity
  split_ifs
  · exact le_rfl
  · exact remainingMassDensity_nonneg _ _ _ _ _

lemma stoppedRemainingDensity_le_surviving (a q : ℝ) (t : ℝ≥0∞)
    (b : ExactSLEGenerator.Driver) (z : ℂ) (hz : 0 < z.im) :
    stoppedRemainingDensity a q t b z ≤ stoppedSurvivingGreen a t b z := by
  unfold stoppedRemainingDensity stoppedSurvivingGreen
  split_ifs
  · exact le_rfl
  · exact remainingMassDensity_le_surviving a q t.toNNReal b z hz

lemma stopped_remaining_to_surviving (a : ℝ) (ha : 1/4 < a) (t : ℝ≥0∞)
    (q : ℕ → ℝ) (hq : ∀ n, 0 < q n ∧ q n ≤ 1) (hlim : Tendsto q atTop (𝓝 0))
    (b : ExactSLEGenerator.Driver) (z : ℂ) (hz : 0 < z.im) :
    Tendsto (fun n => stoppedRemainingDensity a (q n) t b z) atTop
      (𝓝 (stoppedSurvivingGreen a t b z)) := by
  unfold stoppedRemainingDensity stoppedSurvivingGreen
  by_cases ht : t = ∞
  · simp only [ht,ite_true]
    exact tendsto_const_nhds
  · simp only [ite_eq_right ht]
    exact remaining_to_surviving a ha t.toNNReal q hq hlim b z hz

lemma stoppedRemainingDensity_eq (a q : ℝ) (t : ℝ≥0∞)
    (b : ExactSLEGenerator.Driver) (z : ℂ) (hz : 0 < z.im) :
    stoppedRemainingDensity a q t b z = Real.exp (-alpha a*Real.log 2) *
      stoppedRadialRemaining a b.1 z (z.im*q) t := by
  unfold stoppedRemainingDensity stoppedRadialRemaining remainingMassDensity
  split_ifs <;> simp_all only [mul_zero]

lemma stoppedRadialTerminal_integrable (a : ℝ) (ha : 1/4 < a)
    (W : Measure ExactSLEGenerator.Driver) [IsProbabilityMeasure W]
    (hW : IsBrownianReal (fun t (b : ExactSLEGenerator.Driver) => b.1 t) W)
    (z : UpperPlane) (ρ : ℝ) (hρ : 0 < ρ) (hr : ρ ≤ z.1.im)
    (S : ExactSLEGenerator.Driver → ℝ≥0∞) (hS : IsStoppingTime rawFiltration S) :
    Integrable (fun b => if S b < radialTime a b.1 z.1 ρ
      then radialWeight a b.1 z.1 ρ else 0) W := by
  have hmS : Measurable S := hS.measurable'
  have hmT : Measurable (fun b : ExactSLEGenerator.Driver => radialTime a b.1 z.1 ρ) :=
    (radialTime_stopping a (by linarith) z.1 z.2 ρ hρ hr).measurable'
  have hm : MeasurableSet {b : ExactSLEGenerator.Driver | S b < radialTime a b.1 z.1 ρ} :=
    measurableSet_lt hmS hmT
  apply ((radialWeight_mean W hW a ha z.1 z.2 ρ hρ hr).1.indicator hm).congr
  filter_upwards [] with b
  simp only [indicator_apply,mem_ofPred_eq]

lemma stoppedRemainingDensity_mean_bound (a : ℝ) (ha : 1/4 < a)
    (W : Measure ExactSLEGenerator.Driver) [IsProbabilityMeasure W]
    (hW : IsBrownianReal (fun t (b : ExactSLEGenerator.Driver) => b.1 t) W)
    (z : UpperPlane) (q : ℝ) (hq : 0 < q) (hq1 : q ≤ 1)
    (S : ExactSLEGenerator.Driver → ℝ≥0∞) (hS : IsStoppingTime rawFiltration S) :
    Integrable (fun b => stoppedRemainingDensity a q (S b) b z.1) W ∧
      (∫ b, stoppedRemainingDensity a q (S b) b z.1 ∂W) ≤ initialGreen a z := by
  have hρ : 0 < z.1.im*q := mul_pos z.2 hq
  have hr : z.1.im*q ≤ z.1.im := mul_le_of_le_one_right z.2.le hq1
  obtain ⟨hi,he⟩ := radial_conditional_weight_all W hW a ha z.1 z.2
    (z.1.im*q) hρ hr S hS univ MeasurableSet.univ
  simp only [setIntegral_univ] at he
  simp only [stoppedRemainingDensity_eq a q _ _ _ z.2]
  refine ⟨hi.const_mul _, ?_⟩
  rw [integral_const_mul, ← he]
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  rw [← (radialWeight_mean W hW a ha z.1 z.2 _ hρ hr).2]
  apply integral_mono (stoppedRadialTerminal_integrable a ha W hW z _ hρ hr S hS)
    (radialWeight_mean W hW a ha z.1 z.2 _ hρ hr).1
  intro b
  dsimp only
  split_ifs
  · exact le_rfl
  · exact (radialWeight_bound a ha z.1 z.2 _ hρ hr b).1

 

theorem survivingGreen_optional_bound (a : ℝ) (ha : 1/4 < a)
    (W : Measure ExactSLEGenerator.Driver) [IsProbabilityMeasure W]
    (hW : IsBrownianReal (fun t (b : ExactSLEGenerator.Driver) => b.1 t) W)
    (z : UpperPlane) (S : ExactSLEGenerator.Driver → ℝ≥0∞)
    (hS : IsStoppingTime rawFiltration S) :
    Integrable (fun b => stoppedSurvivingGreen a (S b) b z.1) W ∧
      (∫ b, stoppedSurvivingGreen a (S b) b z.1 ∂W) ≤ initialGreen a z := by
  let q : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hq (n : ℕ) : 0 < q n ∧ q n ≤ 1 := by
    constructor
    · exact div_pos zero_lt_one (by positivity)
    · apply div_le_one_of_le₀ (by linarith [Nat.cast_nonneg (α := ℝ) n]) (by positivity)
  have hlim : Tendsto q atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let F : ℕ → ExactSLEGenerator.Driver → ℝ := fun n b =>
    stoppedRemainingDensity a (q n) (S b) b z.1
  let G : ExactSLEGenerator.Driver → ℝ := fun b => stoppedSurvivingGreen a (S b) b z.1
  have hFi (n : ℕ) := (stoppedRemainingDensity_mean_bound a ha W hW z (q n)
    (hq n).1 (hq n).2 S hS).1
  have hFm (n : ℕ) : AEStronglyMeasurable (F n) W := (hFi n).aestronglyMeasurable
  have hconv : ∀ᵐ b ∂W, Tendsto (fun n => F n b) atTop (𝓝 (G b)) :=
    Eventually.of_forall (fun b => stopped_remaining_to_surviving a ha (S b) q hq hlim b z.1 z.2)
  have hbound (n : ℕ) : eLpNorm (F n) 1 W ≤ ENNReal.ofReal (initialGreen a z) := by
    rw [eLpNorm_one_eq_lintegral_enorm (hFm n), ← ofReal_integral_norm_eq_lintegral_enorm (hFi n)]
    have he : (fun b => ‖F n b‖) = F n := by
      funext b
      exact Real.norm_of_nonneg (stoppedRemainingDensity_nonneg a (q n) (S b) b z.1)
    rw [he]
    exact ENNReal.ofReal_le_ofReal
      (stoppedRemainingDensity_mean_bound a ha W hW z (q n) (hq n).1 (hq n).2 S hS).2
  have hGm := aestronglyMeasurable_of_tendsto_ae atTop hFm hconv
  have hGb := Lp.eLpNorm_le_of_ae_tendsto (Eventually.of_forall hbound) hFm hGm hconv
  have hGi : Integrable G W :=
    memLp_one_iff_integrable.mp (hGb.trans_lt ENNReal.ofReal_lt_top)
  refine ⟨hGi, ?_⟩
  rw [eLpNorm_one_eq_lintegral_enorm hGm, ← ofReal_integral_norm_eq_lintegral_enorm hGi] at hGb
  have he : (fun b => ‖G b‖) = G := by
    funext b
    exact Real.norm_of_nonneg (stoppedSurvivingGreen_nonneg a (S b) b z.1)
  rw [he] at hGb
  exact (ENNReal.ofReal_le_ofReal_iff (initialGreen_pos a z).le).mp hGb

lemma stopped_remaining_integral_tendsto (a : ℝ) (ha : 1/4 < a)
    (W : Measure ExactSLEGenerator.Driver) [IsProbabilityMeasure W]
    (hW : IsBrownianReal (fun t (b : ExactSLEGenerator.Driver) => b.1 t) W)
    (z : UpperPlane) (S : ExactSLEGenerator.Driver → ℝ≥0∞)
    (hS : IsStoppingTime rawFiltration S)
    (q : ℕ → ℝ) (hq : ∀ n, 0 < q n ∧ q n ≤ 1) (hlim : Tendsto q atTop (𝓝 0))
    (U : Set ExactSLEGenerator.Driver) :
    Tendsto (fun n => ∫ b in U, stoppedRemainingDensity a (q n) (S b) b z.1 ∂W)
      atTop (𝓝 (∫ b in U, stoppedSurvivingGreen a (S b) b z.1 ∂W)) := by
  apply tendsto_integral_of_dominated_convergence
    (fun b => stoppedSurvivingGreen a (S b) b z.1)
  · intro n
    exact (stoppedRemainingDensity_mean_bound a ha W hW z (q n)
      (hq n).1 (hq n).2 S hS).1.aestronglyMeasurable.restrict
  · exact (survivingGreen_optional_bound a ha W hW z S hS).1.integrableOn
  · intro n
    filter_upwards [] with b
    rw [Real.norm_of_nonneg (stoppedRemainingDensity_nonneg a (q n) (S b) b z.1)]
    exact stoppedRemainingDensity_le_surviving a (q n) (S b) b z.1 z.2
  · exact Eventually.of_forall (fun b =>
      stopped_remaining_to_surviving a ha (S b) q hq hlim b z.1 z.2)

 

theorem survivingGreen_optional_comparison (a : ℝ) (ha : 1/4 < a)
    (W : Measure ExactSLEGenerator.Driver) [IsProbabilityMeasure W]
    (hW : IsBrownianReal (fun t (b : ExactSLEGenerator.Driver) => b.1 t) W)
    (z : UpperPlane) (S T : ExactSLEGenerator.Driver → ℝ≥0∞)
    (hS : IsStoppingTime rawFiltration S) (hT : IsStoppingTime rawFiltration T)
    (hst : S ≤ T) (U : Set ExactSLEGenerator.Driver)
    (hU : MeasurableSet[hS.measurableSpace] U) :
    (∫ b in U, stoppedSurvivingGreen a (T b) b z.1 ∂W) ≤
      ∫ b in U, stoppedSurvivingGreen a (S b) b z.1 ∂W := by
  have hUT : MeasurableSet[hT.measurableSpace] U := (hS.measurableSpace_mono hT hst) _ hU
  have hc (q : ℝ) (hq : 0 < q) (hq1 : q ≤ 1) :
      (∫ b in U, stoppedRemainingDensity a q (T b) b z.1 ∂W) ≤
        ∫ b in U, stoppedRemainingDensity a q (S b) b z.1 ∂W := by
    have hρ : 0 < z.1.im*q := mul_pos z.2 hq
    have hr : z.1.im*q ≤ z.1.im := mul_le_of_le_one_right z.2.le hq1
    have heS := (radial_conditional_weight_all W hW a ha z.1 z.2
      (z.1.im*q) hρ hr S hS U hU).2
    have heT := (radial_conditional_weight_all W hW a ha z.1 z.2
      (z.1.im*q) hρ hr T hT U hUT).2
    simp only [stoppedRemainingDensity_eq a q _ _ _ z.2,integral_const_mul]
    rw [← heS, ← heT]
    apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
    apply integral_mono
      (stoppedRadialTerminal_integrable a ha W hW z _ hρ hr T hT).integrableOn
      (stoppedRadialTerminal_integrable a ha W hW z _ hρ hr S hS).integrableOn
    intro b
    dsimp only
    split_ifs with ht hs hs
    · exact le_rfl
    · exact False.elim (hs ((hst b).trans_lt ht))
    · exact (radialWeight_bound a ha z.1 z.2 _ hρ hr b).1
    · exact le_rfl
  let q : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hq (n : ℕ) : 0 < q n ∧ q n ≤ 1 := by
    constructor
    · exact div_pos zero_lt_one (by positivity)
    · apply div_le_one_of_le₀ (by linarith [Nat.cast_nonneg (α := ℝ) n]) (by positivity)
  have hlim : Tendsto q atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  exact le_of_tendsto_of_tendsto'
    (stopped_remaining_integral_tendsto a ha W hW z T hT q hq hlim U)
    (stopped_remaining_integral_tendsto a ha W hW z S hS q hq hlim U)
    (fun n => hc (q n) (hq n).1 (hq n).2)

end ExactSLEGreen
end
end
 

 
section
 

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Classical NNReal ENNReal Topology

namespace ExactSLEGreen
open ExactSLEGenerator ExactSLEMain

lemma radialRemaining_time_joint_measurable (a : ℝ) (ha : 1/4 < a) (q : ℝ)
    (hq : 0 < q) (hq1 : q ≤ 1) :
    Measurable (fun p : ℝ≥0 × (ExactSLEGenerator.Driver × UpperPlane) =>
      radialRemaining a p.2.1.1 p.2.2.1 (p.2.2.1.im*q) p.1) := by
  have ha0 : 0<a := by linarith
  let Ω := ℝ≥0 × (ExactSLEGenerator.Driver × UpperPlane)
  let z : Ω → ℂ := fun p => p.2.2.1
  let b : Ω → ExactSLEGenerator.Driver := fun p => p.2.1
  let t : Ω → ℝ≥0 := Prod.fst
  have hz (ω : Ω) : 0<(z ω).im := ω.2.2.2
  have hzM : Measurable z := measurable_subtype_coe.comp (measurable_snd.comp measurable_snd)
  have hbM : Measurable b := measurable_fst.comp measurable_snd
  have htM : Measurable t := measurable_fst
  let ρ : Ω → ℝ := fun ω => (z ω).im*q
  have hρ (ω : Ω) : 0<ρ ω := mul_pos (hz ω) hq
  have hr (ω : Ω) : ρ ω≤(z ω).im := mul_le_of_le_one_right (hz ω).le hq1
  let δ : ℕ → Ω → ℝ := fun n ω => angleThreshold (z ω) n
  let L (n : ℕ) (ω : Ω) := explicitRadialLocalization a ha0 (z ω) (hz ω) (ρ ω) (δ n ω)
    (hρ ω) (hr ω) (angleThreshold_pos (z ω) (hz ω) n) (angleThreshold_initial (z ω) (hz ω) n)
  have hρM : Measurable ρ := hzM.im.mul_const q
  have hδM (n : ℕ) : Measurable (δ n) := by
    dsimp [δ,angleThreshold]
    exact (hzM.im.div hzM.norm).div_const _
  have hεM (n : ℕ) : Measurable (fun ω => (L n ω).ε) := by
    change Measurable (fun ω => heightFloor (z ω).im (ρ ω) (δ n ω)/2)
    unfold heightFloor
    fun_prop
  have hNM (n : ℕ) : Measurable (fun ω => (L n ω).N) := by
    change Measurable (fun ω => (⟨(z ω).im/δ n ω+logCeiling (z ω).im (ρ ω) (δ n ω)+1, _⟩ : ℝ≥0))
    apply Measurable.subtype_mk
    unfold logCeiling heightFloor
    fun_prop
  have hBM (n : ℕ) : Measurable (fun ω => (L n ω).B) := by
    change Measurable (fun ω => (⟨(z ω).im^2/(2*a*(δ n ω)^2)+1, _⟩ : ℝ≥0))
    apply Measurable.subtype_mk
    fun_prop
  let T (n : ℕ) (ω : Ω) := regionStop a (L n ω).ε (L n ω).hε (z ω)
    (L n ω).N (ρ ω) (δ n ω) (L n ω).B (b ω)
  have hTM (n : ℕ) : Measurable (T n) :=
    regionStop_parameter_measurable a (fun ω => (L n ω).ε) (fun ω => (L n ω).hε) z b _ ρ (δ n) _ (hεM n) hzM hbM
      (measurable_subtype_coe.comp (hNM n)) hρM (hδM n) (hBM n)
  have hPM : Measurable (physicalGreen a) := by
    have hx := X.continuous.measurable
    have hy := Y.continuous.measurable
    have hj := J.continuous.measurable
    unfold physicalGreen logGreen Q
    fun_prop
  let F (n : ℕ) (ω : Ω) := if t ω < T n ω then physicalGreen a (localState a (L n ω).ε (L n ω).hε (z ω) (t ω) (b ω)) else 0
  have hFM (n : ℕ) : Measurable (F n) := (hPM.comp
    ((localState_parameter_joint_measurable a (fun ω => (L n ω).ε) (fun ω => (L n ω).hε) z b (hεM n) hzM hbM).comp
      (htM.prodMk measurable_id))).ite (measurableSet_lt htM (hTM n)) measurable_const
  apply measurable_of_tendsto_metrizable hFM
  apply tendsto_pi_nhds.mpr
  intro ω
  exact localizationRemaining_tendsto a ha0 (z ω) (hz ω) (ρ ω) (hρ ω) (hr ω)
    (fun n => L n ω) (b ω) (t ω)

end ExactSLEGreen

namespace ExactSLEGenerator

 

lemma pastDriver_stopping_measurable
    (S : Driver → ℝ≥0∞) (hS : IsStoppingTime rawFiltration S) :
    Measurable[hS.measurableSpace] (fun b => pastDriver (S b).toNNReal b) := by
  classical
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
  have htop : MeasurableSet[hS.measurableSpace] {b | S b = ∞} :=
    hS.measurable (measurableSet_singleton ∞)
  let : MeasurableSpace Driver := hS.measurableSpace
  apply measurable_pi_iff.mpr
  intro n
  have h : Measurable (fun b => if S b = ∞ then (0 : ℝ)
      else b.1 (ExactSLEGreen.capTime S (u n) b)) :=
    Measurable.ite htop measurable_const (hval n)
  convert h using 1
  funext b
  change b.1 (min (u n) (S b).toNNReal) = _
  by_cases hb : S b = ∞
  · simp only [hb,ENNReal.toNNReal_top,min_zero,ite_true,b.2]
  · rw [ite_eq_right hb]
    congr 1
    unfold ExactSLEGreen.capTime
    conv_rhs => rw [← ENNReal.coe_toNNReal hb]
    simp only [← ENNReal.coe_min, ENNReal.toNNReal_coe, min_comm]

end ExactSLEGenerator

namespace ExactSLEGreen
open ExactSLEGenerator ExactSLEMain

lemma remainingMassDensity_time_joint_measurable (a : ℝ) (ha : 1/4 < a)
    (q : ℝ) (hq : 0 < q) (hq1 : q ≤ 1) :
    Measurable (fun p : ℝ≥0 × (ExactSLEGenerator.Driver × UpperPlane) =>
      remainingMassDensity a q p.1 p.2.1 p.2.2.1) := by
  have h := (radialRemaining_time_joint_measurable a ha q hq hq1).const_mul
    (Real.exp (-alpha a*Real.log 2))
  convert h using 1
  funext p
  exact ite_eq_left p.2.2.2

lemma survivingGreen_time_joint_measurable (a : ℝ) (ha : 1/4 < a) :
    Measurable (fun p : ℝ≥0 × (ExactSLEGenerator.Driver × UpperPlane) =>
      survivingGreen a p.1 p.2.1 p.2.2.1) := by
  let q : ℕ → ℝ := fun n => 1 / ((n : ℝ)+1)
  have hq (n : ℕ) : 0<q n ∧ q n≤1 := by
    constructor
    · exact div_pos zero_lt_one (by positivity)
    · apply div_le_one_of_le₀ (by linarith [Nat.cast_nonneg (α := ℝ) n]) (by positivity)
  apply measurable_of_tendsto_metrizable
    (fun n => remainingMassDensity_time_joint_measurable a ha (q n) (hq n).1 (hq n).2)
  apply tendsto_pi_nhds.mpr
  intro p
  exact remaining_to_surviving a ha p.1 q hq
    tendsto_one_div_add_atTop_nhds_zero_nat p.2.1 p.2.2.1 p.2.2.2

lemma survivingGreen_driver_congr (a : ℝ) (b c : ExactSLEGenerator.Driver)
    (t : ℝ≥0) (h : ∀ s≤t, b.1 s=c.1 s) (z : ℂ) :
    survivingGreen a t b z = survivingGreen a t c z := by
  simp only [survivingGreen,alive_driver_congr h,actualState_driver_congr h]

 

theorem stoppedSurvivingGreen_raw_joint (a : ℝ) (ha : 1/4 < a)
    (S : ExactSLEGenerator.Driver → ℝ≥0∞) (hS : IsStoppingTime rawFiltration S) :
    letI : MeasurableSpace ExactSLEGenerator.Driver := hS.measurableSpace
    Measurable (fun p : ExactSLEGenerator.Driver × UpperPlane =>
      stoppedSurvivingGreen a (S p.1) p.1 p.2.1) := by
  have hp : @Measurable (ExactSLEGenerator.Driver × UpperPlane)
      (ℝ≥0 × (ExactSLEGenerator.Driver × UpperPlane))
      (hS.measurableSpace.prod inferInstance) inferInstance
      (fun p => ((S p.1).toNNReal,(pastDriver (S p.1).toNNReal p.1,p.2))) := by
    exact ((ENNReal.measurable_toNNReal.comp hS.measurable).comp
      (@measurable_fst _ _ hS.measurableSpace inferInstance)).prodMk
      (((pastDriver_stopping_measurable S hS).comp
        (@measurable_fst _ _ hS.measurableSpace inferInstance)).prodMk
        (@measurable_snd _ _ hS.measurableSpace inferInstance))
  have hM := (survivingGreen_time_joint_measurable a ha).comp hp
  have htop : MeasurableSet[hS.measurableSpace] {b | S b=∞} :=
    hS.measurable (measurableSet_singleton ∞)
  let : MeasurableSpace ExactSLEGenerator.Driver := hS.measurableSpace
  have hm : Measurable (fun p : ExactSLEGenerator.Driver × UpperPlane =>
      if S p.1=∞ then 0 else
        survivingGreen a (S p.1).toNNReal (pastDriver (S p.1).toNNReal p.1) p.2.1) :=
    Measurable.ite (measurable_fst htop) measurable_const hM
  convert hm using 1
  funext p
  unfold stoppedSurvivingGreen
  congr 1
  exact survivingGreen_driver_congr a p.1 _ _
    (fun s hs => (pastDriver_eq (S p.1).toNNReal p.1 s hs).symm) p.2.1

lemma stoppedSurvivingGreen_joint_measurable (a : ℝ) (ha : 1/4 < a)
    (S : ExactSLEGenerator.Driver → ℝ≥0∞) (hS : IsStoppingTime rawFiltration S) :
    Measurable (fun p : ExactSLEGenerator.Driver × UpperPlane =>
      stoppedSurvivingGreen a (S p.1) p.1 p.2.1) :=
  (stoppedSurvivingGreen_raw_joint a ha S hS).mono
    (SLEExactGauge.MassVersions.prod_sigma_le hS.measurableSpace_le _) le_rfl

 

theorem stoppedRemainingDensity_raw_joint (a : ℝ) (ha : 1/4 < a)
    (q : ℝ) (hq : 0<q) (hq1 : q≤1)
    (S : ExactSLEGenerator.Driver → ℝ≥0∞) (hS : IsStoppingTime rawFiltration S) :
    letI : MeasurableSpace ExactSLEGenerator.Driver := hS.measurableSpace
    Measurable (fun p : ExactSLEGenerator.Driver × UpperPlane =>
      stoppedRemainingDensity a q (S p.1) p.1 p.2.1) := by
  have hp : @Measurable (ExactSLEGenerator.Driver × UpperPlane)
      (ℝ≥0 × (ExactSLEGenerator.Driver × UpperPlane))
      (hS.measurableSpace.prod inferInstance) inferInstance
      (fun p => ((S p.1).toNNReal,(pastDriver (S p.1).toNNReal p.1,p.2))) := by
    exact ((ENNReal.measurable_toNNReal.comp hS.measurable).comp
      (@measurable_fst _ _ hS.measurableSpace inferInstance)).prodMk
      (((pastDriver_stopping_measurable S hS).comp
        (@measurable_fst _ _ hS.measurableSpace inferInstance)).prodMk
        (@measurable_snd _ _ hS.measurableSpace inferInstance))
  have hM := (remainingMassDensity_time_joint_measurable a ha q hq hq1).comp hp
  have htop : MeasurableSet[hS.measurableSpace] {b | S b=∞} :=
    hS.measurable (measurableSet_singleton ∞)
  let : MeasurableSpace ExactSLEGenerator.Driver := hS.measurableSpace
  have hm : Measurable (fun p : ExactSLEGenerator.Driver × UpperPlane =>
      if S p.1=∞ then 0 else
        remainingMassDensity a q (S p.1).toNNReal (pastDriver (S p.1).toNNReal p.1) p.2.1) :=
    Measurable.ite (measurable_fst htop) measurable_const hM
  convert hm using 1
  funext p
  unfold stoppedRemainingDensity
  congr 1
  simp only [remainingMassDensity, ite_eq_left p.2.2]
  congr 1
  exact radialRemaining_driver_congr a (by linarith) p.2.1 p.2.2 _
    (mul_pos p.2.2 hq) (mul_le_of_le_one_right p.2.2.le hq1) p.1 _ _
    (fun s hs => (pastDriver_eq (S p.1).toNNReal p.1 s hs).symm)

lemma stoppedRemainingDensity_joint_measurable (a : ℝ) (ha : 1/4 < a)
    (q : ℝ) (hq : 0<q) (hq1 : q≤1)
    (S : ExactSLEGenerator.Driver → ℝ≥0∞) (hS : IsStoppingTime rawFiltration S) :
    Measurable (fun p : ExactSLEGenerator.Driver × UpperPlane =>
      stoppedRemainingDensity a q (S p.1) p.1 p.2.1) :=
  (stoppedRemainingDensity_raw_joint a ha q hq hq1 S hS).mono
    (SLEExactGauge.MassVersions.prod_sigma_le hS.measurableSpace_le _) le_rfl

end ExactSLEGreen
end
end
 

 
section
 

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped Classical NNReal ENNReal
namespace ExactSLEGreen
open ExactSLEMain ExactSLEGenerator ExactSLEFlow

lemma localState_fst_eq_solution {a ε : ℝ} (hε : 0<ε)
    (b : ExactSLEGenerator.Driver) {z : ℂ} {T : ℝ≥0} {f : ℝ→ℂ}
    (hf : odeUntil a b.1 z T f)
    (hlower : ∀u∈Icc (0:ℝ) T, ε≤(f u).im) :
    ∀u∈Icc (0:ℝ) T,
      (localState a ε hε z u.toNNReal b).1+(b.1 u.toNNReal:ℂ)=f u := by
  let g : ℝ→ℂ := fun u => (localState a ε hε z u.toNNReal b).1+(b.1 u.toNNReal:ℂ)
  let v : ℝ→ℂ := fun u => -(b.1 u.toNNReal:ℂ)
  have hgc : Continuous g :=
    ((localState_continuous a ε hε z b).fst.comp continuous_real_toNNReal).add
      (Complex.continuous_ofReal.comp (b.1.continuous.comp continuous_real_toNNReal))
  have hgd (u : ℝ) (hu : u∈Icc (0:ℝ) T) :
      HasDerivWithinAt g (cutoffVector a ε (g u+v u)) (Icc (0:ℝ) T) u := by
    have hd := (ContinuousLinearMap.fst ℝ ℂ ℝ).hasFDerivAt.comp_hasDerivWithinAt u
      (localState_noiseFree_deriv a ε hε z b T u hu)
    simpa only [g,v,ContinuousLinearMap.coe_fst',Prod.fst_sub,Prod.fst_smul,
      noise,Prod.smul_mk,Prod.fst,Complex.real_smul,mul_neg,mul_one,sub_neg_eq_add,add_neg_cancel_right,
      cutoffDrift,Function.comp_def] using hd
  have hfd (u : ℝ) (hu : u∈Icc (0:ℝ) T) :
      HasDerivWithinAt f (cutoffVector a ε (f u+v u)) (Icc (0:ℝ) T) u := by
    have hy : ε≤(f u-(b.1 u.toNNReal:ℂ)).im := by
      simpa only [Complex.sub_im,Complex.ofReal_im,sub_zero] using hlower u hu
    simpa only [v,←sub_eq_add_neg,cutoffVector,heightClamp_eq hy] using (hf.2 u hu).2
  exact additive_flow_unique (cutoffVector_lipschitz a ε hε) hgc.continuousOn
    (odeUntil_continuousOn hf) hgd hfd (by simp [localState_zero,hf.1,b.2])

lemma localState_eq_actual_of_height {a ε : ℝ} (hε : 0<ε)
    (b : ExactSLEGenerator.Driver) {z : ℂ} {T : ℝ≥0} {f : ℝ→ℂ}
    (hf : odeUntil a b.1 z T f)
    (hlower : ∀u∈Icc (0:ℝ) T, ε≤(f u).im) :
    ∀t≤T, localState a ε hε z t b=actualState a b.1 t z := by
  have he := localState_fst_eq_solution hε b hf hlower
  have hy (t : ℝ≥0) (ht : t≤T) : ε≤(localState a ε hε z t b).1.im := by
    have hh := congrArg Complex.im (he t ⟨t.coe_nonneg,ht⟩)
    simp only [Real.toNNReal_coe,Complex.add_im,Complex.ofReal_im,add_zero] at hh
    rw [hh]
    exact hlower t ⟨t.coe_nonneg,ht⟩
  intro t ht
  have h := state_eq_loewner_on_safe a ε hε b.1 b.1.continuous b.2 z
    (fun u => localState a ε hε z u b) (localState_continuous a ε hε z b)
    (fun u => localState_eq_zero a ε hε z u b) t (fun u hu => hy u (hu.trans ht))
  exact Prod.ext (h.2.1 t le_rfl).symm h.2.2.symm

lemma localState_eventually_eq_actual (a : ℝ) (b : ExactSLEGenerator.Driver)
    {z : ℂ} {t : ℝ≥0} (hz : alive a b.1 t z) :
    ∀ᶠ n : ℕ in atTop,
      localState a (1/((n:ℝ)+1)) (by positivity) z t b=actualState a b.1 t z := by
  obtain ⟨f,hf⟩ := hz
  obtain ⟨η,hη,hηf⟩ := odeUntil_height_lower hf
  filter_upwards [tendsto_one_div_add_atTop_nhds_zero_nat.eventually (gt_mem_nhds hη)] with n hn
  exact localState_eq_actual_of_height (by positivity) b hf
    (fun u hu => hn.le.trans (hηf u hu)) t le_rfl

lemma survivingGreen_pos_iff (a : ℝ) (t : ℝ≥0) (b : ExactSLEGenerator.Driver) (z : ℂ) :
    0<survivingGreen a t b z ↔ alive a b.1 t z := by
  classical
  unfold survivingGreen
  split_ifs
  · exact iff_of_true (mul_pos (Real.exp_pos _) (Real.exp_pos _)) ‹_›
  · simp_all

lemma measurableSet_alive_joint (a : ℝ) (ha : 1/4<a) :
    MeasurableSet {p : ℝ≥0×(ExactSLEGenerator.Driver×UpperPlane) |
      alive a p.2.1.1 p.1 p.2.2.1} := by
  simp_rw [←survivingGreen_pos_iff]
  exact measurableSet_lt measurable_const (survivingGreen_time_joint_measurable a ha)

 
def killedState (a : ℝ) (t : ℝ≥0) (b : ExactSLEGenerator.Driver) (z : ℂ) : State :=
  if alive a b.1 t z then actualState a b.1 t z else 0

lemma killedState_time_joint_measurable (a : ℝ) (ha : 1/4<a) :
    Measurable (fun p : ℝ≥0×(ExactSLEGenerator.Driver×UpperPlane) =>
      killedState a p.1 p.2.1 p.2.2.1) := by
  classical
  apply measurable_of_tendsto_metrizable (f:=fun (n : ℕ) p =>
    if alive a p.2.1.1 p.1 p.2.2.1 then
      localState a (1/((n:ℝ)+1)) (by positivity) p.2.2.1 p.1 p.2.1 else 0)
  · intro n
    exact (localState_parameter_joint_measurable a (fun _ => 1/((n:ℝ)+1))
      (fun _ => by positivity) (fun p : ExactSLEGenerator.Driver×UpperPlane => p.2.1)
      Prod.fst measurable_const (measurable_subtype_coe.comp measurable_snd)
      measurable_fst).ite (measurableSet_alive_joint a ha) measurable_const
  · apply tendsto_pi_nhds.mpr
    intro p
    by_cases hp : alive a p.2.1.1 p.1 p.2.2.1
    · simp only [ite_eq_left hp,killedState]
      exact tendsto_const_nhds.congr' ((localState_eventually_eq_actual a p.2.1 hp).mono (fun _ h => h.symm))
    · simp only [ite_eq_right hp,killedState]
      exact tendsto_const_nhds

lemma loewnerMap_time_joint_measurable (a : ℝ) (ha : 1/4<a) :
    Measurable (fun p : ℝ≥0×(ExactSLEGenerator.Driver×UpperPlane) =>
      loewnerMap a p.2.1.1 p.1 p.2.2.1) := by
  classical
  have he (p : ℝ≥0×(ExactSLEGenerator.Driver×UpperPlane)) :
      loewnerMap a p.2.1.1 p.1 p.2.2.1 =
        if alive a p.2.1.1 p.1 p.2.2.1 then
          (killedState a p.1 p.2.1 p.2.2.1).1+(p.2.1.1 p.1:ℂ) else 0 := by
    by_cases h : alive a p.2.1.1 p.1 p.2.2.1
    · simp only [ite_eq_left h,killedState,actualState,sub_add_cancel]
    · simp only [ite_eq_right h,loewnerMap,dite_eq_right h]
  simp_rw [he]
  exact ((killedState_time_joint_measurable a ha).fst.add
    ((Complex.continuous_ofReal.comp (continuous_subtype_val.comp (continuous_fst.comp
      continuous_snd) |>.eval continuous_fst)).measurable)).ite
        (measurableSet_alive_joint a ha) measurable_const

end ExactSLEGreen
end
end

end OAI
