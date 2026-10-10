import Mathlib
import OAI.Probability.SLE.MomentGauge
import OAI.Probability.SLEGauge.RadonMoments

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
open ExactSLEGenerator ExactSLEMain
open MeasureTheory ProbabilityTheory Filter Set
open scoped Classical NNReal ENNReal Topology
lemma localizationStop_after_survival (a : ℝ) (ha : 0 < a) (z : ℂ) (hz : 0 < z.im)
    (ρ : ℝ) (hρ : 0 < ρ) (_hr : ρ ≤ z.im)
    (L : ∀ n, RadialLocalization a z ρ (angleThreshold z n)) (b : ExactSLEGenerator.Driver)
    (t : ℝ≥0) (ht : alive a b.1 t z) (htr : (t : ℝ≥0∞) < radialTime a b.1 z ρ) :
    ∀ᶠ n in atTop, t < regionStop a (L n).ε (L n).hε z (L n).N ρ (angleThreshold z n) (L n).B b := by
  obtain ⟨η,hη,hηs⟩ := actual_sine_lower a b.1 b.1.continuous z t ht
  filter_upwards [(angleThreshold_tendsto z).eventually (gt_mem_nhds hη)] with n hn
  let Ln := L n
  let T := regionStop a Ln.ε Ln.hε z Ln.N ρ (angleThreshold z n) Ln.B b
  let V := localState a Ln.ε Ln.hε z T b
  by_contra hnt
  have hTt : T ≤ t := le_of_not_gt hnt
  have he := regionStop_actualState a Ln.ε Ln.hε z Ln.N ρ (angleThreshold z n) Ln.B Ln.initial b T le_rfl
  rcases regionStop_true_exit a Ln.ε ha Ln.hε z Ln.N ρ (angleThreshold z n) hρ
    (angleThreshold_pos z hz n) Ln.B Ln.initial Ln.small Ln.large Ln.time b with hR|hS
  · have htime := regionStop_eq_radialTime a Ln.ε Ln.hε z Ln.N ρ (angleThreshold z n)
      Ln.B Ln.initial b hR
    have hle : radialTime a b.1 z ρ ≤ (t : ℝ≥0∞) := by
      rw [htime]
      exact ENNReal.coe_le_coe.mpr hTt
    exact not_le.mpr htr hle
  · have hs := regionStop_safe a Ln.ε Ln.hε z Ln.N ρ (angleThreshold z n) Ln.B Ln.initial b T le_rfl
    have hnp : 0 < ‖V.1‖ := (Ln.hε.trans_le hs.1).trans_le (Complex.im_le_norm _)
    have hd : Y V/‖V.1‖ = angleThreshold z n := (div_eq_iff hnp.ne').mpr hS
    have hη' := hηs T hTt
    rw [he.2,hd] at hη'
    exact not_le.mpr hn hη'

lemma localizationRemaining_tendsto (a : ℝ) (ha : 0<a) (z : ℂ) (hz : 0<z.im)
    (ρ : ℝ) (hρ : 0<ρ) (hr : ρ≤z.im)
    (L : ∀ n, RadialLocalization a z ρ (angleThreshold z n))
    (b : ExactSLEGenerator.Driver) (t : ℝ≥0) :
    Tendsto (fun n => if t < regionStop a (L n).ε (L n).hε z (L n).N ρ (angleThreshold z n) (L n).B b
      then physicalGreen a (localState a (L n).ε (L n).hε z t b) else 0)
      atTop (𝓝 (radialRemaining a b.1 z ρ t)) := by
  by_cases h : alive a b.1 t z ∧ (t : ℝ≥0∞)<radialTime a b.1 z ρ
  · apply tendsto_const_nhds.congr'
    filter_upwards [localizationStop_after_survival a ha z hz ρ hρ hr L b t h.1 h.2] with n hn
    rw [ite_eq_left hn,radialRemaining,ite_eq_left h]
    exact congrArg (physicalGreen a) (regionStop_actualState a (L n).ε (L n).hε z
      (L n).N ρ (angleThreshold z n) (L n).B (L n).initial b t hn.le).2
  · have hv (n : ℕ) : ¬ t < regionStop a (L n).ε (L n).hε z (L n).N ρ (angleThreshold z n) (L n).B b := by
      intro hn
      apply h
      refine ⟨(regionStop_actualState a (L n).ε (L n).hε z (L n).N ρ
        (angleThreshold z n) (L n).B (L n).initial b t hn.le).1, ?_⟩
      apply lt_of_lt_of_le (ENNReal.coe_lt_coe.mpr hn)
      apply le_sInf
      rintro u ⟨v,rfl,_,hv⟩
      exact ENNReal.coe_le_coe.mpr (regionStop_le_hit a (L n).ε (L n).hε z (L n).N ρ
        (angleThreshold z n) (L n).B (L n).initial b v hv)
    simpa only [ite_eq_right (hv _),radialRemaining,ite_eq_right h] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
end ExactSLEGreen
namespace ExactSLEGreen
open ExactSLEGenerator ExactSLEMain
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

theorem joint_radialRemaining_measurable (a : ℝ) (ha : 1/4 < a) (q : ℝ)
    (hq : 0 < q) (hq1 : q ≤ 1) (t : ℝ≥0) :
    Measurable (fun p : ExactSLEGenerator.Driver × {z : ℂ // 0 < z.im} =>
      radialRemaining a p.1.1 p.2.1 (p.2.1.im*q) t) := by
  have ha0 : 0<a := by linarith
  let Ω := ExactSLEGenerator.Driver × {z : ℂ // 0 < z.im}
  let z : Ω → ℂ := fun p => p.2.1
  let b : Ω → ExactSLEGenerator.Driver := Prod.fst
  have hz (ω : Ω) : 0<(z ω).im := ω.2.2
  have hzM : Measurable z := measurable_subtype_coe.comp measurable_snd
  have hbM : Measurable b := measurable_fst
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
  let F (n : ℕ) (ω : Ω) := if t < T n ω then physicalGreen a (localState a (L n ω).ε (L n ω).hε (z ω) t (b ω)) else 0
  have hFM (n : ℕ) : Measurable (F n) := (hPM.comp
    ((localState_parameter_joint_measurable a (fun ω => (L n ω).ε) (fun ω => (L n ω).hε) z b (hεM n) hzM hbM).comp
      (measurable_const.prodMk measurable_id))).ite (measurableSet_lt measurable_const (hTM n)) measurable_const
  apply measurable_of_tendsto_metrizable hFM
  apply tendsto_pi_nhds.mpr
  intro ω
  exact localizationRemaining_tendsto a ha0 (z ω) (hz ω) (ρ ω) (hρ ω) (hr ω)
    (fun n => L n ω) (b ω) t
end ExactSLEGreen

namespace ExactSLEGreen
open ExactSLEGenerator ExactSLEMain
open MeasureTheory ProbabilityTheory Filter Set
open scoped Classical NNReal ENNReal Topology
lemma radialRemaining_driver_congr (a : ℝ) (ha : 0<a) (z : ℂ) (hz : 0<z.im)
    (ρ : ℝ) (hρ : 0<ρ) (hr : ρ≤z.im) (b c : ExactSLEGenerator.Driver) (t : ℝ≥0)
    (h : ∀ s≤t,b.1 s=c.1 s) : radialRemaining a b.1 z ρ t = radialRemaining a c.1 z ρ t := by
  have hiff : radialTime a b.1 z ρ≤t ↔ radialTime a c.1 z ρ≤t := by
    constructor
    · intro hb
      rwa [← radialTime_driver_congr_before a ha z hz ρ hρ hr b c t h hb]
    · intro hc
      rwa [← radialTime_driver_congr_before a ha z hz ρ hρ hr c b t (fun s hs => (h s hs).symm) hc]
  have hh : (t : ℝ≥0∞)<radialTime a b.1 z ρ ↔ (t : ℝ≥0∞)<radialTime a c.1 z ρ := by
    simpa only [not_le] using hiff.not
  simp only [radialRemaining,alive_driver_congr h,hh,actualState_driver_congr h]
end ExactSLEGreen
namespace ExactSLEGreen
open MeasureTheory ProbabilityTheory ExactSLEGenerator ExactSLEMain
open scoped NNReal ENNReal
 

theorem radialRemaining_raw_joint (a : ℝ) (ha : 1/4<a) (q : ℝ) (hq : 0<q)
    (hq1 : q≤1) (t : ℝ≥0) :
    letI : MeasurableSpace ExactSLEGenerator.Driver := rawFiltration t
    Measurable (fun p : ExactSLEGenerator.Driver × {z : ℂ // 0<z.im} =>
      radialRemaining a p.1.1 p.2.1 (p.2.1.im*q) t)
    := by
  have he : (fun p : ExactSLEGenerator.Driver × {z : ℂ // 0<z.im} =>
      radialRemaining a p.1.1 p.2.1 (p.2.1.im*q) t) =
    (fun p : ExactSLEGenerator.Driver × {z : ℂ // 0<z.im} =>
      radialRemaining a (pastDriver t p.1).1 p.2.1 (p.2.1.im*q) t) := by
    funext p
    exact radialRemaining_driver_congr a (by linarith) p.2.1 p.2.2 _ (mul_pos p.2.2 hq)
      (mul_le_of_le_one_right p.2.2.le hq1) p.1 (pastDriver t p.1) t
      (fun s hs => (pastDriver_eq t p.1 s hs).symm)
  change @Measurable (ExactSLEGenerator.Driver × {z : ℂ // 0<z.im}) ℝ
    ((rawFiltration t).prod inferInstance) inferInstance _
  rw [he]
  have hp : @Measurable (ExactSLEGenerator.Driver × {z : ℂ // 0<z.im})
      (ExactSLEGenerator.Driver × {z : ℂ // 0<z.im})
      ((rawFiltration t).prod inferInstance) inferInstance (fun p => (pastDriver t p.1,p.2)) :=
    ((pastDriver_raw_measurable t).comp
      (@measurable_fst _ _ (rawFiltration t) inferInstance)).prodMk
      (@measurable_snd _ _ (rawFiltration t) inferInstance)
  exact @Measurable.comp (ExactSLEGenerator.Driver × {z : ℂ // 0<z.im})
    (ExactSLEGenerator.Driver × {z : ℂ // 0<z.im}) ℝ
    ((rawFiltration t).prod inferInstance) inferInstance inferInstance
    (fun p => radialRemaining a p.1.1 p.2.1 (p.2.1.im*q) t)
    (fun p => (pastDriver t p.1,p.2))
    (joint_radialRemaining_measurable a ha q hq hq1 t) hp
end ExactSLEGreen
namespace ExactSLEGreen
open MeasureTheory ProbabilityTheory ExactSLEGenerator ExactSLEMain
open scoped NNReal ENNReal
noncomputable def remainingMassDensity (a q : ℝ) (t : ℝ≥0) (b : ExactSLEGenerator.Driver) (z : ℂ) : ℝ :=
  if 0<z.im then Real.exp (-alpha a*Real.log 2)*radialRemaining a b.1 z (z.im*q) t else 0
end ExactSLEGreen
namespace ExactSLEGreen
open ExactSLEGenerator ExactSLEMain
open MeasureTheory ProbabilityTheory Filter Set
open scoped Classical NNReal ENNReal Topology
lemma remainingMassDensity_measurable (a : ℝ) (ha : 1/4<a) (q : ℝ) (hq : 0<q)
    (hq1 : q≤1) (t : ℝ≥0) :
    Measurable (fun p : ExactSLEGenerator.Driver × ℂ => remainingMassDensity a q t p.1 p.2) := by
  let U : Set (ExactSLEGenerator.Driver × ℂ) := {p | 0<p.2.im}
  have hU : MeasurableSet U := measurableSet_lt measurable_const (Complex.measurable_im.comp measurable_snd)
  have hm : Measurable (fun p : U =>
      Real.exp (-alpha a*Real.log 2)*radialRemaining a p.1.1.1 p.1.2 (p.1.2.im*q) t) := by
    have hp : Measurable (fun p : U => (p.1.1, (⟨p.1.2,p.2⟩ : {z : ℂ // 0<z.im}))) := by fun_prop
    exact measurable_const.mul ((joint_radialRemaining_measurable a ha q hq hq1 t).comp hp)
  exact hm.dite (g:=fun _ => 0) measurable_const hU
lemma remainingMassDensity_local_bound (a : ℝ) (ha : 1/4<a) (q : ℝ) (hq : 0<q)
    (hq1 : q≤1) (t : ℝ≥0) (b : ExactSLEGenerator.Driver) (c : ℝ) (hc : 0<c)
    (z : ℂ) (hz : c≤2*z.im) : ‖remainingMassDensity a q t b z‖≤(c*q)^(-alpha a) := by
  have hz0 : 0<z.im := by linarith
  have hb := radialRemaining_bound a ha z hz0 (z.im*q) (mul_pos hz0 hq)
    (mul_le_of_le_one_right hz0.le hq1) b t
  have ht : 0<2*z.im*q := by positivity
  calc
    _ = Real.exp (-alpha a*Real.log 2)*‖radialRemaining a b.1 z (z.im*q) t‖ := by
      simp only [remainingMassDensity,ite_eq_left hz0,norm_mul,Real.norm_of_nonneg (Real.exp_pos _).le]
    _ ≤ Real.exp (-alpha a*Real.log 2)*Real.exp (-alpha a*Real.log (z.im*q)) :=
      mul_le_mul_of_nonneg_left hb (Real.exp_pos _).le
    _ = (2*z.im*q)^(-alpha a) := by
      rw [←Real.exp_add,Real.rpow_def_of_pos ht]
      rw [show 2*z.im*q=2*(z.im*q) by ring,Real.log_mul (by norm_num) (mul_pos hz0 hq).ne']
      congr 1; ring
    _ ≤ _ := Real.rpow_le_rpow_of_nonpos (mul_pos hc hq)
      (mul_le_mul_of_nonneg_right hz hq.le) (neg_nonpos.mpr (alpha_pos ha).le)
lemma remainingMassEval_joint_integrable (a : ℝ) (ha : 1/4<a)
    (W : Measure ExactSLEGenerator.Driver) [IsFiniteMeasure W]
    (q : ℝ) (hq : 0<q) (hq1 : q≤1) (t : ℝ≥0)
    (K : Set ℂ) (hK : MeasurableSet K) (hKb : Bornology.IsBounded K)
    (c : ℝ) (hc : 0<c) (hcK : ∀ z,z∈K→c≤2*z.im)
    (f : ℂ → ℝ) (hf : Measurable f) (hfB : ∃ B : ℝ,0≤B ∧ ∀ z∈K,‖f z‖≤B) :
    Integrable (fun p : ExactSLEGenerator.Driver × ℂ =>
      f p.2 * remainingMassDensity a q t p.1 p.2) (W.prod (volume.restrict K)) := by
  obtain ⟨B,hB,hBf⟩ := hfB
  have : IsFiniteMeasure (volume.restrict K) := ⟨by simpa using hKb.measure_lt_top⟩
  have hm : Measurable (fun p : ExactSLEGenerator.Driver × ℂ =>
      f p.2 * remainingMassDensity a q t p.1 p.2) :=
    (hf.comp measurable_snd).mul (remainingMassDensity_measurable a ha q hq hq1 t)
  apply Integrable.of_bound hm.aestronglyMeasurable (B*((c*q)^(-alpha a)))
  have hmem : ∀ᵐ p ∂W.prod (volume.restrict K), p.2∈K :=
    (Measure.ae_prod_iff_ae_ae (hK.preimage measurable_snd)).mpr
      (Eventually.of_forall fun _ => ae_restrict_mem hK)
  filter_upwards [hmem] with p hp
  rw [norm_mul]
  exact mul_le_mul (hBf _ hp) (remainingMassDensity_local_bound a ha q hq hq1 t p.1 c hc p.2 (hcK _ hp))
    (norm_nonneg _) hB
end ExactSLEGreen
namespace ExactSLEGreen
open ExactSLEGenerator ExactSLEMain
open MeasureTheory ProbabilityTheory Filter Set
open scoped Classical NNReal ENNReal Topology
lemma finite_density_conditional (a : ℝ) (ha : 1/4<a)
    (W : Measure ExactSLEGenerator.Driver) [IsProbabilityMeasure W]
    (hW : IsBrownianReal (fun t (b : ExactSLEGenerator.Driver) => b.1 t) W)
    (q : ℝ) (hq : 0<q) (hq1 : q≤1) (t : ℝ≥0) (z : ℂ) (hz : 0<z.im)
    (U : Set ExactSLEGenerator.Driver) (hU : MeasurableSet[rawFiltration t] U) :
    (∫b in U, (timeMassDensity a q ∞ b z).toReal-(timeMassDensity a q t b z).toReal ∂W) =
      ∫b in U, remainingMassDensity a q t b z ∂W := by
  have he (b : ExactSLEGenerator.Driver) :
      (timeMassDensity a q ∞ b z).toReal-(timeMassDensity a q t b z).toReal =
        Real.exp (-alpha a*Real.log 2)*(if (t : ℝ≥0∞)<radialTime a b.1 z (z.im*q)
          then radialWeight a b.1 z (z.im*q) else 0) := by
    have hn := (fullRadialDensity_bound a ha z hz (2*z.im*q) (by positivity) (by nlinarith) b).1
    have hρ : 2*z.im*q/2=z.im*q := by ring
    by_cases hh : radialTime a b.1 z (z.im*q)≤t
    · simp only [timeMassDensity,le_top,ite_true,ite_eq_left hh,massDensity,ite_eq_left hz,
        ENNReal.toReal_ofReal hn,sub_self,ite_eq_right (not_lt.mpr hh),mul_zero]
    · simp only [timeMassDensity,le_top,ite_true,ite_eq_right hh,massDensity,ite_eq_left hz,
        ENNReal.toReal_zero,sub_zero,ite_eq_left (lt_of_not_ge hh),fullRadialDensity,hρ]
      exact ENNReal.toReal_ofReal (by simpa only [fullRadialDensity,hρ] using hn)
  simp_rw [he,remainingMassDensity,ite_eq_left hz]
  rw [integral_const_mul,integral_const_mul]
  congr 1
  have hS : IsStoppingTime rawFiltration (fun _ : ExactSLEGenerator.Driver => (t : WithTop ℝ≥0)) :=
    isStoppingTime_const _ _
  exact (radial_conditional_weight W hW a ha z hz (z.im*q) (mul_pos hz hq)
    (mul_le_of_le_one_right hz.le hq1) (fun _ => t) hS U
    ((hS.le_measurableSpace_of_const_le (fun _ => le_rfl)) _ hU)).2
end ExactSLEGreen
namespace ExactSLEGreen
open MeasureTheory ProbabilityTheory ExactSLEGenerator ExactSLEMain
open scoped NNReal ENNReal
 

theorem actual_finite_conditional_mass (a : ℝ) (ha : 1/4<a)
    (W : Measure ExactSLEGenerator.Driver) [IsProbabilityMeasure W]
    (hW : IsBrownianReal (fun t (b : ExactSLEGenerator.Driver) => b.1 t) W)
    (q : ℝ) (hq : 0<q) (hq1 : q≤1) (t : ℝ≥0)
    (K : Set ℂ) (hK : MeasurableSet K) (hKb : Bornology.IsBounded K)
    (c : ℝ) (hc : 0<c) (hcK : ∀ z,z∈K→c≤2*z.im)
    (f : ℂ → ℝ) (hf : Measurable f) (hfB : ∃ B : ℝ,0≤B ∧ ∀ z∈K,‖f z‖≤B)
    (U : Set ExactSLEGenerator.Driver) (hU : MeasurableSet[rawFiltration t] U) :
    (∫b in U, actualMassEval a q ∞ K f b-actualMassEval a q t K f b ∂W) =
      ∫b in U, (∫z in K, f z*remainingMassDensity a q t b z) ∂W
    := by
  have hIm (v : ℝ≥0∞) := actualMassEval_joint_integrable a ha W q hq hq1 v K hK hKb c hc hcK f hf hfB
  have hI (v : ℝ≥0∞) : Integrable (fun p : ExactSLEGenerator.Driver × ℂ =>
      f p.2*(timeMassDensity a q v p.1 p.2).toReal) ((W.restrict U).prod (volume.restrict K)) :=
    (hIm v).mono_measure (Measure.prod_mono Measure.restrict_le_self le_rfl)
  have hsub : Integrable (fun p : ExactSLEGenerator.Driver × ℂ => f p.2*
      ((timeMassDensity a q ∞ p.1 p.2).toReal-(timeMassDensity a q t p.1 p.2).toReal))
      ((W.restrict U).prod (volume.restrict K)) := by
    convert (hI ∞).sub (hI t) using 1
    first | rfl | (funext point; dsimp only [Pi.sub_apply]; ring)
  have he (b : ExactSLEGenerator.Driver) : actualMassEval a q ∞ K f b-actualMassEval a q t K f b =
      ∫z in K, f z*((timeMassDensity a q ∞ b z).toReal-(timeMassDensity a q t b z).toReal) := by
    simp only [actualMassEval,mul_sub]
    exact (integral_sub
      (actualMassEval_integrable a ha q hq hq1 ∞ K hK hKb c hc hcK f hf hfB b)
      (actualMassEval_integrable a ha q hq hq1 t K hK hKb c hc hcK f hf hfB b)).symm
  simp_rw [he]
  rw [integral_integral_swap hsub]
  conv_rhs => rw [integral_integral_swap
    (remainingMassEval_joint_integrable a ha (W.restrict U) q hq hq1 t K hK hKb c hc hcK f hf hfB)]
  apply setIntegral_congr_fun hK
  intro z hzK
  dsimp only
  rw [integral_const_mul,integral_const_mul]
  congr 1
  exact finite_density_conditional a ha W hW q hq hq1 t z (by have := hcK z hzK; linarith) U hU
end ExactSLEGreen

namespace ExactSLEGreen
open ExactSLEGenerator ExactSLEMain
open scoped Classical NNReal ENNReal
 
noncomputable def survivingGreen (a : ℝ) (t : ℝ≥0) (b : ExactSLEGenerator.Driver) (z : ℂ) : ℝ :=
  if alive a b.1 t z then Real.exp (-alpha a*Real.log 2)*physicalGreen a (actualState a b.1 t z) else 0
end ExactSLEGreen
namespace ExactSLEGreen
open MeasureTheory ProbabilityTheory Filter Set ExactSLEGenerator ExactSLEMain
open scoped NNReal ENNReal Topology
lemma physicalRadius_actual_pos (a : ℝ) (b : ExactSLEGenerator.Driver) (z : ℂ)
    (t : ℝ≥0) (ht : alive a b.1 t z) : 0<physicalRadius (actualState a b.1 t z) := by
  obtain ⟨f,hf⟩ := ht
  have h := fullRadius_pos b.1.continuous hf le_rfl
  rw [←actual_radius_eq_full b.1.continuous ⟨f,hf⟩] at h
  linarith
lemma physicalRadius_actual_anti (a : ℝ) (ha : 0<a) (b : ExactSLEGenerator.Driver) (z : ℂ)
    (s t : ℝ≥0) (hst : s≤t) (ht : alive a b.1 t z) :
    physicalRadius (actualState a b.1 t z)≤physicalRadius (actualState a b.1 s z) := by
  obtain ⟨f,hf⟩ := ht
  have he := fullRadius_active_clock b.1.continuous hf hst le_rfl
  have hp := fullRadius_pos b.1.continuous hf hst
  have hn := activeODEClock_nonneg (b:=b.1) (T:=t) (σ:=s) (f:=f) (show (s:ℝ)≤t from hst)
  have hle : fullLoewnerRadius a b.1 z t≤fullLoewnerRadius a b.1 z s := by
    rw [he]
    exact mul_le_of_le_one_right hp.le (Real.exp_le_one_iff.mpr (by nlinarith))
  rw [←actual_radius_eq_full b.1.continuous ⟨f,hf⟩,
    ←actual_radius_eq_full b.1.continuous ⟨f,odeUntil_mono hf hst⟩] at hle
  linarith
lemma survivingGreen_nonneg (a : ℝ) (t : ℝ≥0) (b : ExactSLEGenerator.Driver) (z : ℂ) :
    0 ≤ survivingGreen a t b z := by
  unfold survivingGreen physicalGreen
  split_ifs <;> positivity
lemma remainingMassDensity_nonneg (a q : ℝ) (t : ℝ≥0) (b : ExactSLEGenerator.Driver) (z : ℂ) :
    0≤remainingMassDensity a q t b z := by
  unfold remainingMassDensity radialRemaining physicalGreen
  split_ifs <;> positivity
lemma remaining_to_surviving (a : ℝ) (ha : 1/4<a) (t : ℝ≥0)
    (q : ℕ → ℝ) (hq : ∀n,0<q n ∧ q n≤1) (hlim : Tendsto q atTop (𝓝 0))
    (b : ExactSLEGenerator.Driver) (z : ℂ) (hz : 0<z.im) :
    Tendsto (fun n => remainingMassDensity a (q n) t b z) atTop (𝓝 (survivingGreen a t b z)) := by
  by_cases ht : alive a b.1 t z
  · have hR := physicalRadius_actual_pos a b z t ht
    have hqR : ∀ᶠ n in atTop, z.im*q n<physicalRadius (actualState a b.1 t z) := by
      have hconv : Tendsto (fun n => z.im*q n) atTop (𝓝 0) := by simpa using hlim.const_mul z.im
      exact hconv.eventually (gt_mem_nhds hR)
    apply tendsto_const_nhds.congr'
    filter_upwards [hqR] with n hn
    have hnT : (t : ℝ≥0∞)<radialTime a b.1 z (z.im*q n) := by
      by_contra h
      have hTt := le_of_not_gt h
      have hfin : radialTime a b.1 z (z.im*q n)≠∞ := ne_top_of_le_ne_top ENNReal.coe_ne_top hTt
      have hle : (radialTime a b.1 z (z.im*q n)).toNNReal≤t := by
        exact ENNReal.coe_le_coe.mp (by simpa only [ENNReal.coe_toNNReal hfin] using hTt)
      have hh := (radialTime_attained a (by linarith) z hz _ (mul_pos hz (hq n).1)
        (mul_le_of_le_one_right hz.le (hq n).2) b hfin).2
      have he := physicalRadius_actual_anti a (by linarith) b z _ t hle ht
      rw [hh] at he
      exact not_le.mpr hn he
    simp only [remainingMassDensity,ite_eq_left hz,radialRemaining,ht,hnT,and_self,ite_true,survivingGreen]
  · simpa only [remainingMassDensity,ite_eq_left hz,radialRemaining,ht,false_and,ite_false,survivingGreen,
      mul_zero] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0:ℝ)) atTop (𝓝 0))
end ExactSLEGreen
namespace ExactSLEGreen
open MeasureTheory ProbabilityTheory Filter Set ExactSLEGenerator ExactSLEMain
open scoped Classical NNReal ENNReal Topology
lemma remainingMassDensity_mean_bound (a : ℝ) (ha : 1/4<a)
    (W : Measure ExactSLEGenerator.Driver) [IsProbabilityMeasure W]
    (hW : IsBrownianReal (fun t (b : ExactSLEGenerator.Driver) => b.1 t) W)
    (q : ℝ) (hq : 0<q) (hq1 : q≤1) (t : ℝ≥0) (z : ℂ) (hz : 0<z.im) :
    Integrable (fun b => remainingMassDensity a q t b z) W ∧
      (∫b,remainingMassDensity a q t b z∂W)≤Real.exp (-alpha a*Real.log 2)*physicalGreen a (z,0) := by
  have hS : IsStoppingTime rawFiltration (fun _ : ExactSLEGenerator.Driver => (t : WithTop ℝ≥0)) :=
    isStoppingTime_const _ _
  have H := radial_conditional_weight W hW a ha z hz (z.im*q) (mul_pos hz hq)
    (mul_le_of_le_one_right hz.le hq1) (fun _ => t) hS univ MeasurableSet.univ
  have hmean := radialWeight_mean W hW a ha z hz (z.im*q) (mul_pos hz hq)
    (mul_le_of_le_one_right hz.le hq1)
  constructor
  · simpa only [remainingMassDensity,ite_eq_left hz] using H.1.const_mul (Real.exp (-alpha a*Real.log 2))
  · simp only [remainingMassDensity,ite_eq_left hz]
    have He := H.2
    simp only [setIntegral_univ] at He
    rw [integral_const_mul,←He]
    apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
    rw [←hmean.2]
    apply integral_mono_of_nonneg
    · filter_upwards [] with b
      split_ifs
      · exact (radialWeight_bound a ha z hz _ (mul_pos hz hq)
          (mul_le_of_le_one_right hz.le hq1) b).1
      · exact le_rfl
    · exact hmean.1
    · filter_upwards [] with b
      split_ifs
      · exact le_rfl
      · exact (radialWeight_bound a ha z hz _ (mul_pos hz hq)
          (mul_le_of_le_one_right hz.le hq1) b).1
end ExactSLEGreen
namespace ExactSLEGreen
open MeasureTheory ProbabilityTheory Filter ExactSLEGenerator ExactSLEMain
open scoped Classical NNReal ENNReal Topology
 

end ExactSLEGreen
end
end

end OAI
