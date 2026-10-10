import Mathlib
import OAI.Probability.SLE.MomentGauge
import OAI.Probability.SLEGauge.StoppedWeights

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
namespace ExactSLEMain
open ExactSLEGreen
theorem finite_tilt_mean_one (W : Measure Driver) [IsProbabilityMeasure W]
    (hW : IsBrownianReal (fun (t : ℝ≥0) (b : Driver) => b.1 t) W)
    (a θ : ℝ) (ha : 1 / 4 < a) (hθ : 0 < θ) (hθπ : θ < Real.pi) (l : ℕ) :
    Integrable (fun b : Driver => tiltWeight a θ b.1 l) W ∧
    (∫ b : Driver, tiltWeight a θ b.1 l ∂W) = 1 := by
  have ha0 : 0 < a := by linarith
  have hs := Real.sin_pos_of_pos_of_lt_pi hθ hθπ
  have hz : 0 < (fromDisk θ 0).im := by simpa only [fromDisk_zero_im] using hs
  have hρ : 0 < Real.sin θ*Real.exp (-2*a*l) := mul_pos hs (Real.exp_pos _)
  have hr : Real.sin θ*Real.exp (-2*a*l) ≤ (fromDisk θ 0).im := by
    rw [fromDisk_zero_im]
    have he : Real.exp (-2*a*l) ≤ 1 := Real.exp_le_one_iff.mpr (by
      have h : (0 : ℝ) ≤ 2*a*l := by positivity
      nlinarith)
    exact (mul_le_mul_of_nonneg_left he hs.le).trans_eq (mul_one _)
  have hm := radialWeight_mean W hW a ha (fromDisk θ 0) hz _ hρ hr
  have he : (fun b : Driver => tiltWeight a θ b.1 l) =
      fun b : Driver => radialWeight a b.1 (fromDisk θ 0) (Real.sin θ*Real.exp (-2*a*l)) /
        physicalGreen a (fromDisk θ 0,0) := funext fun b => tiltWeight_radialWeight a θ ha hθ hθπ b l
  rw [he]
  refine ⟨hm.1.div_const _,?_⟩
  rw [integral_div,hm.2]
  exact div_self (show physicalGreen a (fromDisk θ 0,0) ≠ 0 from (Real.exp_pos _).ne')

end ExactSLEMain

namespace ExactSLEGreen
open ExactSLEGenerator ExactSLEMain
open scoped Classical

noncomputable def radialRemaining (a : ℝ) (b : ℝ≥0 → ℝ) (z : ℂ) (ρ : ℝ) (t : ℝ≥0) : ℝ :=
  if alive a b t z ∧ (t : ℝ≥0∞) < radialTime a b z ρ then
    physicalGreen a (actualState a b t z) else 0

noncomputable def radialStop (a : ℝ) (ha : 0 < a) (z : ℂ) (hz : 0 < z.im)
    (ρ : ℝ) (hρ : 0 < ρ) (hr : ρ ≤ z.im) (n : ℕ) : ExactSLEGenerator.Driver → ℝ≥0 :=
  let L := radialLocalization a ha z hz ρ (angleThreshold z n) hρ hr
    (angleThreshold_pos z hz n) (angleThreshold_initial z hz n)
  regionStop a L.ε L.hε z L.N ρ (angleThreshold z n) L.B

lemma radialStop_actual (a : ℝ) (ha : 0 < a) (z : ℂ) (hz : 0 < z.im)
    (ρ : ℝ) (hρ : 0 < ρ) (hr : ρ ≤ z.im) (n : ℕ) (b : ExactSLEGenerator.Driver)
    (t : ℝ≥0) (ht : t ≤ radialStop a ha z hz ρ hρ hr n b) :
    alive a b.1 t z := by
  let L := radialLocalization a ha z hz ρ (angleThreshold z n) hρ hr
    (angleThreshold_pos z hz n) (angleThreshold_initial z hz n)
  exact (regionStop_actualState a L.ε L.hε z L.N ρ (angleThreshold z n) L.B L.initial b t ht).1

lemma radialStop_le_radialTime (a : ℝ) (ha : 0 < a) (z : ℂ) (hz : 0 < z.im)
    (ρ : ℝ) (hρ : 0 < ρ) (hr : ρ ≤ z.im) (n : ℕ) (b : ExactSLEGenerator.Driver) :
    (radialStop a ha z hz ρ hρ hr n b : ℝ≥0∞) ≤ radialTime a b.1 z ρ := by
  let L := radialLocalization a ha z hz ρ (angleThreshold z n) hρ hr
    (angleThreshold_pos z hz n) (angleThreshold_initial z hz n)
  apply le_sInf
  rintro u ⟨t,rfl,_,ht⟩
  exact ENNReal.coe_le_coe.mpr (regionStop_le_hit a L.ε L.hε z L.N ρ (angleThreshold z n)
    L.B L.initial b t ht)

lemma radialStop_after_survival (a : ℝ) (ha : 0 < a) (z : ℂ) (hz : 0 < z.im)
    (ρ : ℝ) (hρ : 0 < ρ) (hr : ρ ≤ z.im) (b : ExactSLEGenerator.Driver)
    (t : ℝ≥0) (ht : alive a b.1 t z) (htr : (t : ℝ≥0∞) < radialTime a b.1 z ρ) :
    ∀ᶠ n in atTop, t < radialStop a ha z hz ρ hρ hr n b := by
  obtain ⟨η,hη,hηs⟩ := actual_sine_lower a b.1 b.1.continuous z t ht
  filter_upwards [(angleThreshold_tendsto z).eventually (gt_mem_nhds hη)] with n hn
  let L := radialLocalization a ha z hz ρ (angleThreshold z n) hρ hr
    (angleThreshold_pos z hz n) (angleThreshold_initial z hz n)
  let T := radialStop a ha z hz ρ hρ hr n b
  let V := localState a L.ε L.hε z T b
  by_contra hnt
  have hTt : T ≤ t := le_of_not_gt hnt
  have he := regionStop_actualState a L.ε L.hε z L.N ρ (angleThreshold z n) L.B L.initial b T le_rfl
  rcases regionStop_true_exit a L.ε ha L.hε z L.N ρ (angleThreshold z n) hρ
    (angleThreshold_pos z hz n) L.B L.initial L.small L.large L.time b with hR|hS
  · have htime := regionStop_eq_radialTime a L.ε L.hε z L.N ρ (angleThreshold z n)
      L.B L.initial b hR
    have hle : radialTime a b.1 z ρ ≤ (t : ℝ≥0∞) := by
      rw [htime]
      exact ENNReal.coe_le_coe.mpr hTt
    exact not_le.mpr htr hle
  · have hs := regionStop_safe a L.ε L.hε z L.N ρ (angleThreshold z n) L.B L.initial b T le_rfl
    have hnp : 0 < ‖V.1‖ := (L.hε.trans_le hs.1).trans_le (Complex.im_le_norm _)
    have hd : Y V/‖V.1‖ = angleThreshold z n := (div_eq_iff hnp.ne').mpr hS
    have hη' := hηs T hTt
    rw [he.2,hd] at hη'
    exact not_le.mpr hn hη'

lemma radialStop_eventually_eq (a : ℝ) (ha : 0 < a) (z : ℂ) (hz : 0 < z.im)
    (ρ : ℝ) (hρ : 0 < ρ) (hr : ρ ≤ z.im) (b : ExactSLEGenerator.Driver)
    (hfin : radialTime a b.1 z ρ ≠ ∞) :
    ∀ᶠ n in atTop, (radialStop a ha z hz ρ hρ hr n b : ℝ≥0∞) = radialTime a b.1 z ρ := by
  let t := (radialTime a b.1 z ρ).toNNReal
  have ht := radialTime_attained a ha z hz ρ hρ hr b hfin
  obtain ⟨η,hη,hηs⟩ := actual_sine_lower a b.1 b.1.continuous z t ht.1
  filter_upwards [(angleThreshold_tendsto z).eventually (gt_mem_nhds hη)] with n hn
  let L := radialLocalization a ha z hz ρ (angleThreshold z n) hρ hr
    (angleThreshold_pos z hz n) (angleThreshold_initial z hz n)
  let T := radialStop a ha z hz ρ hρ hr n b
  let V := localState a L.ε L.hε z T b
  have hTt : T ≤ t := regionStop_le_hit a L.ε L.hε z L.N ρ (angleThreshold z n) L.B L.initial b t ht.2
  have he := regionStop_actualState a L.ε L.hε z L.N ρ (angleThreshold z n) L.B L.initial b T le_rfl
  rcases regionStop_true_exit a L.ε ha L.hε z L.N ρ (angleThreshold z n) hρ
    (angleThreshold_pos z hz n) L.B L.initial L.small L.large L.time b with hR|hS
  · exact (regionStop_eq_radialTime a L.ε L.hε z L.N ρ (angleThreshold z n) L.B L.initial b hR).symm
  · have hs := regionStop_safe a L.ε L.hε z L.N ρ (angleThreshold z n) L.B L.initial b T le_rfl
    have hnp : 0 < ‖V.1‖ := (L.hε.trans_le hs.1).trans_le (Complex.im_le_norm _)
    have hd : Y V/‖V.1‖ = angleThreshold z n := (div_eq_iff hnp.ne').mpr hS
    have hη' := hηs T hTt
    rw [he.2,hd] at hη'
    exact False.elim (not_le.mpr hn hη')

lemma radialStop_before_tendsto (a : ℝ) (_ha : 1/4 < a) (ha0 : 0 < a)
    (z : ℂ) (hz : 0 < z.im) (ρ : ℝ) (hρ : 0 < ρ) (hr : ρ ≤ z.im)
    (b : ExactSLEGenerator.Driver) (t : ℝ≥0) :
    Tendsto (fun n => if t < radialStop a ha0 z hz ρ hρ hr n b then
        physicalGreen a (actualState a b.1 t z) else 0) atTop
      (𝓝 (radialRemaining a b.1 z ρ t)) := by
  by_cases hg : alive a b.1 t z ∧ (t : ℝ≥0∞) < radialTime a b.1 z ρ
  · rw [radialRemaining,ite_eq_left hg]
    apply Filter.Tendsto.congr' _ tendsto_const_nhds
    filter_upwards [radialStop_after_survival a ha0 z hz ρ hρ hr b t hg.1 hg.2] with n hn
    simp only [ite_eq_left hn]
  · rw [radialRemaining,ite_eq_right hg]
    have hc : ∀ n, ¬ t < radialStop a ha0 z hz ρ hρ hr n b := by
      intro n hn
      apply hg
      exact ⟨radialStop_actual a ha0 z hz ρ hρ hr n b t hn.le,
        (ENNReal.coe_lt_coe.mpr hn).trans_le (radialStop_le_radialTime a ha0 z hz ρ hρ hr n b)⟩
    simp only [ite_eq_right (hc _)]
    exact tendsto_const_nhds

lemma radialStop_terminal_tendsto (a : ℝ) (ha : 1/4 < a) (ha0 : 0 < a)
    (z : ℂ) (hz : 0 < z.im) (ρ : ℝ) (hρ : 0 < ρ) (hr : ρ ≤ z.im)
    (b : ExactSLEGenerator.Driver) (t : ℝ≥0) :
    Tendsto (fun n => if t < radialStop a ha0 z hz ρ hρ hr n b then
        radialApproximation a ha0 z hz ρ hρ hr n b else 0) atTop
      (𝓝 (if (t : ℝ≥0∞) < radialTime a b.1 z ρ then radialWeight a b.1 z ρ else 0)) := by
  by_cases hfin : radialTime a b.1 z ρ = ∞
  · have hg : radialWeight a b.1 z ρ = 0 := by rw [radialWeight,ite_eq_left hfin]
    simp only [hg,ite_self]
    have hc := radialApproximation_tendsto a ha ha0 z hz ρ hρ hr b
    rw [hg] at hc
    apply squeeze_zero _ _ hc
    · intro n
      split_ifs
      · exact (radialApproximation_bound a ha ha0 z hz ρ hρ hr n b).1
      · exact le_rfl
    · intro n
      split_ifs
      · exact le_rfl
      · exact (radialApproximation_bound a ha ha0 z hz ρ hρ hr n b).1
  · have he : ∀ᶠ n in atTop, (t < radialStop a ha0 z hz ρ hρ hr n b) ↔
        (t : ℝ≥0∞) < radialTime a b.1 z ρ := by
      filter_upwards [radialStop_eventually_eq a ha0 z hz ρ hρ hr b hfin] with n hn
      rw [← hn,ENNReal.coe_lt_coe]
    by_cases hlt : (t : ℝ≥0∞) < radialTime a b.1 z ρ
    · rw [ite_eq_left hlt]
      apply Filter.Tendsto.congr' _ (radialApproximation_tendsto a ha ha0 z hz ρ hρ hr b)
      filter_upwards [he] with n hn
      rw [ite_eq_left (hn.mpr hlt)]
    · rw [ite_eq_right hlt]
      apply Filter.Tendsto.congr' _ tendsto_const_nhds
      filter_upwards [he] with n hn
      rw [ite_eq_right (fun h => hlt (hn.mp h))]

lemma radialStop_stopping (a : ℝ) (ha : 0 < a) (z : ℂ) (hz : 0 < z.im)
    (ρ : ℝ) (hρ : 0 < ρ) (hr : ρ ≤ z.im) (n : ℕ) :
    IsStoppingTime rawFiltration (fun b => (radialStop a ha z hz ρ hρ hr n b : WithTop ℝ≥0)) := by
  let L := radialLocalization a ha z hz ρ (angleThreshold z n) hρ hr
    (angleThreshold_pos z hz n) (angleThreshold_initial z hz n)
  exact regionStop_stopping a L.ε L.hε z L.N ρ (angleThreshold z n) L.B

lemma stopped_event_lt {S T : ExactSLEGenerator.Driver → ℝ≥0}
    (hS : IsStoppingTime rawFiltration (fun b => (S b : WithTop ℝ≥0)))
    (hT : IsStoppingTime rawFiltration (fun b => (T b : WithTop ℝ≥0)))
    (U : Set ExactSLEGenerator.Driver) (hU : MeasurableSet[hS.measurableSpace] U) :
    MeasurableSet[(hS.min hT).measurableSpace] (U ∩ {b | S b < T b}) := by
  have he : U ∩ {b | S b < T b} =
      (U ∩ {b | (S b : WithTop ℝ≥0) ≤ T b}) \ {b | (S b : WithTop ℝ≥0) = T b} := by
    ext b
    simp only [Set.mem_inter_iff,Set.mem_ofPred_eq,Set.mem_sdiff,WithTop.coe_le_coe,WithTop.coe_eq_coe]
    exact ⟨fun h => ⟨⟨h.1,h.2.le⟩,h.2.ne⟩,fun h => ⟨h.1.1,lt_of_le_of_ne h.1.2 h.2⟩⟩
  rw [he]
  exact (hS.measurableSet_inter_le hT U hU).diff (hS.measurableSet_eq_stopping_time_min hT)

lemma radialStop_optional (W : Measure ExactSLEGenerator.Driver) [IsProbabilityMeasure W]
    (hW : IsBrownianReal (fun t (b : ExactSLEGenerator.Driver) => b.1 t) W)
    (a : ℝ) (_ha : 1/4 < a) (ha0 : 0 < a) (z : ℂ) (hz : 0 < z.im)
    (ρ : ℝ) (hρ : 0 < ρ) (hr : ρ ≤ z.im) (n : ℕ)
    (S : ExactSLEGenerator.Driver → ℝ≥0)
    (hS : IsStoppingTime rawFiltration (fun b => (S b : WithTop ℝ≥0)))
    (U : Set ExactSLEGenerator.Driver) (hU : MeasurableSet[hS.measurableSpace] U) :
    Integrable (fun b => if S b < radialStop a ha0 z hz ρ hρ hr n b then
      physicalGreen a (actualState a b.1 (S b) z) else 0) W ∧
    (∫ b in U, (if S b < radialStop a ha0 z hz ρ hρ hr n b then
        physicalGreen a (actualState a b.1 (S b) z) else 0) ∂W) =
      ∫ b in U, (if S b < radialStop a ha0 z hz ρ hρ hr n b then
        radialApproximation a ha0 z hz ρ hρ hr n b else 0) ∂W := by
  let L := radialLocalization a ha0 z hz ρ (angleThreshold z n) hρ hr
    (angleThreshold_pos z hz n) (angleThreshold_initial z hz n)
  let T := radialStop a ha0 z hz ρ hρ hr n
  have hT := radialStop_stopping a ha0 z hz ρ hρ hr n
  let C : Set ExactSLEGenerator.Driver := {b | S b < T b}
  have hC : MeasurableSet C := by
    exact (iSup_le fun t => rawFiltration.le t) _ (by
      simpa only [WithTop.coe_lt_coe] using measurableSet_lt hS.measurable_iSup hT.measurable_iSup)
  have hmin : IsStoppingTime rawFiltration (fun b => (min (S b) (T b) : WithTop ℝ≥0)) := by
    simpa only [WithTop.coe_min] using hS.min hT
  have hUC : MeasurableSet[hmin.measurableSpace] (U ∩ C) := by
    simpa only [← WithTop.coe_min] using stopped_event_lt hS hT U hU
  have hUC' : MeasurableSet (U ∩ C) := hmin.measurableSpace_le _ hUC
  let f := fun b => physicalGreen a (localState a L.ε L.hε z (min (S b) (T b)) b)
  have hsafe (b : ExactSLEGenerator.Driver) :
      L.ε ≤ Y (localState a L.ε L.hε z (min (S b) (T b)) b) ∧
      ‖localState a L.ε L.hε z (min (S b) (T b)) b‖ ≤ L.N := by
    have hs := regionStop_safe a L.ε L.hε z L.N ρ (angleThreshold z n) L.B L.initial b (min (S b) (T b)) (min_le_right (S b) (T b))
    exact ⟨hs.1,hs.2.1⟩
  have hf_eq : f = fun b => greenCutoff a L.ε L.N (localState a L.ε L.hε z (min (S b) (T b)) b) := by
    funext b
    exact ((greenCutoff_eq_near a L.ε L.hε L.N _ (hsafe b).2 (hsafe b).1).eq_of_nhds).symm
  have hfi : Integrable f W := by
    rw [hf_eq]
    have hm := (greenCutoff_smooth a L.ε L.hε L.N).continuous.measurable.comp
      (localState_stopped_measurable a L.ε L.hε z (fun b => min (S b) (T b)) hmin)
    obtain ⟨c,hc⟩ := (greenCutoff_compact a L.ε L.N).exists_bound_of_continuous
      (greenCutoff_smooth a L.ε L.hε L.N).continuous
    exact Integrable.of_bound hm.aestronglyMeasurable c (Eventually.of_forall fun b => hc _)
  have he (b : ExactSLEGenerator.Driver) (hb : b ∈ C) :
      physicalGreen a (actualState a b.1 (S b) z) = f b := by
    have hbt : S b < T b := hb
    dsimp only [f]
    rw [min_eq_left hbt.le]
    rw [(regionStop_actualState a L.ε L.hε z L.N ρ (angleThreshold z n) L.B L.initial b (S b) hbt.le).2]
  have hfun : (fun b => if S b < T b then physicalGreen a (actualState a b.1 (S b) z) else 0) =
      C.indicator f := by
    funext b
    by_cases hb : b ∈ C
    · rw [Set.indicator_of_mem hb,ite_eq_left (show S b < T b from hb),he b hb]
    · rw [Set.indicator_of_notMem hb,ite_eq_right (show ¬S b < T b from hb)]
  constructor
  · change Integrable (fun b => if S b < T b then physicalGreen a (actualState a b.1 (S b) z) else 0) W
    rw [hfun]
    exact hfi.indicator hC
  · change (∫ b in U, (if S b < T b then physicalGreen a (actualState a b.1 (S b) z) else 0) ∂W) = _
    rw [hfun,integral_indicator hC,Measure.restrict_restrict hC,Set.inter_comm C U]
    have ho := localGreen_optional W hW a L.ε ha0.ne' L.hε z L.N L.B
      (fun b => min (S b) (T b)) T hmin hT (fun b => min_le_right _ _) (fun b => regionStop_le a L.ε L.hε z L.N ρ (angleThreshold z n) L.B b)
      (fun b t ht => let hs := regionStop_safe a L.ε L.hε z L.N ρ (angleThreshold z n) L.B L.initial b t ht
        ⟨hs.1,hs.2.1⟩) (U ∩ C) hUC
    change (∫ b in U ∩ C, f b ∂W) = _
    rw [ho]
    have hfun' : (fun b => if S b < T b then radialApproximation a ha0 z hz ρ hρ hr n b else 0) =
        C.indicator (radialApproximation a ha0 z hz ρ hρ hr n) := rfl
    change _ = ∫ b in U, (if S b < T b then radialApproximation a ha0 z hz ρ hρ hr n b else 0) ∂W
    rw [hfun',integral_indicator hC,Measure.restrict_restrict hC,Set.inter_comm C U]
    rfl

lemma radialStop_before_bound (a : ℝ) (ha : 1/4 < a) (ha0 : 0 < a) (z : ℂ)
    (hz : 0 < z.im) (ρ : ℝ) (hρ : 0 < ρ) (hr : ρ ≤ z.im) (n : ℕ)
    (b : ExactSLEGenerator.Driver) (t : ℝ≥0) :
    ‖if t < radialStop a ha0 z hz ρ hρ hr n b then
      physicalGreen a (actualState a b.1 t z) else 0‖ ≤ Real.exp (-alpha a*Real.log ρ) := by
  split_ifs with ht
  · let L := radialLocalization a ha0 z hz ρ (angleThreshold z n) hρ hr
      (angleThreshold_pos z hz n) (angleThreshold_initial z hz n)
    rw [(regionStop_actualState a L.ε L.hε z L.N ρ (angleThreshold z n) L.B L.initial b t ht.le).2]
    have hs := regionStop_safe a L.ε L.hε z L.N ρ (angleThreshold z n) L.B L.initial b t ht.le
    rw [Real.norm_eq_abs,abs_of_pos (show 0 < physicalGreen a (localState a L.ε L.hε z t b) from Real.exp_pos _)]
    exact physicalGreen_bound a ρ ha hρ _ (L.hε.trans_le hs.1) hs.2.2.1
  · simpa only [norm_zero] using (Real.exp_pos (-alpha a*Real.log ρ)).le

lemma radialStop_before_measurable (a : ℝ) (ha0 : 0 < a) (z : ℂ)
    (hz : 0 < z.im) (ρ : ℝ) (hρ : 0 < ρ) (hr : ρ ≤ z.im) (n : ℕ)
    (S : ExactSLEGenerator.Driver → ℝ≥0)
    (hS : IsStoppingTime rawFiltration (fun b => (S b : WithTop ℝ≥0))) :
    Measurable[hS.measurableSpace] (fun b => if S b < radialStop a ha0 z hz ρ hρ hr n b then
      physicalGreen a (actualState a b.1 (S b) z) else 0) := by
  let L := radialLocalization a ha0 z hz ρ (angleThreshold z n) hρ hr
    (angleThreshold_pos z hz n) (angleThreshold_initial z hz n)
  let T := radialStop a ha0 z hz ρ hρ hr n
  have hT := radialStop_stopping a ha0 z hz ρ hρ hr n
  have hmin : IsStoppingTime rawFiltration (fun b => (min (S b) (T b) : WithTop ℝ≥0)) := by
    simpa only [WithTop.coe_min] using hS.min hT
  have hle : hmin.measurableSpace ≤ hS.measurableSpace :=
    hmin.measurableSpace_mono hS (fun b => WithTop.coe_le_coe.mpr (min_le_left _ _))
  have hC : MeasurableSet[hS.measurableSpace] {b | S b < T b} := by
    apply hle
    simpa only [Set.univ_inter,← WithTop.coe_min] using stopped_event_lt hS hT Set.univ MeasurableSet.univ
  have hA : StronglyAdapted rawFiltration (localState a L.ε L.hε z) :=
    fun t => (localState_adapted a L.ε L.hε z t).stronglyMeasurable
  have hv : Measurable[hS.measurableSpace] (fun b => localState a L.ε L.hε z (min (S b) (T b)) b) :=
    (measurable_stoppedValue (hA.isStronglyProgressive_of_continuous
      (localState_continuous a L.ε L.hε z)) hmin).mono hle le_rfl
  have hfun : (fun b => if S b < T b then physicalGreen a (actualState a b.1 (S b) z) else 0) =
      {b | S b < T b}.indicator
        (fun b => greenCutoff a L.ε L.N (localState a L.ε L.hε z (min (S b) (T b)) b)) := by
    funext b
    by_cases hb : S b < T b
    · rw [ite_eq_left hb,Set.indicator_of_mem (show b ∈ {b | S b < T b} from hb),min_eq_left hb.le]
      have hs := regionStop_safe a L.ε L.hε z L.N ρ (angleThreshold z n) L.B L.initial b (S b) hb.le
      rw [(regionStop_actualState a L.ε L.hε z L.N ρ (angleThreshold z n) L.B L.initial b (S b) hb.le).2]
      exact ((greenCutoff_eq_near a L.ε L.hε L.N _ hs.2.1 hs.1).eq_of_nhds).symm
    · rw [ite_eq_right hb,Set.indicator_of_notMem (show b ∉ {b | S b < T b} from hb)]
  change Measurable[hS.measurableSpace] (fun b => if S b < T b then physicalGreen a (actualState a b.1 (S b) z) else 0)
  rw [hfun]
  exact ((greenCutoff_smooth a L.ε L.hε L.N).continuous.measurable.comp hv).indicator hC

lemma radialRemaining_measurable (a : ℝ) (ha : 1/4 < a) (z : ℂ) (hz : 0 < z.im)
    (ρ : ℝ) (hρ : 0 < ρ) (hr : ρ ≤ z.im)
    (S : ExactSLEGenerator.Driver → ℝ≥0)
    (hS : IsStoppingTime rawFiltration (fun b => (S b : WithTop ℝ≥0))) :
    Measurable[hS.measurableSpace] (fun b => radialRemaining a b.1 z ρ (S b)) := by
  have ha0 : 0 < a := by linarith
  let : MeasurableSpace ExactSLEGenerator.Driver := hS.measurableSpace
  apply measurable_of_tendsto_metrizable
    (fun n => radialStop_before_measurable a ha0 z hz ρ hρ hr n S hS)
  exact tendsto_pi_nhds.mpr (fun b => radialStop_before_tendsto a ha ha0 z hz ρ hρ hr b (S b))

 

theorem radial_conditional_weight (W : Measure ExactSLEGenerator.Driver) [IsProbabilityMeasure W]
    (hW : IsBrownianReal (fun t (b : ExactSLEGenerator.Driver) => b.1 t) W)
    (a : ℝ) (ha : 1/4 < a) (z : ℂ) (hz : 0 < z.im)
    (ρ : ℝ) (hρ : 0 < ρ) (hr : ρ ≤ z.im)
    (S : ExactSLEGenerator.Driver → ℝ≥0)
    (hS : IsStoppingTime rawFiltration (fun b => (S b : WithTop ℝ≥0)))
    (U : Set ExactSLEGenerator.Driver) (hU : MeasurableSet[hS.measurableSpace] U) :
    Integrable (fun b => radialRemaining a b.1 z ρ (S b)) W ∧
    (∫ b in U, (if (S b : ℝ≥0∞) < radialTime a b.1 z ρ then radialWeight a b.1 z ρ else 0) ∂W) =
      ∫ b in U, radialRemaining a b.1 z ρ (S b) ∂W := by
  have ha0 : 0 < a := by linarith
  let F := fun n (b : ExactSLEGenerator.Driver) => if S b < radialStop a ha0 z hz ρ hρ hr n b
    then physicalGreen a (actualState a b.1 (S b) z) else 0
  let H := fun n (b : ExactSLEGenerator.Driver) => if S b < radialStop a ha0 z hz ρ hρ hr n b
    then radialApproximation a ha0 z hz ρ hρ hr n b else 0
  let G := fun b : ExactSLEGenerator.Driver => radialRemaining a b.1 z ρ (S b)
  let K := fun b : ExactSLEGenerator.Driver => if (S b : ℝ≥0∞) < radialTime a b.1 z ρ then radialWeight a b.1 z ρ else 0
  let C := Real.exp (-alpha a*Real.log ρ)
  have hFi (n : ℕ) : Integrable (F n) W :=
    (radialStop_optional W hW a ha ha0 z hz ρ hρ hr n S hS U hU).1
  have hHi (n : ℕ) : Integrable (H n) W := by
    have hT := radialStop_stopping a ha0 z hz ρ hρ hr n
    have hC : MeasurableSet {b | S b < radialStop a ha0 z hz ρ hρ hr n b} := by
      exact (iSup_le fun t => rawFiltration.le t) _ (by
        simpa only [WithTop.coe_lt_coe] using measurableSet_lt hS.measurable_iSup hT.measurable_iSup)
    exact (radialApproximation_mean W hW a ha0 z hz ρ hρ hr n).1.indicator hC
  have hFc (b : ExactSLEGenerator.Driver) : Tendsto (fun n => F n b) atTop (𝓝 (G b)) :=
    radialStop_before_tendsto a ha ha0 z hz ρ hρ hr b (S b)
  have hHc (b : ExactSLEGenerator.Driver) : Tendsto (fun n => H n b) atTop (𝓝 (K b)) :=
    radialStop_terminal_tendsto a ha ha0 z hz ρ hρ hr b (S b)
  have hFb (n : ℕ) (b : ExactSLEGenerator.Driver) : ‖F n b‖ ≤ C :=
    radialStop_before_bound a ha ha0 z hz ρ hρ hr n b (S b)
  have hHb (n : ℕ) (b : ExactSLEGenerator.Driver) : ‖H n b‖ ≤ C := by
    dsimp only [H]
    split_ifs
    · have h := radialApproximation_bound a ha ha0 z hz ρ hρ hr n b
      simpa only [Real.norm_eq_abs,abs_of_nonneg h.1] using h.2
    · exact (norm_zero.trans_le (Real.exp_pos _).le)
  have hGi : Integrable G W := Integrable.of_bound
    ((radialRemaining_measurable a ha z hz ρ hρ hr S hS).mono hS.measurableSpace_le le_rfl).aestronglyMeasurable C
    (Eventually.of_forall fun b => le_of_tendsto (hFc b).norm (Eventually.of_forall fun n => hFb n b))
  refine ⟨hGi,?_⟩
  have hFl := tendsto_integral_of_dominated_convergence (μ := W.restrict U) (fun _ => C)
    (fun n => (hFi n).aestronglyMeasurable.restrict) (integrable_const C)
    (fun n => Eventually.of_forall (hFb n)) (Eventually.of_forall hFc)
  have hHl := tendsto_integral_of_dominated_convergence (μ := W.restrict U) (fun _ => C)
    (fun n => (hHi n).aestronglyMeasurable.restrict) (integrable_const C)
    (fun n => Eventually.of_forall (hHb n)) (Eventually.of_forall hHc)
  have he : (fun n => ∫ b in U, F n b ∂W) = fun n => ∫ b in U, H n b ∂W :=
    funext fun n => (radialStop_optional W hW a ha ha0 z hz ρ hρ hr n S hS U hU).2
  rw [he] at hFl
  exact tendsto_nhds_unique hHl hFl

end ExactSLEGreen
namespace ExactSLEGreen
open ExactSLEGenerator ExactSLEMain
open scoped Classical
noncomputable def stoppedRadialRemaining (a : ℝ) (b : ℝ≥0 → ℝ) (z : ℂ) (ρ : ℝ) (t : ℝ≥0∞) : ℝ :=
  if t = ∞ then 0 else radialRemaining a b z ρ t.toNNReal

lemma radialRemaining_bound (a : ℝ) (ha : 1/4 < a) (z : ℂ) (hz : 0 < z.im)
    (ρ : ℝ) (hρ : 0 < ρ) (hr : ρ ≤ z.im) (b : ExactSLEGenerator.Driver) (t : ℝ≥0) :
    ‖radialRemaining a b.1 z ρ t‖ ≤ Real.exp (-alpha a*Real.log ρ) := by
  have ha0 : 0 < a := by linarith
  exact le_of_tendsto (radialStop_before_tendsto a ha ha0 z hz ρ hρ hr b t).norm
    (Eventually.of_forall fun n => radialStop_before_bound a ha ha0 z hz ρ hρ hr n b t)

lemma radialWeight_bound (a : ℝ) (ha : 1/4 < a) (z : ℂ) (hz : 0 < z.im)
    (ρ : ℝ) (hρ : 0 < ρ) (hr : ρ ≤ z.im) (b : ExactSLEGenerator.Driver) :
    0 ≤ radialWeight a b.1 z ρ ∧ radialWeight a b.1 z ρ ≤ Real.exp (-alpha a*Real.log ρ) := by
  have ha0 : 0 < a := by linarith
  have hc := radialApproximation_tendsto a ha ha0 z hz ρ hρ hr b
  exact ⟨ge_of_tendsto hc (Eventually.of_forall fun n => (radialApproximation_bound a ha ha0 z hz ρ hρ hr n b).1),
    le_of_tendsto hc (Eventually.of_forall fun n => (radialApproximation_bound a ha ha0 z hz ρ hρ hr n b).2)⟩

lemma radial_terminal_integrable (W : Measure ExactSLEGenerator.Driver) [IsProbabilityMeasure W]
    (hW : IsBrownianReal (fun t (b : ExactSLEGenerator.Driver) => b.1 t) W)
    (a : ℝ) (ha : 1/4 < a) (z : ℂ) (hz : 0 < z.im)
    (ρ : ℝ) (hρ : 0 < ρ) (hr : ρ ≤ z.im)
    (S : ExactSLEGenerator.Driver → ℝ≥0)
    (hS : IsStoppingTime rawFiltration (fun b => (S b : WithTop ℝ≥0))) :
    Integrable (fun b => if (S b : ℝ≥0∞) < radialTime a b.1 z ρ then radialWeight a b.1 z ρ else 0) W := by
  have ha0 : 0 < a := by linarith
  let H := fun n (b : ExactSLEGenerator.Driver) => if S b < radialStop a ha0 z hz ρ hρ hr n b
    then radialApproximation a ha0 z hz ρ hρ hr n b else 0
  have hHi (n : ℕ) : Integrable (H n) W := by
    have hT := radialStop_stopping a ha0 z hz ρ hρ hr n
    have hC : MeasurableSet {b | S b < radialStop a ha0 z hz ρ hρ hr n b} := by
      exact (iSup_le fun t => rawFiltration.le t) _ (by
        simpa only [WithTop.coe_lt_coe] using measurableSet_lt hS.measurable_iSup hT.measurable_iSup)
    exact (radialApproximation_mean W hW a ha0 z hz ρ hρ hr n).1.indicator hC
  apply Integrable.of_bound (aestronglyMeasurable_of_tendsto_ae atTop (fun n => (hHi n).aestronglyMeasurable)
    (Eventually.of_forall fun b => radialStop_terminal_tendsto a ha ha0 z hz ρ hρ hr b (S b)))
    (Real.exp (-alpha a*Real.log ρ))
  filter_upwards [] with b
  split_ifs
  · have h := radialWeight_bound a ha z hz ρ hρ hr b
    simpa only [Real.norm_eq_abs,abs_of_nonneg h.1] using h.2
  · simpa only [norm_zero] using (Real.exp_pos (-alpha a*Real.log ρ)).le

noncomputable def capTime (S : ExactSLEGenerator.Driver → ℝ≥0∞) (n : ℝ≥0) (b : ExactSLEGenerator.Driver) : ℝ≥0 :=
  (min (S b) (n : ℝ≥0∞)).toNNReal
lemma capTime_coe (S : ExactSLEGenerator.Driver → ℝ≥0∞) (n : ℝ≥0) (b : ExactSLEGenerator.Driver) :
    (capTime S n b : ℝ≥0∞) = min (S b) (n : ℝ≥0∞) :=
  ENNReal.coe_toNNReal (ne_of_lt (lt_of_le_of_lt (min_le_right _ _) ENNReal.coe_lt_top))
lemma capTime_stopping (S : ExactSLEGenerator.Driver → ℝ≥0∞) (hS : IsStoppingTime rawFiltration S)
    (n : ℝ≥0) : IsStoppingTime rawFiltration (fun b => (capTime S n b : WithTop ℝ≥0)) := by
  have heq : (fun b => (capTime S n b : WithTop ℝ≥0)) = fun b => min (S b) (n : ℝ≥0∞) := funext (capTime_coe S n)
  rw [heq]
  exact hS.min_const n
end ExactSLEGreen
end

end OAI
