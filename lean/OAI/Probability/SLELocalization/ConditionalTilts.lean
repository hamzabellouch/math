import Mathlib
import OAI.Probability.SLELocalization.AngularClock
import OAI.Probability.SLE.ClippedCoordinates
import OAI.Probability.SLE.IntegralLimits
import OAI.Probability.SLE.ItoIsometry
import OAI.Probability.SLE.StochasticIntegrals

namespace OAI


/-! Conformal localization and Brownian Predictable estimates. -/

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge.BrownianPredictable
open PredictableLimit

lemma indicator_difference_centered {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ}
    (hB : IsBrownianReal B P) (T : ℝ≥0)
    (A D : ℕ → ℕ → Ω → ℝ)
    (hA : ∀ n i, Measurable[pastSigma B (dyadicTime T n i)] (A n i))
    (hD : ∀ n i, Measurable[pastSigma B (dyadicTime T n i)] (D n i))
    (hA2 : ∀ n i, MemLp (A n i) 2 P) (hD2 : ∀ n i, MemLp (D n i) 2 P)
    (K : ℝ) (hK : 0 ≤ K)
    (hbA : ∀ n i, ∀ᵐ sample ∂P, |A n i sample| ≤ K)
    (hbD : ∀ n i, ∀ᵐ sample ∂P, |D n i sample| ≤ K)
    (θ : Ω → ℝ≥0∞)
    (hsupport : ∀ n i, ∀ᵐ sample ∂P,
      (dyadicTime T n i : ℝ≥0∞) < θ sample → A n i sample = D n i sample)
    (E : Set Ω) (hE : NullMeasurableSet E P)
    (hstop : ∀ t : ℝ≥0, ∃ S : Set Ω, MeasurableSet[pastSigma B t] S ∧
      S =ᵐ[P] (E ∩ {sample | θ sample ≤ (t : ℝ≥0∞)} : Set Ω))
    (YA YD : Ω → ℝ)
    (hlA : ∀ᵐ sample ∂P, Tendsto (fun n => dyadicDriverSum B T A n sample) atTop (𝓝 (YA sample)))
    (hlD : ∀ᵐ sample ∂P, Tendsto (fun n => dyadicDriverSum B T D n sample) atTop (𝓝 (YD sample))) :
    Integrable (E.indicator (fun sample => YA sample-YD sample)) P ∧
      (∫ sample, E.indicator (fun sample => YA sample-YD sample) sample ∂P) = 0 := by
  classical
  choose S hSm hSeq using hstop
  let Q := fun n i => (S (dyadicTime T n i)).indicator (fun sample => A n i sample-D n i sample)
  have hQm (n i : ℕ) : Measurable[pastSigma B (dyadicTime T n i)] (Q n i) :=
    ((hA n i).sub (hD n i)).indicator (hSm _)
  have heq (n i : ℕ) : Q n i =ᵐ[P] E.indicator (fun sample => A n i sample-D n i sample) := by
    filter_upwards [hSeq (dyadicTime T n i), hsupport n i] with sample he hs
    have he : sample ∈ S (dyadicTime T n i) ↔ sample ∈ E ∧ θ sample ≤ (dyadicTime T n i : ℝ≥0∞) := Iff.of_eq he
    by_cases hz : θ sample ≤ (dyadicTime T n i : ℝ≥0∞)
    · simp only [Q,Set.indicator_apply,he,hz,and_true]
    · have hh := hs (lt_of_not_ge hz)
      simp only [Q,Set.indicator_apply,hh,sub_self,ite_self]
  have hQ2 (n i : ℕ) : MemLp (Q n i) 2 P := by
    have hd := (hA2 n i).sub (hD2 n i)
    have hm : MemLp (E.indicator (fun sample => A n i sample-D n i sample)) 2 P :=
      hd.of_le (hd.aestronglyMeasurable.indicator₀ hE)
        (Filter.Eventually.of_forall (fun sample => norm_indicator_le_norm_self _ sample))
    exact hm.ae_eq (heq n i).symm
  have hQb (n i : ℕ) : ∀ᵐ sample ∂P, |Q n i sample| ≤ 2*K := by
    filter_upwards [hbA n i,hbD n i] with sample ha hd
    dsimp only [Q]
    rw [Set.indicator_apply]
    split_ifs
    · exact (abs_sub _ _).trans (by linarith)
    · simpa only [abs_zero] using (show 0 ≤ 2*K by positivity)
  have heall : ∀ᵐ sample ∂P, ∀ n i, Q n i sample = E.indicator (fun sample => A n i sample-D n i sample) sample :=
    ae_all_iff.2 (fun n => ae_all_iff.2 (heq n))
  apply limit_centered hB T Q hQm hQ2 (2*K) (by positivity) hQb _
  filter_upwards [heall,hlA,hlD] with sample he ha hd
  have heqsum (n : ℕ) : dyadicDriverSum B T Q n sample =
      E.indicator (fun sample => dyadicDriverSum B T A n sample-dyadicDriverSum B T D n sample) sample := by
    unfold dyadicDriverSum
    simp only [he,Set.indicator_apply]
    split_ifs <;> simp [sub_mul,Finset.sum_sub_distrib]
  simp only [heqsum,Set.indicator_apply]
  split_ifs
  · exact ha.sub hd
  · exact tendsto_const_nhds

end SLEExactGauge.BrownianPredictable

end

end

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge.GammaTwoRadius
open LoewnerCutoff LoewnerExit GammaField BrownianPredictable BrownianStopped BrownianIto TaylorMeshes
open scoped unitInterval
variable {ε : ℝ} (hε : 0 < ε)

def coeffAt (k : ℕ) (s : ℝ≥0) (l b η sdev : ℝ) (z : ℂ) (r ρ δ : ℝ)
    (q : C(I, ℝ) × ℝ) : ℝ := by
  classical
  exact if ∀ t ∈ Icc 0 (s:ℝ), 0 < deficit hε s.coe_nonneg q.1 z ρ δ t then
    iteratedDeriv k (field hε s.coe_nonneg l b η r sdev q.1 z s) q.2 else 0

lemma coeffAt_measurable (k : ℕ) (_hk : k = 1 ∨ k = 2) (s : ℝ≥0)
    (l b η sdev : ℝ) (hl : 0 < l) (hb : 0 < b) (hη : 0 < η) (z : ℂ) (r ρ δ : ℝ) :
    @Measurable (C(I, ℝ) × ℝ) ℝ (@Prod.instMeasurableSpace _ _ (borel _) inferInstance) _ (coeffAt hε k s l b η sdev z r ρ δ) := by
  let : MeasurableSpace C(I, ℝ) := borel _
  let : BorelSpace C(I, ℝ) := ⟨rfl⟩
  have hc : Continuous (fun q : C(I, ℝ) × ℝ =>
      iteratedDeriv k (field hε s.coe_nonneg l b η r sdev q.1 z s) q.2) := by
    have hp : Continuous (fun q : C(I, ℝ) × ℝ => ((q.1,(s:ℝ)),q.2)) :=
      (continuous_fst.prodMk continuous_const).prodMk continuous_snd
    have hc := (continuous_derivative hε s.coe_nonneg hl hb hη r sdev z k).comp hp
    dsimp only [Function.comp_def] at hc
    exact hc
  apply hc.measurable.ite _ measurable_const
  exact ((isOpen_positive_on hε s.coe_nonneg z ρ δ s).preimage continuous_fst).measurableSet

def rawCoeff {Ω : Type*} (k : ℕ) (B : ℝ≥0 → Ω → ℝ) (T s : ℝ≥0)
    (l b η sdev : ℝ) (z : ℂ) (r ρ δ : ℝ) (sample : Ω) : ℝ :=
  if s < T then coeffAt hε k s l b η sdev z r ρ δ (BrownianDriver.path B sdev s sample, B s sample) else 0

lemma rawCoeff_measurable_past {Ω : Type*} [MeasurableSpace Ω]
    (k : ℕ) (hk : k = 1 ∨ k = 2) (B : ℝ≥0 → Ω → ℝ) (T s : ℝ≥0)
    (l b η sdev : ℝ) (hl : 0 < l) (hb : 0 < b) (hη : 0 < η) (z : ℂ) (r ρ δ : ℝ) :
    Measurable[pastSigma B s] (rawCoeff hε k B T s l b η sdev z r ρ δ) := by
  classical
  let : MeasurableSpace C(I, ℝ) := borel _
  let : BorelSpace C(I, ℝ) := ⟨rfl⟩
  let : MeasurableSpace Ω := pastSigma B s
  unfold rawCoeff
  split_ifs
  · exact (coeffAt_measurable hε k hk s l b η sdev hl hb hη z r ρ δ).comp
      ((BrownianDriver.path_measurable_past B sdev s).prodMk (past_measurable_eval B (s := s) le_rfl))
  · exact measurable_const

lemma rawCoeff_aemeasurable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (k : ℕ) (hk : k = 1 ∨ k = 2) (T s : ℝ≥0)
    (l b η sdev : ℝ) (hl : 0 < l) (hb : 0 < b) (hη : 0 < η) (z : ℂ) (r ρ δ : ℝ) :
    AEMeasurable (rawCoeff hε k B T s l b η sdev z r ρ δ) P := by
  classical
  let : MeasurableSpace C(I, ℝ) := borel _
  let : BorelSpace C(I, ℝ) := ⟨rfl⟩
  unfold rawCoeff
  split_ifs
  · exact (coeffAt_measurable hε k hk s l b η sdev hl hb hη z r ρ δ).comp_aemeasurable
      ((BrownianDriver.path_aemeasurable hB sdev s).prodMk (hB.toIsPreBrownianReal.hasLaw_eval s).aemeasurable)
  · exact aemeasurable_const

lemma rawCoeff_eq {Ω : Type*} (k : ℕ) (B : ℝ≥0 → Ω → ℝ) (T s : ℝ≥0)
    (hT : 0 < (T:ℝ)) (l b η sdev : ℝ) (z : ℂ) (r ρ δ : ℝ) (sample : Ω)
    (hc : Continuous (fun t => B t sample)) :
    rawCoeff hε k B T s l b η sdev z r ρ δ sample =
      if (s:ℝ) < stop hε T.coe_nonneg (BrownianDriver.path B sdev T sample) z ρ δ then
        iteratedDeriv k (field hε T.coe_nonneg l b η r sdev (BrownianDriver.path B sdev T sample) z s) (B s sample) else 0 := by
  classical
  by_cases hsT : s < T
  · have he := BrownianDriver.prefix_eq B sdev s T sample hc hsT.le
    have hf := field_prefix_eq hε s.coe_nonneg T.coe_nonneg hsT.le
      (BrownianDriver.path B sdev s sample) (BrownianDriver.path B sdev T sample) z l b η r sdev he
      ⟨s.coe_nonneg, le_rfl⟩
    have hd := deficit_prefix_eq hε s.coe_nonneg T.coe_nonneg hsT.le
      (BrownianDriver.path B sdev s sample) (BrownianDriver.path B sdev T sample) z ρ δ he
    have hi : (∀ t ∈ Icc 0 (s:ℝ), 0 < deficit hε s.coe_nonneg (BrownianDriver.path B sdev s sample) z ρ δ t) ↔
        (s:ℝ) < stop hε T.coe_nonneg (BrownianDriver.path B sdev T sample) z ρ δ := by
      rw [lt_stop_iff hε T.coe_nonneg hT _ z ρ δ ⟨s.coe_nonneg,hsT⟩]
      exact forall₂_congr (fun t ht => by rw [hd ht])
    simp only [rawCoeff, ite_eq_left hsT, coeffAt, hi, hf]
  · have hstop : ¬ (s:ℝ) < stop hε T.coe_nonneg (BrownianDriver.path B sdev T sample) z ρ δ :=
      not_lt_of_ge ((stop_bounds hε T.coe_nonneg _ z ρ δ).2.trans (not_lt.1 hsT))
    simp only [rawCoeff, ite_eq_right hsT, ite_eq_right hstop]

lemma rawCoeff_stoppedCoeff_ae {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) (k : ℕ) (T : ℝ≥0)
    (hT : 0 < (T:ℝ)) (l b η sdev : ℝ) (z : ℂ) (r ρ δ : ℝ) (n i : ℕ) :
    rawCoeff hε k B T (dyadicTime T n i) l b η sdev z r ρ δ =ᵐ[P]
      stoppedCoeff k B T
        (fun sample => stop hε T.coe_nonneg (BrownianDriver.path B sdev T sample) z ρ δ)
        (fun sample => field hε T.coe_nonneg l b η r sdev (BrownianDriver.path B sdev T sample) z) n i := by
  filter_upwards [hB.cont] with sample hc
  rw [rawCoeff_eq hε k B T _ hT l b η sdev z r ρ δ sample hc]
  simp only [stoppedCoeff, coe_dyadicTime]

end SLEExactGauge.GammaTwoRadius

end

end

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal unitInterval
namespace SLEExactGauge.LoewnerExit
open LoewnerCutoff

lemma stop_antitone_radius {ε T : ℝ} (hε : 0 < ε) (hT : 0 < T)
    (U : C(I, ℝ)) (z : ℂ) (ρ ρ₂ δ : ℝ) (hρρ₂ : ρ ≤ ρ₂) :
    stop hε hT.le U z ρ₂ δ ≤ stop hε hT.le U z ρ δ := by
  by_contra hn
  have hlt : stop hε hT.le U z ρ δ < stop hε hT.le U z ρ₂ δ := lt_of_not_ge hn
  have hp := (deficit_pos_iff hε hT.le U z ρ₂ δ _).1
    (positive_before hε hT.le hT U z ρ₂ δ (stop_bounds hε hT.le U z ρ δ).1 hlt)
  have hpos : 0 < deficit hε hT.le U z ρ δ (stop hε hT.le U z ρ δ) :=
    (deficit_pos_iff hε hT.le U z ρ δ _).2 ⟨hρρ₂.trans_lt hp.1,hp.2⟩
  exact (not_lt_of_ge (nonpos_at_of_lt hε hT.le hT U z ρ δ
    (hlt.trans_le (stop_bounds hε hT.le U z ρ₂ δ).2))) hpos

end SLEExactGauge.LoewnerExit

end

end

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal unitInterval
namespace SLEExactGauge.FiniteTilt.Cutoff
open LoewnerCutoff LoewnerField LoewnerExit LoewnerLocalized
variable {z : ℂ} {u v : ℝ}

def retarget (C : Cutoff z v) (hz : z ∈ halfPlane) (huv : u ≤ v) : Cutoff z u where
  angle := C.angle
  angle_pos := C.angle_pos
  angle_initial := C.angle_initial
  height := C.height
  height_pos := C.height_pos
  horizon := C.horizon
  horizon_pos := C.horizon_pos
  height_small := C.height_small.trans_le (by
    apply mul_le_mul_of_nonneg_left _ hz.le
    apply Real.exp_le_exp.mpr
    exact div_le_div_of_nonneg_right (neg_le_neg huv) (by positivity))
  time_large := lt_of_le_of_lt (by
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_right huv (sq_nonneg _)) C.time_large

lemma retarget_stop_le (C : Cutoff z v) (hz : z ∈ halfPlane) (huv : u ≤ v)
    {Ω : Type*} (κ : ℝ) (B : ℝ≥0 → Ω → ℝ) (sample : Ω) :
    (C.retarget hz huv).stopTime κ B sample ≤ C.stopTime κ B sample := by
  apply stop_antitone_radius C.height_pos C.horizon_pos
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (neg_le_neg huv)) (by exact mul_nonneg (by norm_num) hz.le)

lemma retarget_has_hit_of_lt (C : Cutoff z v) (hz : z ∈ halfPlane)
    (hu : 0 < u) (huv : u ≤ v) {Ω : Type*} (κ : ℝ) (B : ℝ≥0 → Ω → ℝ) (sample : Ω)
    {γ : ℝ → ℂ} {g f : ℝ → ℂ → ℂ}
    (h : IsLoewnerTraceUsing (fun t => Real.sqrt κ*B t.toNNReal sample) γ g f)
    (hc : Continuous (fun t => B t sample)) (hb0 : B 0 sample = 0)
    (hlt : (C.retarget hz huv).stopTime κ B sample < C.stopTime κ B sample) :
    firstLiveRadiusStop γ g z u = ENNReal.ofReal ((C.retarget hz huv).stopTime κ B sample) := by
  let D := C.retarget hz huv
  have hd := D.initial_deficit_brownian κ B sample hz hu hc hb0
  have ht := D.bounds κ B sample
  have hR : loewnerRadius g (D.stopTime κ B sample) z = (2*z.im)*Real.exp (-u) := by
    rcases D.source_terminal κ B sample h hz hu hc hb0 with hr | hs
    · exact hr
    · have hp := (deficit_pos_iff C.height_pos C.horizon.coe_nonneg (C.paths κ B sample)
        z ((2*z.im)*Real.exp (-v)) C.angle (D.stopTime κ B sample)).1
        (positive_before C.height_pos C.horizon.coe_nonneg C.horizon_pos (C.paths κ B sample)
          z ((2*z.im)*Real.exp (-v)) C.angle ht.1 hlt)
      have he := D.source_sine κ B sample h hz hu hc hb0
      have hi : C.angle < loewnerAngleSine κ (fun t => B t sample) g (D.stopTime κ B sample) z := by
        rw [← he]
        exact hp.2.2
      exact False.elim ((ne_of_gt hi) hs)
  have hh := h.firstLiveRadiusStop_eq
    ((continuous_const.mul (hc.comp continuous_real_toNNReal)).continuousOn)
    (t := ⟨D.stopTime κ B sample,ht.1⟩) (D.source_live κ B sample h hz hu hc hb0) hR
  rw [ENNReal.ofReal_eq_coe_nnreal ht.1]
  exact hh

lemma stopTime_zero (C : Cutoff z 0) {Ω : Type*} (κ : ℝ)
    (B : ℝ≥0 → Ω → ℝ) (sample : Ω) : C.stopTime κ B sample = 0 := by
  apply le_antisymm _ (C.bounds κ B sample).1
  by_contra hn
  have hp := (deficit_pos_iff C.height_pos C.horizon.coe_nonneg (C.paths κ B sample)
    z ((2*z.im)*Real.exp (-0)) C.angle 0).1
    (positive_before C.height_pos C.horizon.coe_nonneg C.horizon_pos (C.paths κ B sample)
      z ((2*z.im)*Real.exp (-0)) C.angle le_rfl (lt_of_not_ge hn))
  simpa only [LoewnerExit.radius,position_initial,logDerivative_initial,neg_zero,
    Real.exp_zero,mul_one,div_one,lt_self_iff_false] using hp.1

lemma value_zero (C : Cutoff z 0) (hz : z ∈ halfPlane) {Ω : Type*} (κ : ℝ)
    (B : ℝ≥0 → Ω → ℝ) (sample : Ω) (hb0 : B 0 sample = 0) :
    ENNReal.ofReal (C.value κ B sample) =
      ENNReal.ofReal ((2*z.im)^(-codimension κ)*(z.im/‖z‖)^(8/κ-1)) := by
  unfold value
  rw [C.stopTime_zero,Real.toNNReal_zero,hb0,field_initial C.height_pos C.horizon.coe_nonneg
    (1-κ/8) (8/κ-1) (Real.sqrt κ) (C.paths κ B sample) z (C.height_initial hz le_rfl).le,
    green_initial κ hz]

end SLEExactGauge.FiniteTilt.Cutoff

end

end

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal unitInterval
namespace SLEExactGauge.BrownianLocal.LocalRegular

lemma mono {F V : ℝ → ℝ → ℝ} {b : ℝ → ℝ} {S T : ℝ}
    (h : BrownianLocal.LocalRegular F V b T) (hST : S ≤ T) :
    BrownianLocal.LocalRegular F V b S where
  smooth := h.smooth
  third_cont := h.third_cont.mono (Set.prod_mono (Icc_subset_Icc_right hST) Subset.rfl)
  time_cont := fun x => (h.time_cont x).mono (Icc_subset_Icc_right hST)
  time_deriv := fun t ht => h.time_deriv t ⟨ht.1,ht.2.trans_le hST⟩
  drift_cont := h.drift_cont.mono (Set.prod_mono (Icc_subset_Icc_right hST) (Icc_subset_Icc_right hST))
  second_cont := h.second_cont.mono (Icc_subset_Icc_right hST)

end SLEExactGauge.BrownianLocal.LocalRegular

end

end

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal unitInterval
namespace SLEExactGauge.FiniteTilt.Cutoff
open GammaField GammaTwoRadius BrownianPredictable BrownianStopped BrownianIto TaylorMeshes PredictableLimit
variable {z : ℂ} {v : ℝ} (C : Cutoff z v)

def targetField {Ω : Type*} (η κ : ℝ) (B : ℝ≥0 → Ω → ℝ) (sample : Ω) : ℝ → ℝ → ℝ :=
  GammaField.field C.height_pos C.horizon.coe_nonneg (κ/2) ((8/κ-1)/2) η
    ((2*z.im)*Real.exp (-v)) (Real.sqrt κ) (C.paths κ B sample) z

def targetDrift {Ω : Type*} (η κ : ℝ) (B : ℝ≥0 → Ω → ℝ) (sample : Ω) : ℝ → ℝ → ℝ :=
  GammaField.drift C.height_pos C.horizon.coe_nonneg (κ/2) ((8/κ-1)/2) η
    ((2*z.im)*Real.exp (-v)) (Real.sqrt κ) (C.paths κ B sample) z

def targetCoeff {Ω : Type*} (k : ℕ) (η κ : ℝ) (B : ℝ≥0 → Ω → ℝ) (w : ℝ) (n i : ℕ) : Ω → ℝ :=
  GammaTwoRadius.rawCoeff C.height_pos k B C.horizon (dyadicTime C.horizon n i)
    (κ/2) ((8/κ-1)/2) η (Real.sqrt κ) z ((2*z.im)*Real.exp (-v)) ((2*z.im)*Real.exp (-w)) C.angle

def targetRemainder {Ω : Type*} (η κ : ℝ) (B : ℝ≥0 → Ω → ℝ) (t : Ω → ℝ) (sample : Ω) : ℝ :=
  C.targetField η κ B sample (t sample) (B (t sample).toNNReal sample) -
    C.targetField η κ B sample 0 (B 0 sample) -
    (∫ s in (0:ℝ)..(t sample), C.targetDrift η κ B sample s (B s.toNNReal sample)) -
    (1/2:ℝ)*∫ s in (0:ℝ)..(t sample),
      iteratedDeriv 2 (C.targetField η κ B sample s) (B s.toNNReal sample)

lemma targetCoeff_eq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) (k : ℕ) (η κ : ℝ)
    (hz : z ∈ halfPlane) (w : ℝ) (hwv : w ≤ v) (n i : ℕ) :
    C.targetCoeff k η κ B w n i =ᵐ[P]
      stoppedCoeff k B C.horizon ((C.retarget hz hwv).stopTime κ B) (C.targetField η κ B) n i :=
  rawCoeff_stoppedCoeff_ae C.height_pos hB k C.horizon C.horizon_pos (κ/2) ((8/κ-1)/2)
    η (Real.sqrt κ) z _ _ C.angle n i

lemma targetCoeff_measurable {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (k : ℕ) (hk : k = 1 ∨ k = 2) (η κ : ℝ)
    (hκ : 0 < κ ∧ κ < 8) (hη : 0 < η) (w : ℝ) (n i : ℕ) :
    Measurable[pastSigma B (dyadicTime C.horizon n i)] (C.targetCoeff k η κ B w n i) := by
  have hl : 0 < κ/2 := by linarith [hκ.1]
  have hb : 0 < (8/κ-1)/2 := by
    have hh : 1 < 8/κ := (lt_div_iff₀ hκ.1).2 (by simpa using hκ.2)
    linarith
  exact rawCoeff_measurable_past C.height_pos k hk B C.horizon _ _ _ _ _ hl hb hη z _ _ C.angle

lemma targetCoeff_aemeasurable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) (k : ℕ) (hk : k = 1 ∨ k = 2) (η κ : ℝ)
    (hκ : 0 < κ ∧ κ < 8) (hη : 0 < η) (w : ℝ) (n i : ℕ) :
    AEMeasurable (C.targetCoeff k η κ B w n i) P := by
  have hl : 0 < κ/2 := by linarith [hκ.1]
  have hb : 0 < (8/κ-1)/2 := by
    have hh : 1 < 8/κ := (lt_div_iff₀ hκ.1).2 (by simpa using hκ.2)
    linarith
  exact rawCoeff_aemeasurable C.height_pos hB k hk C.horizon _ _ _ _ _ hl hb hη z _ _ C.angle

lemma targetCoeff_bound {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) (k : ℕ) (η κ : ℝ)
    (hκ : 0 < κ ∧ κ < 8) (hη : 0 < η) (hz : z ∈ halfPlane) (hv : 0 < v)
    (γ : Ω → ℝ → ℂ) (g f : Ω → ℝ → ℂ → ℂ)
    (hmaps : ∀ᵐ sample ∂P, IsLoewnerTraceUsing
      (fun t => Real.sqrt κ*B t.toNNReal sample) (γ sample) (g sample) (f sample)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ w, w ≤ v → ∀ n i,
      ∀ᵐ sample ∂P, |C.targetCoeff k η κ B w n i sample| ≤ K := by
  have hl : 0 < κ/2 := by linarith [hκ.1]
  have hb : 0 < (8/κ-1)/2 := by
    have hh : 1 < 8/κ := (lt_div_iff₀ hκ.1).2 (by simpa using hκ.2)
    linarith
  obtain ⟨K,hK,hKb⟩ := coefficient_bound C.height_pos C.horizon.coe_nonneg hl hb hη
    ((2*z.im)*Real.exp (-v)) (Real.sqrt κ) (η+v) (1/C.angle) z k
  refine ⟨K,hK,?_⟩
  intro w hwv n i
  filter_upwards [C.targetCoeff_eq hB k η κ hz w hwv n i,hmaps,hB.cont,
    hB.toIsPreBrownianReal.eval_zero_ae_eq_zero] with sample he hm hc hb0
  rw [he]
  unfold stoppedCoeff
  split_ifs with hh
  · have ht : mesh C.horizon n i ∈ Icc 0 (C.stopTime κ B sample) :=
      ⟨by unfold mesh; positivity,hh.le.trans (C.retarget_stop_le hz hwv κ B sample)⟩
    exact hKb (C.paths κ B sample) _ _ (C.remaining_upper κ B sample hm hz hv hc hb0 η ht)
      (by simpa only [mesh_toNNReal] using C.ratio_upper κ B sample hz hv hc hb0 ht)
  · simpa only [abs_zero] using hK

lemma target_sum_tendsto {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) (η κ : ℝ)
    (hκ : 0 < κ ∧ κ < 8) (hη : 0 < η) (hz : z ∈ halfPlane) (hv : 0 < v)
    (γ : Ω → ℝ → ℂ) (g f : Ω → ℝ → ℂ → ℂ)
    (hmaps : ∀ᵐ sample ∂P, IsLoewnerTraceUsing
      (fun t => Real.sqrt κ*B t.toNNReal sample) (γ sample) (g sample) (f sample))
    (w : ℝ) (hwv : w ≤ v) :
    ∀ᵐ sample ∂P, Tendsto (fun n => dyadicDriverSum B C.horizon (C.targetCoeff 1 η κ B w) n sample)
      atTop (𝓝 (C.targetRemainder η κ B ((C.retarget hz hwv).stopTime κ B) sample)) := by
  have hl : 0 < κ/2 := by linarith [hκ.1]
  have hb : 0 < (8/κ-1)/2 := by
    have hh : 1 < 8/κ := (lt_div_iff₀ hκ.1).2 (by simpa using hκ.2)
    linarith
  let D := C.retarget hz hwv
  have hreg : ∀ᵐ sample ∂P, BrownianLocal.LocalRegular (C.targetField η κ B sample)
      (C.targetDrift η κ B sample) (fun t => B t.toNNReal sample) (D.stopTime κ B sample) := by
    filter_upwards [hB.cont] with sample hc
    have hρ : 0 < (2*z.im)*Real.exp (-v) := by have hy : 0 < z.im := hz; positivity
    exact (regular C.height_pos C.horizon.coe_nonneg hl hb hη hρ C.horizon_pos
      (Real.sqrt κ) (C.paths κ B sample) z C.angle _ (hc.comp continuous_real_toNNReal)).mono
      (C.retarget_stop_le hz hwv κ B sample)
  obtain ⟨K₁,hK₁,hb₁⟩ := C.targetCoeff_bound hB 1 η κ hκ hη hz hv γ g f hmaps
  obtain ⟨K₂,hK₂,hb₂⟩ := C.targetCoeff_bound hB 2 η κ hκ hη hz hv γ g f hmaps
  have hMem : ∀ n i, MemLp (C.targetCoeff 2 η κ B w n i) 2 P := by
    intro n i
    apply MemLp.of_bound (C.targetCoeff_aemeasurable hB 2 (Or.inr rfl) η κ hκ hη w n i).aestronglyMeasurable K₂
    simpa only [Real.norm_eq_abs] using hb₂ w hwv n i
  have hi := BrownianLocal.stopped_fieldSum_tendsto_ae hB C.horizon (D.stopTime κ B)
    (C.targetField η κ B) (C.targetDrift η κ B)
    (Filter.Eventually.of_forall (fun sample => D.bounds κ B sample)) hreg
    (C.targetCoeff 2 η κ B w) (C.targetCoeff_eq hB 2 η κ hz w hwv)
    (C.targetCoeff_measurable B 2 (Or.inr rfl) η κ hκ hη w) hMem
    K₂ hK₂ (fun n i => by
      filter_upwards [C.targetCoeff_eq hB 2 η κ hz w hwv n i,hb₂ w hwv n i] with sample he hh
      rwa [← he])
    K₁ hK₁ (fun n i => by
      filter_upwards [C.targetCoeff_eq hB 1 η κ hz w hwv n i,hb₁ w hwv n i] with sample he hh
      rwa [← he])
  have heall : ∀ᵐ sample ∂P, ∀ n i, C.targetCoeff 1 η κ B w n i sample =
      stoppedCoeff 1 B C.horizon (D.stopTime κ B) (C.targetField η κ B) n i sample :=
    ae_all_iff.2 (fun n => ae_all_iff.2 (C.targetCoeff_eq hB 1 η κ hz w hwv n))
  filter_upwards [hi,heall] with sample hi he
  simpa only [targetRemainder,dyadicDriverSum,he] using hi

end SLEExactGauge.FiniteTilt.Cutoff

end

end

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal unitInterval
namespace SLEExactGauge.GammaField
open LoewnerCutoff LoewnerExit

lemma integral_drift_nonpos_from {ε T κ η : ℝ} (hε : 0 < ε) (hT : 0 ≤ T)
    (hκ : 0 < κ ∧ κ < 8) (hη : 0 < η) (ρ : ℝ)
    (hTp : 0 < T) (U : C(I, ℝ)) (z : ℂ) (δ : ℝ) (B : ℝ → ℝ) (hB : Continuous B)
    (hU : ∀ s ∈ Icc 0 T, extendDriver T U s = Real.sqrt κ*B s)
    {a : ℝ} (ha : 0 ≤ a) (haτ : a ≤ stop hε hT U z ρ δ) :
    (∫ t in a..(stop hε hT U z ρ δ), drift hε hT (κ/2) ((8/κ-1)/2) η ρ (Real.sqrt κ) U z t (B t)) +
    (1/2:ℝ)*∫ t in a..(stop hε hT U z ρ δ),
      iteratedDeriv 2 (field hε hT (κ/2) ((8/κ-1)/2) η ρ (Real.sqrt κ) U z t) (B t) ≤ 0 := by
  have hl : 0 < κ/2 := by linarith [hκ.1]
  have hb : 0 < (8/κ-1)/2 := by
    have hh : 1 < 8/κ := (lt_div_iff₀ hκ.1).2 (by simpa using hκ.2)
    linarith
  have hm : Continuous (fun t : ℝ => ((U,t),B t)) :=
    (continuous_const.prodMk continuous_id).prodMk hB
  have hv := (continuous_drift hε hT hl hb hη ρ (Real.sqrt κ) z).comp hm
  have hc := (continuous_derivative hε hT hl hb hη ρ (Real.sqrt κ) z 2).comp hm
  have hiV := hv.intervalIntegrable (μ := volume) a (stop hε hT U z ρ δ)
  have hiC := hc.intervalIntegrable (μ := volume) a (stop hε hT U z ρ δ)
  dsimp only [Function.comp_def] at hiV hiC
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add hiV (hiC.const_mul (1/2:ℝ))]
  rw [intervalIntegral.integral_of_le haτ]
  apply integral_nonpos_of_ae
  have hne : ∀ᵐ t : ℝ ∂volume, t ≠ stop hε hT U z ρ δ := by simp [ae_iff]
  filter_upwards [ae_restrict_mem measurableSet_Ioc,ae_restrict_of_ae hne] with t ht he
  have hlt : t < stop hε hT U z ρ δ := lt_of_le_of_ne ht.2 he
  have hh := (deficit_pos_iff hε hT U z ρ δ t).1
    (positive_before hε hT hTp U z ρ δ (ha.trans ht.1.le) hlt)
  exact drift_nonpos hε hT hκ hη ρ U z t (B t) hh.2.1.le
    (hU t ⟨ha.trans ht.1.le,ht.2.trans (stop_bounds hε hT U z ρ δ).2⟩)

end SLEExactGauge.GammaField

end

end

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal unitInterval
namespace SLEExactGauge.FiniteTilt.Cutoff
open GammaField LoewnerCutoff LoewnerExit
variable {z : ℂ} {v : ℝ} (C : Cutoff z v)

def targetValue {Ω : Type*} (hz : z ∈ halfPlane) {w : ℝ} (hwv : w ≤ v)
    (η κ : ℝ) (B : ℝ≥0 → Ω → ℝ) (sample : Ω) : ℝ :=
  C.targetField η κ B sample ((C.retarget hz hwv).stopTime κ B sample)
    (B ((C.retarget hz hwv).stopTime κ B sample).toNNReal sample)

lemma targetValue_nonneg {Ω : Type*} (hz : z ∈ halfPlane) {w : ℝ} (hwv : w ≤ v)
    (η κ : ℝ) (hκ : 0 < κ ∧ κ < 8) (hη : 0 < η) (B : ℝ≥0 → Ω → ℝ) (sample : Ω) :
    0 ≤ C.targetValue hz hwv η κ B sample := by
  have hl : 0 < κ/2 := by linarith [hκ.1]
  have hb : 0 < (8/κ-1)/2 := by
    have hh : 1 < 8/κ := (lt_div_iff₀ hκ.1).2 (by simpa using hκ.2)
    linarith
  exact field_nonneg C.height_pos C.horizon.coe_nonneg hl hb hη _ _ _ _ _ _

lemma targetValue_aemeasurable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) (hz : z ∈ halfPlane) {w : ℝ} (hwv : w ≤ v)
    (η κ : ℝ) (hκ : 0 < κ ∧ κ < 8) (hη : 0 < η) :
    AEMeasurable (C.targetValue hz hwv η κ B) P := by
  let : MeasurableSpace C(I, ℝ) := borel _
  let : BorelSpace C(I, ℝ) := ⟨rfl⟩
  have hl : 0 < κ/2 := by linarith [hκ.1]
  have hb : 0 < (8/κ-1)/2 := by
    have hh : 1 < 8/κ := (lt_div_iff₀ hκ.1).2 (by simpa using hκ.2)
    linarith
  let τ := fun U : C(I, ℝ) => stop C.height_pos C.horizon.coe_nonneg U z ((2*z.im)*Real.exp (-w)) C.angle
  have hτ : Measurable τ := measurable_stop C.height_pos C.horizon.coe_nonneg C.horizon_pos z _ C.angle
  have hm := ((continuous_actualField C.height_pos C.horizon hl hb hη
    ((2*z.im)*Real.exp (-v)) (Real.sqrt κ) z).measurable.comp (measurable_id.prodMk hτ)).comp_aemeasurable
    (BrownianDriver.path_aemeasurable hB (Real.sqrt κ) C.horizon)
  apply hm.congr
  filter_upwards [hB.cont] with sample hc
  change GammaField.field C.height_pos C.horizon.coe_nonneg (κ/2) ((8/κ-1)/2) η
    ((2*z.im)*Real.exp (-v)) (Real.sqrt κ) (C.paths κ B sample) z
    ((C.retarget hz hwv).stopTime κ B sample)
    (LoewnerCutoff.extendDriver C.horizon (C.paths κ B sample)
      ((C.retarget hz hwv).stopTime κ B sample) / Real.sqrt κ) = _
  rw [C.path_eq κ B sample hc ((C.retarget hz hwv).bounds κ B sample),mul_div_cancel_left₀ _ (Real.sqrt_pos.2 hκ.1).ne']
  rfl

lemma target_difference_le_remainder {Ω : Type*} (hz : z ∈ halfPlane) {w : ℝ} (hwv : w ≤ v)
    (η κ : ℝ) (hκ : 0 < κ ∧ κ < 8) (hη : 0 < η) (B : ℝ≥0 → Ω → ℝ) (sample : Ω)
    (hc : Continuous (fun t => B t sample)) :
    C.barrier η κ B sample-C.targetValue hz hwv η κ B sample ≤
      C.targetRemainder η κ B (C.stopTime κ B) sample -
      C.targetRemainder η κ B ((C.retarget hz hwv).stopTime κ B) sample := by
  let D := C.retarget hz hwv
  have hl : 0 < κ/2 := by linarith [hκ.1]
  have hb : 0 < (8/κ-1)/2 := by
    have hh : 1 < 8/κ := (lt_div_iff₀ hκ.1).2 (by simpa using hκ.2)
    linarith
  have hm : Continuous (fun t : ℝ => ((C.paths κ B sample,t),B t.toNNReal sample)) :=
    (continuous_const.prodMk continuous_id).prodMk (hc.comp continuous_real_toNNReal)
  have hd := (continuous_drift C.height_pos C.horizon.coe_nonneg hl hb hη
    ((2*z.im)*Real.exp (-v)) (Real.sqrt κ) z).comp hm
  have h2 := (continuous_derivative C.height_pos C.horizon.coe_nonneg hl hb hη
    ((2*z.im)*Real.exp (-v)) (Real.sqrt κ) z 2).comp hm
  have hid := intervalIntegral.integral_add_adjacent_intervals
    (hd.intervalIntegrable (μ := volume) 0 (D.stopTime κ B sample))
    (hd.intervalIntegrable (μ := volume) (D.stopTime κ B sample) (C.stopTime κ B sample))
  have hi2 := intervalIntegral.integral_add_adjacent_intervals
    (h2.intervalIntegrable (μ := volume) 0 (D.stopTime κ B sample))
    (h2.intervalIntegrable (μ := volume) (D.stopTime κ B sample) (C.stopTime κ B sample))
  have hn := integral_drift_nonpos_from C.height_pos C.horizon.coe_nonneg hκ hη
    ((2*z.im)*Real.exp (-v)) C.horizon_pos (C.paths κ B sample) z C.angle
    (fun t => B t.toNNReal sample) (hc.comp continuous_real_toNNReal)
    (C.path_eq κ B sample hc) (D.bounds κ B sample).1 (C.retarget_stop_le hz hwv κ B sample)
  dsimp only [Function.comp_def] at hid hi2
  unfold targetRemainder targetValue targetField targetDrift barrier
  dsimp only [D, stopTime] at hid hi2 hn ⊢
  linarith only [hn,hid,hi2]

end SLEExactGauge.FiniteTilt.Cutoff

end

end

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge.AngularBarrier

lemma value_decay_from {l b t₀ : ℝ} (hl : 0 < l) (hb : 0 < b) (ht₀ : 0 < t₀) :
    ∃ K : ℝ, 0 < K ∧ ∀ t q : ℝ, t₀ ≤ t → 0 ≤ q →
      value l b t q ≤ K*Real.exp (-(l*b/2)*t)*q^b := by
  let c := (1-Real.exp (-l*t₀))/(2*(b+1))
  have hc : 0 < c := div_pos (sub_pos.2 (Real.exp_lt_one_iff.2 (by nlinarith))) (by positivity)
  have hg : 0 < Real.Gamma b := Real.Gamma_pos_of_pos hb
  refine ⟨1/(b*Real.Gamma b*c^b), by positivity, ?_⟩
  intro t q ht hq
  have ht0 : 0 < t := ht₀.trans_le ht
  have ha := scale_pos hl hb ht0
  have hlower : c*Real.exp (l*t) ≤ scale l b t := by
    have hh : 1 ≤ Real.exp (l*t)*Real.exp (-l*t₀) := by
      rw [← Real.exp_add]
      exact Real.one_le_exp_iff.2 (by nlinarith)
    dsimp only [c,scale]
    apply (le_div_iff₀ (by positivity : 0 < 2*(b+1))).2
    have heq : ((1-Real.exp (-l*t₀))/(2*(b+1))*Real.exp (l*t))*(2*(b+1)) =
        (1-Real.exp (-l*t₀))*Real.exp (l*t) := by field_simp
    rw [heq]
    nlinarith
  have hratio : q/scale l b t ≤ q/(c*Real.exp (l*t)) :=
    div_le_div_of_nonneg_left hq (mul_pos hc (Real.exp_pos _)) hlower
  have hpow := Real.rpow_le_rpow (div_nonneg hq ha.le) hratio hb.le
  have hbound := (cdf_le_power hb (div_nonneg hq ha.le)).trans
    (div_le_div_of_nonneg_right hpow (mul_pos hb hg).le)
  have he : Real.exp (l*b/2*t)*(q/(c*Real.exp (l*t)))^b/(b*Real.Gamma b) =
      1/(b*Real.Gamma b*c^b)*Real.exp (-(l*b/2)*t)*q^b := by
    rw [Real.div_rpow hq (mul_pos hc (Real.exp_pos _)).le,
      Real.mul_rpow hc.le (Real.exp_pos _).le, ← Real.exp_mul]
    have hratioexp : Real.exp (l*b/2*t)/Real.exp (l*t*b) = Real.exp (-(l*b/2)*t) := by
      rw [← Real.exp_sub]; congr 1; ring
    calc
      _ = (Real.exp (l*b/2*t)/Real.exp (l*t*b))*q^b/(b*Real.Gamma b*c^b) := by ring
      _ = _ := by rw [hratioexp]; ring
  calc
    _ ≤ Real.exp (l*b/2*t)*((q/(c*Real.exp (l*t)))^b/(b*Real.Gamma b)) :=
      mul_le_mul_of_nonneg_left hbound (Real.exp_pos _).le
    _ = _ := by rw [← mul_div_assoc, he]

end SLEExactGauge.AngularBarrier

end

end

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
open FiniteTilt AngularBarrier

theorem radiusApproachBoundFrom (κ : ℝ) (hκ : 0 < κ ∧ κ < 8) (u₀ : ℝ) (hu₀ : 0 < u₀) :
    ∃ C : ℝ, 0 < C ∧
    ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (B : ℝ≥0 → Ω → ℝ) (_hB : IsBrownianReal B P)
      (γ : Ω → ℝ → ℂ) (g f : Ω → ℝ → ℂ → ℂ)
      (_hγ : ∀ t, 0 ≤ t → AEMeasurable (fun sample => γ sample t) P)
      (_hmaps : ∀ᵐ sample ∂P, IsLoewnerTraceUsing
        (fun t => Real.sqrt κ * B t.toNNReal sample) (γ sample) (g sample) (f sample))
      (z : ℂ) (_hz : z ∈ halfPlane) (u : ℝ) (_hu : u₀ ≤ u),
      P {sample | firstLiveRadiusStop (γ sample) (g sample) z u ≠ (⊤ : ℝ≥0∞)} ≤
        ENNReal.ofReal (C * Real.exp (-codimension κ * u) *
          (z.im / ‖z‖) ^ (8 / κ - 1)) := by
  have hl : 0 < κ/2 := div_pos hκ.1 (by norm_num)
  have hb : 0 < (8/κ-1)/2 := by
    have hh : 1 < 8/κ := (lt_div_iff₀ hκ.1).2 (by simpa using hκ.2)
    linarith
  obtain ⟨C,hC,hdec⟩ := value_decay_from hl hb hu₀
  refine ⟨C,hC,?_⟩
  intro Ω _ P _ B hB γ g f hγ hmaps z hz u hu
  have hu0 : 0 < u := hu₀.trans_le hu
  apply (radiusApproachProfile κ hκ B hB γ g f hmaps z hz u hu0).trans
  apply ENNReal.ofReal_le_ofReal
  have hp : (κ/2)*((8/κ-1)/2)/2 = codimension κ := by
    unfold codimension dimension
    field_simp [hκ.1.ne']
    ring
  have hq : (squaredSine (z.re/z.im))^((8/κ-1)/2) = (z.im/‖z‖)^(8/κ-1) := by
    rw [squaredSine_initial hz, ← Real.rpow_natCast (z.im/‖z‖) 2,
      ← Real.rpow_mul (initial_sine_pos hz).le]
    congr 1
    ring
  have hh := hdec u (squaredSine (z.re/z.im)) hu (squaredSine_pos _).le
  simpa only [profile,hp,hq] using hh

def finiteCenteredMeasure {Ω : Type*} [MeasurableSpace Ω]
    (κ : ℝ) (P : Measure Ω) (B : ℝ≥0 → Ω → ℝ)
    (γ : Ω → ℝ → ℂ) (g : Ω → ℝ → ℂ → ℂ) (z : ℂ) (u : ℝ) : Measure Ω :=
  P.withDensity (fun sample =>
    finiteStoppedDensity κ (fun t => B t sample) (γ sample) (g sample) z u /
      ENNReal.ofReal ((2*z.im)^(-codimension κ)*(z.im/‖z‖)^(8/κ-1)))

def radiusStoppedInverseAngle {Ω : Type*} (κ : ℝ) (B : ℝ≥0 → Ω → ℝ)
    (γ : Ω → ℝ → ℂ) (g : Ω → ℝ → ℂ → ℂ) (z : ℂ) (u : ℝ) (sample : Ω) : ℝ≥0∞ :=
  let τ := firstLiveRadiusStop (γ sample) (g sample) z u
  if τ = (⊤ : ℝ≥0∞) then 1 else ENNReal.ofReal
    ((loewnerAngleSine κ (fun t => B t sample) (g sample) τ.toReal z)^(-(8/κ-1)))

lemma finiteStoppedDensity_aemeasurable {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (κ : ℝ) (hκ : 0 < κ ∧ κ < 8)
    (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P)
    (γ : Ω → ℝ → ℂ) (g f : Ω → ℝ → ℂ → ℂ)
    (hmaps : ∀ᵐ sample ∂P, IsLoewnerTraceUsing
      (fun t => Real.sqrt κ * B t.toNNReal sample) (γ sample) (g sample) (f sample))
    (z : ℂ) (hz : z ∈ halfPlane) (u : ℝ) (hu : 0 < u) :
    AEMeasurable (fun sample => finiteStoppedDensity κ (fun t => B t sample)
      (γ sample) (g sample) z u) P := by
  let C := cutoffs hz u hu.le
  let F := fun n sample => ENNReal.ofReal ((C n).value κ B sample)
  have hexp (n : ℕ) := (C n).expectation hB κ hκ hz hu.le
  have hFm (n : ℕ) : AEMeasurable (F n) P :=
    ENNReal.measurable_ofReal.comp_aemeasurable (hexp n).1.aemeasurable
  have hFl : ∀ᵐ sample ∂P, Tendsto (fun n => F n sample) atTop
      (𝓝 (finiteStoppedDensity κ (fun t => B t sample) (γ sample) (g sample) z u)) := by
    filter_upwards [hmaps,hB.cont,hB.toIsPreBrownianReal.eval_zero_ae_eq_zero] with sample hm hc hb
    exact tendsto_value_killed κ B sample hm hz hu hc hb hκ
  exact aemeasurable_of_tendsto_metrizable_ae' hFm hFl

lemma finiteStoppedDensity_lt_top (κ : ℝ) (B : ℝ≥0 → ℝ) (γ : ℝ → ℂ)
    (g : ℝ → ℂ → ℂ) (z : ℂ) (u : ℝ) : finiteStoppedDensity κ B γ g z u < (⊤ : ℝ≥0∞) := by
  dsimp only [finiteStoppedDensity]
  split_ifs <;> simp

lemma localizationInitialGreen_pos (κ : ℝ) {z : ℂ} (hz : z ∈ halfPlane) :
    0 < (2*z.im)^(-codimension κ)*(z.im/‖z‖)^(8/κ-1) := by
  have hy : 0 < z.im := hz
  exact mul_pos (Real.rpow_pos_of_pos (by positivity) _) (Real.rpow_pos_of_pos (initial_sine_pos hz) _)

lemma finiteCenteredMeasure_probability {Ω : Type*} [MeasurableSpace Ω]
    (κ : ℝ) (hκ : 0 < κ ∧ κ < 8) (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P)
    (γ : Ω → ℝ → ℂ) (g f : Ω → ℝ → ℂ → ℂ)
    (hγ : ∀ t, 0 ≤ t → AEMeasurable (fun sample => γ sample t) P)
    (hmaps : ∀ᵐ sample ∂P, IsLoewnerTraceUsing
      (fun t => Real.sqrt κ * B t.toNNReal sample) (γ sample) (g sample) (f sample))
    (z : ℂ) (hz : z ∈ halfPlane) (u : ℝ) (hu : 0 < u) :
    IsProbabilityMeasure (finiteCenteredMeasure κ P B γ g z u) := by
  have hm0 : ENNReal.ofReal ((2*z.im)^(-codimension κ)*(z.im/‖z‖)^(8/κ-1)) ≠ 0 :=
    (ENNReal.ofReal_pos.2 (localizationInitialGreen_pos κ hz)).ne'
  constructor
  rw [finiteCenteredMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  simp_rw [ENNReal.div_eq_inv_mul]
  rw [lintegral_const_mul' _ _ (ENNReal.inv_ne_top.2 hm0),
    finiteStoppedCenteredLaw κ hκ B hB γ g f hγ hmaps z hz u hu.le,
    ENNReal.inv_mul_cancel hm0 ENNReal.ofReal_ne_top]

lemma finiteStoppedDensity_mul_inverseAngle {Ω : Type*} (κ : ℝ)
    (B : ℝ≥0 → Ω → ℝ) (γ : Ω → ℝ → ℂ) (g f : Ω → ℝ → ℂ → ℂ)
    (z : ℂ) (hz : z ∈ halfPlane) (u : ℝ) (sample : Ω)
    (hm : IsLoewnerTraceUsing (fun t => Real.sqrt κ*B t.toNNReal sample)
      (γ sample) (g sample) (f sample))
    (hc : Continuous (fun t => B t sample)) :
    finiteStoppedDensity κ (fun t => B t sample) (γ sample) (g sample) z u *
      radiusStoppedInverseAngle κ B γ g z u sample =
    {sample | firstLiveRadiusStop (γ sample) (g sample) z u ≠ (⊤ : ℝ≥0∞)}.indicator
      (fun _ => ENNReal.ofReal (((2*z.im)*Real.exp (-u))^(-codimension κ))) sample := by
  classical
  by_cases hhit : firstLiveRadiusStop (γ sample) (g sample) z u = (⊤ : ℝ≥0∞)
  · simp [finiteStoppedDensity,radiusStoppedInverseAngle,hhit]
  have hex : ∃ t : ℝ≥0, z ∈ localizationDomain (γ sample) t ∧
      loewnerRadius (g sample) t z = (2*z.im)*Real.exp (-u) := by
    by_contra hn
    have he : {t : ℝ≥0 | z ∈ localizationDomain (γ sample) t ∧
        loewnerRadius (g sample) t z = (2*z.im)*Real.exp (-u)} = ∅ :=
      Set.eq_empty_iff_forall_notMem.2 (fun t ht => hn ⟨t,ht⟩)
    exact hhit (by simp only [firstLiveRadiusStop,he,Set.image_empty,sInf_empty])
  obtain ⟨t,hzt,hrt⟩ := hex
  have htau := hm.firstLiveRadiusStop_eq ((continuous_const.mul
    (hc.comp continuous_real_toNNReal)).continuousOn) hzt hrt
  have hs : 0 < loewnerAngleSine κ (fun t => B t sample) (g sample) t z := by
    have hh := div_pos (hm.im_pos t.coe_nonneg hzt) (norm_pos_iff.2 (hm.centered_ne_zero t.coe_nonneg hzt))
    simpa only [loewnerAngleSine, Complex.ofReal_mul] using hh
  have hr : 0 < ((2*z.im)*Real.exp (-u))^(-codimension κ) := by
    apply Real.rpow_pos_of_pos
    have hy : 0 < z.im := hz
    positivity
  simp only [finiteStoppedDensity,radiusStoppedInverseAngle,htau,ENNReal.coe_ne_top,
    ite_false,ENNReal.coe_toReal,hrt,Set.mem_ofPred_eq,Ne,not_false_eq_true,
    Set.indicator_of_mem]
  rw [← ENNReal.ofReal_mul (mul_pos hr (Real.rpow_pos_of_pos hs _)).le,
    mul_assoc, ← Real.rpow_add hs, add_neg_cancel, Real.rpow_zero,mul_one]

lemma radius_green_cancel (κ u : ℝ) {z : ℂ} (hz : z ∈ halfPlane) :
    (((2*z.im)*Real.exp (-u))^(-codimension κ) /
      ((2*z.im)^(-codimension κ)*(z.im/‖z‖)^(8/κ-1))) *
      (Real.exp (-codimension κ*u)*(z.im/‖z‖)^(8/κ-1)) = 1 := by
  have hy : 0 < 2*z.im := by have : 0 < z.im := hz; positivity
  have hs := Real.rpow_pos_of_pos (initial_sine_pos hz) (8/κ-1)
  have hp := Real.rpow_pos_of_pos hy (-codimension κ)
  rw [Real.mul_rpow hy.le (Real.exp_pos _).le, ← Real.exp_mul]
  have he : Real.exp (-u * -codimension κ) * Real.exp (-codimension κ*u) = 1 := by
    rw [← Real.exp_add, show -u * -codimension κ + -codimension κ*u = 0 by ring, Real.exp_zero]
  field_simp
  convert he using 1
  congr 2 <;> ring

theorem finiteCenteredInverseAngleBound (κ : ℝ) (hκ : 0 < κ ∧ κ < 8)
    (u₀ : ℝ) (hu₀ : 0 < u₀) :
    ∃ C : ℝ, 0 < C ∧
    ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (B : ℝ≥0 → Ω → ℝ) (_hB : IsBrownianReal B P)
      (γ : Ω → ℝ → ℂ) (g f : Ω → ℝ → ℂ → ℂ)
      (_hγ : ∀ t, 0 ≤ t → AEMeasurable (fun sample => γ sample t) P)
      (_hmaps : ∀ᵐ sample ∂P, IsLoewnerTraceUsing
        (fun t => Real.sqrt κ * B t.toNNReal sample) (γ sample) (g sample) (f sample))
      (z : ℂ) (_hz : z ∈ halfPlane) (u : ℝ) (_hu : u₀ ≤ u),
      IsProbabilityMeasure (finiteCenteredMeasure κ P B γ g z u) ∧
      (∫⁻ sample, radiusStoppedInverseAngle κ B γ g z u sample
        ∂finiteCenteredMeasure κ P B γ g z u) ≤ ENNReal.ofReal C := by
  obtain ⟨C,hC,hbound⟩ := radiusApproachBoundFrom κ hκ u₀ hu₀
  refine ⟨C,hC,?_⟩
  intro Ω _ P _ B hB γ g f hγ hmaps z hz u hu
  have hu0 : 0 < u := hu₀.trans_le hu
  refine ⟨finiteCenteredMeasure_probability κ hκ P B hB γ g f hγ hmaps z hz u hu0, ?_⟩
  let M₀ := ENNReal.ofReal ((2*z.im)^(-codimension κ)*(z.im/‖z‖)^(8/κ-1))
  let K := ENNReal.ofReal (((2*z.im)*Real.exp (-u))^(-codimension κ)) / M₀
  let H : Set Ω := {sample | firstLiveRadiusStop (γ sample) (g sample) z u ≠ (⊤ : ℝ≥0∞)}
  have hmpos := localizationInitialGreen_pos κ hz
  have hm0 : M₀ ≠ 0 := (ENNReal.ofReal_pos.2 hmpos).ne'
  have hd := finiteStoppedDensity_aemeasurable κ hκ B hB γ g f hmaps z hz u hu0
  have hdm : AEMeasurable (fun sample => finiteStoppedDensity κ (fun t => B t sample)
      (γ sample) (g sample) z u / M₀) P := hd.div_const M₀
  have hdf : ∀ᵐ sample ∂P, finiteStoppedDensity κ (fun t => B t sample)
      (γ sample) (g sample) z u / M₀ < (⊤ : ℝ≥0∞) := Filter.Eventually.of_forall
    (fun sample => ENNReal.div_lt_top (finiteStoppedDensity_lt_top κ _ _ _ z u).ne hm0)
  have he : (fun sample => (finiteStoppedDensity κ (fun t => B t sample)
      (γ sample) (g sample) z u / M₀) * radiusStoppedInverseAngle κ B γ g z u sample) =ᵐ[P]
      H.indicator (fun _ => K) := by
    filter_upwards [hmaps,hB.cont] with sample hm hc
    have hh := finiteStoppedDensity_mul_inverseAngle κ B γ g f z hz u sample hm hc
    rw [show (finiteStoppedDensity κ (fun t => B t sample) (γ sample) (g sample) z u / M₀) *
      radiusStoppedInverseAngle κ B γ g z u sample = (finiteStoppedDensity κ (fun t => B t sample)
      (γ sample) (g sample) z u * radiusStoppedInverseAngle κ B γ g z u sample) / M₀ by
        simp only [div_eq_mul_inv]; ac_rfl, hh]
    classical
    by_cases hhit : sample ∈ H
    · simp only [H] at hhit
      simp only [H, Set.indicator_of_mem hhit, K]
    · simp only [H] at hhit
      simp only [H, Set.indicator_of_notMem hhit, ENNReal.zero_div]
  change (∫⁻ sample, radiusStoppedInverseAngle κ B γ g z u sample ∂P.withDensity
    (fun sample => finiteStoppedDensity κ (fun t => B t sample) (γ sample) (g sample) z u / M₀)) ≤ _
  rw [lintegral_withDensity_eq_lintegral_mul_non_measurable₀ P hdm hdf]
  simp only [Pi.mul_apply]
  rw [lintegral_congr_ae he]
  calc
    (∫⁻ sample, H.indicator (fun _ => K) sample ∂P) ≤ K*P H := lintegral_indicator_const_le H K
    _ ≤ K * ENNReal.ofReal (C * Real.exp (-codimension κ*u)*(z.im/‖z‖)^(8/κ-1)) :=
      mul_le_mul' le_rfl (hbound P B hB γ g f hγ hmaps z hz u hu)
    _ = ENNReal.ofReal C := by
      dsimp only [K,M₀]
      have hy : 0 < z.im := hz
      have hratio : 0 ≤ ((2*z.im)*Real.exp (-u))^(-codimension κ) /
          ((2*z.im)^(-codimension κ)*(z.im/‖z‖)^(8/κ-1)) :=
        div_nonneg (Real.rpow_nonneg (by positivity) _) hmpos.le
      rw [← ENNReal.ofReal_div_of_pos hmpos, ← ENNReal.ofReal_mul hratio]
      congr 1
      calc
        _ = C * (((2*z.im)*Real.exp (-u))^(-codimension κ) /
            ((2*z.im)^(-codimension κ)*(z.im/‖z‖)^(8/κ-1)) *
            (Real.exp (-codimension κ*u)*(z.im/‖z‖)^(8/κ-1))) := by ring
        _ = C := by rw [radius_green_cancel κ u hz,mul_one]

end SLEExactGauge

end

end

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal unitInterval
namespace SLEExactGauge.GammaField
open LoewnerCutoff LoewnerField LoewnerExit AngularBarrier GreenPhysical

lemma profile_green_bound (κ : ℝ) (hκ : 0 < κ ∧ κ < 8) :
    ∃ K : ℝ, 0 < K ∧ ∀ x y l t ρ : ℝ, 0 < y → 0 < ρ → 1 ≤ t →
      Real.log (2*y)-l-Real.log ρ ≤ t →
      profile (κ/2) ((8/κ-1)/2) t (x/y) ≤
        K*ρ^(codimension κ)*green (1-κ/8) (8/κ-1) x y l := by
  have hl : 0 < κ/2 := by linarith [hκ.1]
  have hb : 0 < (8/κ-1)/2 := by
    have hh : 1 < 8/κ := (lt_div_iff₀ hκ.1).2 (by simpa using hκ.2)
    linarith
  obtain ⟨K,hK,hdec⟩ := value_decay_from hl hb (by norm_num : (0:ℝ)<1)
  refine ⟨K,hK,?_⟩
  intro x y l t ρ hy hρ ht hr
  have hp : (κ/2)*((8/κ-1)/2)/2 = codimension κ := by
    unfold codimension dimension
    field_simp [hκ.1.ne']
    ring
  have hp' : codimension κ = 1-κ/8 := by unfold codimension dimension; ring
  have hp0 : 0 ≤ codimension κ := by rw [hp']; linarith [hκ.2]
  have hs : 0 < Real.sqrt (x^2+y^2) := Real.sqrt_pos.2 (by positivity)
  have hq0 : squaredSine (x/y) = (y/Real.sqrt (x^2+y^2))^2 := by
    have hsq := Real.sq_sqrt (by positivity : 0 ≤ x^2+y^2)
    unfold squaredSine
    field_simp
    nlinarith
  have hq : (squaredSine (x/y))^((8/κ-1)/2) = (y/Real.sqrt (x^2+y^2))^(8/κ-1) := by
    rw [hq0, ← Real.rpow_natCast (y/Real.sqrt (x^2+y^2)) 2,
      ← Real.rpow_mul (div_pos hy hs).le]
    congr 1
    ring
  have he : Real.exp (-(codimension κ)*t) ≤
      ρ^(codimension κ)*(2*y/Real.exp l)^(-(1-κ/8)) := by
    rw [Real.rpow_def_of_pos hρ,Real.rpow_def_of_pos (div_pos (by positivity) (Real.exp_pos _)),
      ← Real.exp_add]
    apply Real.exp_le_exp.2
    rw [Real.log_div (by positivity) (Real.exp_ne_zero _),Real.log_exp,← hp']
    nlinarith [mul_le_mul_of_nonneg_left hr hp0]
  have hh := hdec t (squaredSine (x/y)) ht (squaredSine_pos _).le
  rw [hp,hq] at hh
  calc
    _ ≤ K*Real.exp (-(codimension κ)*t)*(y/Real.sqrt (x^2+y^2))^(8/κ-1) := hh
    _ ≤ K*(ρ^(codimension κ)*(2*y/Real.exp l)^(-(1-κ/8)))*(y/Real.sqrt (x^2+y^2))^(8/κ-1) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left he hK.le) (Real.rpow_nonneg (div_pos hy hs).le _)
    _ = _ := by rw [green_eq_source _ _ _ _ _ hy]; ring

end SLEExactGauge.GammaField

end

end

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal unitInterval
namespace SLEExactGauge.FiniteTilt.Cutoff
open LoewnerCutoff LoewnerField LoewnerExit GammaField

lemma height_radius_at_stop {z : ℂ} {u : ℝ} (C : Cutoff z u) (hz : z ∈ halfPlane)
    (hu : 0 ≤ u) {Ω : Type*} (κ : ℝ) (B : ℝ≥0 → Ω → ℝ) (sample : Ω)
    (hc : Continuous (fun t => B t sample)) (hb0 : B 0 sample = 0) :
    C.height ≤ (position C.height_pos C.horizon.coe_nonneg (C.paths κ B sample) z (C.stopTime κ B sample)).im ∧
    (2*z.im)*Real.exp (-u) ≤ radius C.height_pos C.horizon.coe_nonneg (C.paths κ B sample) z (C.stopTime κ B sample) := by
  rcases eq_or_lt_of_le hu with rfl | hu'
  · rw [C.stopTime_zero,position_initial]
    constructor
    · exact (C.height_initial hz le_rfl).le
    · simp only [radius,position_initial,logDerivative_initial,neg_zero,Real.exp_zero,mul_one,div_one,le_refl]
  · have hd := (deficit_nonneg_iff C.height_pos C.horizon.coe_nonneg _ z _ C.angle _).1
      (nonneg_until C.height_pos C.horizon.coe_nonneg C.horizon_pos _ z _ C.angle
        (C.initial_deficit_brownian κ B sample hz hu' hc hb0) ⟨(C.bounds κ B sample).1,le_rfl⟩)
    exact ⟨hd.2.1,hd.1⟩

lemma targetValue_bound (κ : ℝ) (hκ : 0 < κ ∧ κ < 8) :
    ∃ K : ℝ, 0 < K ∧ ∀ {z : ℂ} (hz : z ∈ halfPlane) {u v : ℝ}
      (_hu : 0 ≤ u) (huv : u+1 ≤ v) (C : Cutoff z v) {Ω : Type*}
      (B : ℝ≥0 → Ω → ℝ) (sample : Ω) (η : ℝ), 0 < η →
      Continuous (fun t => B t sample) → B 0 sample = 0 →
      C.targetValue hz (by linarith : u ≤ v) η κ B sample ≤
        K*((2*z.im)*Real.exp (-v))^(codimension κ) *
          (C.retarget hz (by linarith : u ≤ v)).value κ B sample := by
  obtain ⟨K,hK,hbound⟩ := profile_green_bound κ hκ
  refine ⟨K,hK,?_⟩
  intro z hz u v hu huv C Ω B sample η hη hc hb0
  let D := C.retarget hz (by linarith : u ≤ v)
  let τ := D.stopTime κ B sample
  let U := C.paths κ B sample
  have hd := D.height_radius_at_stop hz hu κ B sample hc hb0
  have hy : C.height ≤ (position C.height_pos C.horizon.coe_nonneg U z τ).im := hd.1
  have hR : (2*z.im)*Real.exp (-u) ≤ radius C.height_pos C.horizon.coe_nonneg U z τ := hd.2
  have hz0 : 0 < z.im := hz
  have hρu : 0 < (2*z.im)*Real.exp (-u) := by positivity
  have hρv : 0 < (2*z.im)*Real.exp (-v) := by positivity
  have hlog := Real.log_le_log hρu hR
  have hlρ (w : ℝ) : Real.log ((2*z.im)*Real.exp (-w)) = Real.log (2*z.im)-w := by
    rw [Real.log_mul (by positivity) (Real.exp_ne_zero _),Real.log_exp]; ring
  have hr0 := le_max_right η (rawRemaining C.height_pos C.horizon.coe_nonneg η ((2*z.im)*Real.exp (-v)) U z τ)
  change rawRemaining C.height_pos C.horizon.coe_nonneg η ((2*z.im)*Real.exp (-v)) U z τ ≤
    remaining C.height_pos C.horizon.coe_nonneg η ((2*z.im)*Real.exp (-v)) U z τ at hr0
  have hr1 : 1 ≤ remaining C.height_pos C.horizon.coe_nonneg η ((2*z.im)*Real.exp (-v)) U z τ := by
    rw [rawRemaining_eq C.height_pos C.horizon.coe_nonneg _ _ _ _ _ hy,hlρ] at hr0
    rw [hlρ] at hlog
    exact le_trans (by linarith : 1 ≤ η+Real.log (radius C.height_pos C.horizon.coe_nonneg U z τ)-(Real.log (2*z.im)-v)) hr0
  have hr2 : Real.log (2*LoewnerField.height C.height_pos C.horizon.coe_nonneg U z τ)-
      logDerivative C.height_pos C.horizon.coe_nonneg U z τ-Real.log ((2*z.im)*Real.exp (-v)) ≤
      remaining C.height_pos C.horizon.coe_nonneg η ((2*z.im)*Real.exp (-v)) U z τ := by
    unfold rawRemaining at hr0
    linarith
  exact hbound _ _ _ _ _ (LoewnerField.height_pos _ _ _ _ _) hρv hr1 hr2

end SLEExactGauge.FiniteTilt.Cutoff

end

end

end OAI
