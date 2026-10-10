import Mathlib
import OAI.Probability.SLELocalization.AngularClock
import OAI.Probability.SLE.ClippedCoordinates

namespace OAI


/-! Conformal localization and Charge estimates. -/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal unitInterval
noncomputable section
open Set Filter
open scoped Topology ContDiff
noncomputable section
open Set Filter MeasureTheory
open scoped Topology unitInterval
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal unitInterval
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal unitInterval
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal unitInterval
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal unitInterval
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
noncomputable section
open Set Filter Metric
open scoped Topology NNReal
noncomputable section
open Set Filter Metric
open scoped Topology NNReal
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Metric
open scoped Topology NNReal ENNReal
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Metric
open scoped Topology NNReal ENNReal
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Metric TopologicalSpace
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

def sausage (γ : ℝ → ℂ) (v : ℝ) : Set ℂ :=
  {w | ∃ t : ℝ, 0 ≤ t ∧ dist w (γ t) < v}

def sausageCharge (κ : ℝ) (γ : ℝ → ℂ) (v : ℝ) (A : Set ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal (v^(-codimension κ)) * volume (A ∩ sausage γ v)

lemma sausage_open (γ : ℝ → ℂ) (v : ℝ) : IsOpen (sausage γ v) := by
  have he : sausage γ v = ⋃ t : ℝ, ⋃ (_ : 0 ≤ t), ball (γ t) v := by
    ext w
    simp [sausage,mem_ball]
  rw [he]
  exact isOpen_iUnion (fun t => isOpen_iUnion (fun _ => isOpen_ball))

lemma sausage_eq_dense {γ : ℝ → ℂ} (hγ : ContinuousOn γ (Ici 0)) (v : ℝ) :
    sausage γ v = ⋃ n : ℕ, ball (γ (denseSeq ℝ≥0 n)) v := by
  ext w
  simp only [sausage,mem_ofPred_eq,mem_iUnion,mem_ball]
  constructor
  · rintro ⟨t,ht,hvisit⟩
    by_contra hn
    push Not at hn
    have hc : Continuous (fun q : ℝ≥0 => dist w (γ q)) :=
      continuous_const.dist (hγ.comp_continuous continuous_subtype_val (fun q => q.coe_nonneg))
    have hh : v ≤ dist w (γ t) := (denseRange_denseSeq ℝ≥0).induction_on (p := fun q : ℝ≥0 => v ≤ dist w (γ q)) (⟨t,ht⟩ : ℝ≥0)
      (isClosed_le continuous_const hc) hn
    exact (not_lt_of_ge hh) hvisit
  · rintro ⟨n,hn⟩
    exact ⟨denseSeq ℝ≥0 n,(denseSeq ℝ≥0 n).coe_nonneg,hn⟩

lemma measurable_sausage_representative {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (γ : Ω → ℝ → ℂ)
    (hγ : ∀ t, 0 ≤ t → AEMeasurable (fun sample => γ sample t) P)
    (hc : ∀ᵐ sample ∂P, ContinuousOn (γ sample) (Ici 0)) (v : ℝ) :
    ∃ E : Set (Ω × ℂ), MeasurableSet E ∧
      ∀ᵐ sample ∂P, ∀ w : ℂ, (sample,w) ∈ E ↔ w ∈ sausage (γ sample) v := by
  let Y (n : ℕ) := (hγ (denseSeq ℝ≥0 n) (denseSeq ℝ≥0 n).coe_nonneg).mk (fun sample => γ sample (denseSeq ℝ≥0 n))
  have hY (n : ℕ) : Measurable (Y n) := (hγ _ (denseSeq ℝ≥0 n).coe_nonneg).measurable_mk
  have he : ∀ᵐ sample ∂P, ∀ n : ℕ, γ sample (denseSeq ℝ≥0 n) = Y n sample :=
    ae_all_iff.2 (fun n => (hγ _ (denseSeq ℝ≥0 n).coe_nonneg).ae_eq_mk)
  let E : Set (Ω × ℂ) := ⋃ n : ℕ, {x | dist x.2 (Y n x.1) < v}
  refine ⟨E,MeasurableSet.iUnion (fun n => measurableSet_lt
    (measurable_snd.dist ((hY n).comp measurable_fst)) measurable_const),?_⟩
  filter_upwards [hc,he] with sample hcont heq
  intro w
  rw [sausage_eq_dense hcont v]
  simp only [E,mem_iUnion,mem_ofPred_eq,mem_ball,heq]

lemma expected_sausage_area {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [SFinite P]
    (γ : Ω → ℝ → ℂ)
    (hγ : ∀ t, 0 ≤ t → AEMeasurable (fun sample => γ sample t) P)
    (hc : ∀ᵐ sample ∂P, ContinuousOn (γ sample) (Ici 0)) (v : ℝ)
    (A : Set ℂ) (_hA : MeasurableSet A) :
    (∫⁻ sample, volume (A ∩ sausage (γ sample) v) ∂P) =
      ∫⁻ w in A, P {sample | w ∈ sausage (γ sample) v} := by
  classical
  obtain ⟨E,hE,he⟩ := measurable_sausage_representative γ hγ hc v
  let F : Ω → ℂ → ℝ≥0∞ := fun sample w => E.indicator (fun _ => 1) (sample,w)
  have hFm : Measurable (Function.uncurry F) := measurable_const.indicator hE
  have hleft : (fun sample => volume (A ∩ sausage (γ sample) v)) =ᵐ[P]
      (fun sample => ∫⁻ w in A, F sample w) := by
    filter_upwards [he] with sample heq
    have hf : F sample = (sausage (γ sample) v).indicator (fun _ => (1:ℝ≥0∞)) := by
      funext w
      simp only [F,indicator_apply,heq]
    rw [hf,lintegral_indicator_fun_one (sausage_open (γ sample) v).measurableSet,
      Measure.restrict_apply (sausage_open (γ sample) v).measurableSet,inter_comm]
  rw [lintegral_congr_ae hleft,lintegral_lintegral_swap hFm.aemeasurable]
  apply lintegral_congr
  intro w
  have hset : MeasurableSet {sample | (sample,w) ∈ E} := hE.preimage (measurable_id.prodMk measurable_const)
  have hFe : (fun sample => F sample w) = ({sample | (sample,w) ∈ E}).indicator (fun _ => (1:ℝ≥0∞)) := rfl
  rw [hFe,lintegral_indicator_fun_one hset]
  apply measure_congr
  filter_upwards [he] with sample heq
  exact propext (heq w)

end SLEExactGauge

end

end

end

end

end

end

end

end

end

end

end

end

end

end

end

end

end

end

end

end

end

end

end

noncomputable section
open Set Filter MeasureTheory
open scoped Topology
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal unitInterval
noncomputable section
open Set Filter
open scoped Topology ContDiff
noncomputable section
open Set Filter MeasureTheory
open scoped Topology unitInterval
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal unitInterval
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal unitInterval
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal unitInterval
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal unitInterval
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
noncomputable section
open Set Filter Metric
open scoped Topology NNReal
noncomputable section
open Set Filter Metric
open scoped Topology NNReal
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Metric
open scoped Topology NNReal ENNReal
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Metric
open scoped Topology NNReal ENNReal
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Metric TopologicalSpace
open scoped Topology NNReal ENNReal
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Metric
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

lemma IsChordalSLE.maps {Ω : Type*} [MeasurableSpace Ω] {κ : ℝ} {P : Measure Ω}
    {γ : Ω → ℝ → ℂ} (h : IsChordalSLE κ P γ) :
    ∃ B : ℝ≥0 → Ω → ℝ, ∃ g f : Ω → ℝ → ℂ → ℂ,
       IsBrownianReal B P ∧ ∀ᵐ sample ∂P, IsLoewnerTraceUsing
         (fun t => Real.sqrt κ * B t.toNNReal sample) (γ sample) (g sample) (f sample) := by
  classical
  obtain ⟨hm,B,hB,htrace⟩ := h
  have hex (sample : Ω) : ∃ g f : ℝ → ℂ → ℂ,
      IsLoewnerTrace (fun t => Real.sqrt κ * B t.toNNReal sample) (γ sample) →
      IsLoewnerTraceUsing (fun t => Real.sqrt κ * B t.toNNReal sample) (γ sample) g f := by
    by_cases hh : IsLoewnerTrace (fun t => Real.sqrt κ * B t.toNNReal sample) (γ sample)
    · obtain ⟨hc,hz,hi,ht,g,f,hr⟩ := hh
      exact ⟨g,f,fun _ => ⟨hc,hz,hi,ht,hr⟩⟩
    · exact ⟨0,0,fun hh' => (hh hh').elim⟩
  choose g f hgf using hex
  exact ⟨B,g,f,hB,htrace.mono (fun sample hs => hgf sample hs)⟩

lemma IsChordalSLE.continuous {Ω : Type*} [MeasurableSpace Ω] {κ : ℝ} {P : Measure Ω}
    {γ : Ω → ℝ → ℂ} (h : IsChordalSLE κ P γ) :
    ∀ᵐ sample ∂P, ContinuousOn (γ sample) (Ici 0) := by
  obtain ⟨B,hB,ht⟩ := h.2
  exact ht.mono (fun _ hh => hh.1)

lemma IsChordalSLE.no_sausage_below {Ω : Type*} [MeasurableSpace Ω] {κ : ℝ} {P : Measure Ω}
    {γ : Ω → ℝ → ℂ} (h : IsChordalSLE κ P γ) {z : ℂ} {v : ℝ} (hz : z.im ≤ -v) :
    P {sample | z ∈ sausage (γ sample) v} = 0 := by
  obtain ⟨B,hB,ht⟩ := h.2
  apply measure_mono_null (t := {sample | ¬ IsLoewnerTrace
    (fun t => Real.sqrt κ * B t.toNNReal sample) (γ sample)})
  · intro sample hs hh
    obtain ⟨t,ht0,hv⟩ := hs
    have hi := hh.2.2.1 t ht0
    have hab := Complex.abs_im_le_norm (z-γ sample t)
    have hn := neg_abs_le (z-γ sample t).im
    rw [dist_eq_norm] at hv
    simp only [Complex.sub_im] at hab hn
    linarith
  · exact ae_iff.1 ht

theorem sausage_point_bound (κ : ℝ) (hκ : 0 < κ ∧ κ < 8) :
    ∃ A K : ℝ, 1 < A ∧ 0 < K ∧
    ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (γ : Ω → ℝ → ℂ) (_hγ : IsChordalSLE κ P γ) (z : ℂ) (v : ℝ)
      (_hv : 0 < v) (_hhigh : A*v < z.im),
      P {sample | z ∈ sausage (γ sample) v} ≤
        ENNReal.ofReal (K*v^(codimension κ)*z.im^(-codimension κ)) := by
  obtain ⟨C,c,hC,hc,hc1,hbound⟩ := euclideanApproachBound κ hκ
  let p := codimension κ
  refine ⟨6/c,C*3^p*2^(-p),by rw [lt_div_iff₀ hc]; linarith,
    by positivity,?_⟩
  intro Ω _ P _ γ hγ z v hv hhigh
  obtain ⟨B,g,f,hB,hmaps⟩ := hγ.maps
  have hy : 0 < z.im := lt_trans (by positivity : 0 < (6/c)*v) hhigh
  have hcy : 6*v < c*z.im := by
    have hx := mul_lt_mul_of_pos_left hhigh hc
    field_simp at hx
    nlinarith
  have hsmall : 2*v < z.im := by nlinarith
  have hsub : {sample | z ∈ sausage (γ sample) v} ≤ᵐ[P]
      {sample | liveDistanceApproach (γ sample) z (3*v)} := by
    filter_upwards [hmaps] with sample hm hs
    obtain ⟨visitTime,hvisitTime,hvisit⟩ := hs
    let visitNonneg : ℝ≥0 := ⟨visitTime,hvisitTime⟩
    have hcont : Continuous (fun time : ℝ≥0 => dist z (γ sample time)) :=
      continuous_const.dist (hm.1.comp_continuous continuous_subtype_val
        (fun time => time.coe_nonneg))
    let approachTimes : Set ℝ≥0 := Icc 0 visitNonneg ∩
      {time | dist z (γ sample time) ≤ 2*v}
    have hcompact : IsCompact approachTimes :=
      isCompact_Icc.inter_right (isClosed_le hcont continuous_const)
    obtain ⟨firstTime,hfirst,hmin⟩ := hcompact.exists_isLeast
      ⟨visitNonneg,⟨⟨zero_le,le_rfl⟩,by change dist z (γ sample visitTime) ≤ 2*v; linarith⟩⟩
    have hfirstTime : (firstTime:ℝ) ≤ visitTime := hfirst.1.2
    have hstrict (time : ℝ≥0) (htime : time < firstTime) :
        2*v < dist z (γ sample time) := by
      by_contra hn
      exact (not_le_of_gt htime)
        (hmin ⟨⟨zero_le,htime.le.trans hfirst.1.2⟩,not_lt.1 hn⟩)
    have hinit : 2*v < dist z (γ sample 0) := by
      rw [hm.2.1,dist_zero_right]
      exact hsmall.trans_le (Complex.im_le_norm z)
    have hdist : dist z (γ sample firstTime) = 2*v := by
      apply le_antisymm hfirst.2
      by_contra hn
      have hlt : dist z (γ sample firstTime) < 2*v := not_le.1 hn
      have hcc : ContinuousOn (fun time : ℝ => dist z (γ sample time))
          (Icc 0 (firstTime:ℝ)) :=
        (continuous_const.dist continuous_id).comp_continuousOn
          (hm.1.mono Icc_subset_Ici_self)
      obtain ⟨time,htime,heq⟩ := intermediate_value_Icc' firstTime.coe_nonneg hcc
        ⟨hlt.le,hinit.le⟩
      have htimeFirst : time < (firstTime:ℝ) :=
        lt_of_le_of_ne htime.2 (by intro heq; subst time; linarith)
      have hh := hstrict ⟨time,htime.1⟩ htimeFirst
      change 2*v < dist z (γ sample time) at hh
      exact (not_lt_of_ge heq.le) hh
    have hbefore (time : ℝ) (htime : time ∈ Icc 0 (firstTime:ℝ)) :
        2*v ≤ dist z (γ sample time) := by
      rcases lt_or_eq_of_le htime.2 with hlt | heq
      · exact (hstrict ⟨time,htime.1⟩ hlt).le
      · rw [heq,hdist]
    have hfree : ball z (2*v) ⊆ halfPlane \ localizationSegment (γ sample) 0 firstTime := by
      intro point hpoint
      have hnorm : ‖point-z‖ < 2*v := by
        simpa only [mem_ball,dist_eq_norm] using hpoint
      constructor
      · have hh := Complex.abs_im_le_norm (point-z)
        have hn := neg_abs_le (point-z).im
        change 0 < point.im
        simp only [Complex.sub_im] at hh hn
        linarith
      · rintro ⟨time,htime,rfl⟩
        have hh := hbefore time htime
        have hh' := mem_ball.1 hpoint
        rw [dist_comm] at hh'
        linarith
    have hclosure := hm.future_tip_mem_closure firstTime.coe_nonneg hfirstTime
    have hball : γ sample visitTime ∈ ball z (2*v) := by
      rw [mem_ball,dist_comm]
      linarith
    obtain ⟨point,hpointBall,hpointDomain⟩ :=
      mem_closure_iff.1 hclosure (ball z (2*v)) isOpen_ball hball
    have hcomponent :=
      (convex_ball z (2*v)).isPreconnected.subset_connectedComponentIn hpointBall hfree
    have hzball : z ∈ ball z (2*v) := mem_ball_self (by positivity)
    have hzlive : z ∈ localizationDomain (γ sample) firstTime := by
      refine ⟨hfree hzball,?_⟩
      rw [← connectedComponentIn_eq (hcomponent hzball)]
      exact hpointDomain.2
    refine ⟨firstTime,hzlive,?_⟩
    have hnot : γ sample firstTime ∈ (localizationDomain (γ sample) firstTime)ᶜ := by
      intro hh
      exact hh.1.2 ⟨firstTime,⟨firstTime.coe_nonneg,le_rfl⟩,rfl⟩
    have hh := infDist_le_dist_of_mem (x := z) hnot
    rw [hdist] at hh
    linarith
  apply (measure_mono_ae hsub).trans
  apply (hbound P B hB γ g f hγ.1 hmaps z hy (3*v) (by positivity) (by linarith)).trans
  apply ENNReal.ofReal_le_ofReal
  have hn : 0 < ‖z‖ := lt_of_lt_of_le hy (Complex.im_le_norm z)
  have ha : 0 ≤ 8/κ-1 := by rw [sub_nonneg,le_div_iff₀ hκ.1]; linarith [hκ.2]
  have hs : (z.im/‖z‖)^(8/κ-1) ≤ 1 :=
    Real.rpow_le_one (by positivity) ((div_le_one hn).2 (Complex.im_le_norm z)) ha
  have hnon : 0 ≤ C*(2*z.im)^(-p)*(3*v)^p := by positivity
  calc
    C*((2*z.im)^(-p)*(z.im/‖z‖)^(8/κ-1))*(3*v)^p
        = (C*(2*z.im)^(-p)*(3*v)^p)*((z.im/‖z‖)^(8/κ-1)) := by ring
    _ ≤ (C*(2*z.im)^(-p)*(3*v)^p)*1 := mul_le_mul_of_nonneg_left hs hnon
    _ = (C*3^p*2^(-p))*v^p*z.im^(-p) := by
      rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hy.le,
        Real.mul_rpow (by norm_num : (0:ℝ) ≤ 3) hv.le]
      ring

end SLEExactGauge

end

end

end

end

end

end

end

end

end

end

end

end

end

end

end

end

end

end

end

end

end

end

end

end

noncomputable section
open Set Filter MeasureTheory
open scoped Topology
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal unitInterval
noncomputable section
open Set Filter
open scoped Topology ContDiff
noncomputable section
open Set Filter MeasureTheory
open scoped Topology unitInterval
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal unitInterval
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal unitInterval
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal unitInterval
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal unitInterval
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
noncomputable section
open Set Filter Metric
open scoped Topology NNReal
noncomputable section
open Set Filter Metric
open scoped Topology NNReal
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Metric
open scoped Topology NNReal ENNReal
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Metric
open scoped Topology NNReal ENNReal
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Metric TopologicalSpace
open scoped Topology NNReal ENNReal
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Metric
open scoped Topology NNReal ENNReal
noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

def regionBand (R a b : ℝ) : Set ℂ :=
  {w | w.re ∈ Icc (-R) R ∧ w.im ∈ Icc a b}

lemma regionBand_measurable (R a b : ℝ) : MeasurableSet (regionBand R a b) :=
  (Complex.measurable_re measurableSet_Icc).inter (Complex.measurable_im measurableSet_Icc)

lemma lintegral_regionBand (R a b : ℝ) (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ w in regionBand R a b, F w.im) =
      ENNReal.ofReal (2*R) * ∫⁻ y in Icc a b, F y := by
  have he := Complex.volume_preserving_equiv_real_prod.setLIntegral_comp_preimage_emb
    Complex.measurableEquivRealProd.measurableEmbedding (fun x : ℝ × ℝ => F x.2)
      (Icc (-R) R ×ˢ Icc a b)
  change (∫⁻ w in regionBand R a b, F w.im) = _ at he
  rw [he,Measure.volume_eq_prod,← Measure.prod_restrict,
    lintegral_prod (fun x : ℝ × ℝ => F x.2) (hF.comp measurable_snd).aemeasurable]
  simp only [lintegral_const,Measure.restrict_apply_univ,Real.volume_Icc,sub_neg_eq_add,
    ← two_mul R,mul_comm]

lemma volume_regionBand (R a b : ℝ) :
    volume (regionBand R a b) = ENNReal.ofReal (2*R)*ENNReal.ofReal (b-a) := by
  simpa only [lintegral_one,Measure.restrict_apply_univ,Real.volume_Icc] using
    lintegral_regionBand R a b (fun _ => 1) measurable_const

lemma height_kernel_finite (R p : ℝ) (hR : 0 ≤ R) (hp : p < 1) :
    (∫⁻ w in regionBand R 0 R, ENNReal.ofReal (w.im^(-p))) < ⊤ := by
  rw [lintegral_regionBand R 0 R (fun y : ℝ => ENNReal.ofReal (y^(-p))) (measurable_id.pow_const (-p)).ennreal_ofReal]
  apply ENNReal.mul_lt_top ENNReal.ofReal_lt_top
  have hi : IntegrableOn (fun y : ℝ => y^(-p)) (Icc 0 R) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hR).1 (intervalIntegral.intervalIntegrable_rpow' (by linarith))
  rw [← ofReal_integral_eq_lintegral_ofReal hi]
  · exact ENNReal.ofReal_lt_top
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
    exact Real.rpow_nonneg hy.1 _

end SLEExactGauge

end

end

end

end

end

end

end

end

end

end

end

end

end

end

end

end

end

end

end

end

end

end

end

end

end

noncomputable section
open Set Filter MeasureTheory
open scoped Topology
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal unitInterval
noncomputable section
open Set Filter
open scoped Topology ContDiff
noncomputable section
open Set Filter MeasureTheory
open scoped Topology unitInterval
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal unitInterval
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal unitInterval
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal unitInterval
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal unitInterval
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
noncomputable section
open Set Filter Metric
open scoped Topology NNReal
noncomputable section
open Set Filter Metric
open scoped Topology NNReal
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Metric
open scoped Topology NNReal ENNReal
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Metric
open scoped Topology NNReal ENNReal
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Metric TopologicalSpace
open scoped Topology NNReal ENNReal
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Metric
open scoped Topology NNReal ENNReal
noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Metric
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
universe u

lemma expected_sausage_area_bound
    {κ R A K : ℝ} (_hR : 0 < R) (hA : 1 < A) (hK : 0 < K)
    (hb : ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (γ : Ω → ℝ → ℂ) (_hγ : IsChordalSLE κ P γ) (z : ℂ) (v : ℝ)
      (_hv : 0 < v) (_hhigh : A*v < z.im),
      P {sample | z ∈ sausage (γ sample) v} ≤
        ENNReal.ofReal (K*v^(codimension κ)*z.im^(-codimension κ)))
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (γ : Ω → ℝ → ℂ) (hγ : IsChordalSLE κ P γ) (v : ℝ) (hv : 0 < v) :
    (∫⁻ sample, volume (ball 0 R ∩ sausage (γ sample) v) ∂P) ≤
      ENNReal.ofReal (2*R)*ENNReal.ofReal ((A+1)*v) +
        ENNReal.ofReal (K*v^(codimension κ)) *
          ∫⁻ w in regionBand R 0 R, ENNReal.ofReal (w.im^(-codimension κ)) := by
  rw [expected_sausage_area γ hγ.1 hγ.continuous v (ball 0 R) measurableSet_ball]
  let F := (regionBand R (-v) (A*v)).indicator (fun _ => (1 : ℝ≥0∞))
  let G := (regionBand R 0 R).indicator (fun w => ENNReal.ofReal (w.im^(-codimension κ)))
  have hFm : Measurable F := measurable_const.indicator (regionBand_measurable _ _ _)
  have hGm : Measurable G :=
    (Complex.measurable_im.pow_const _).ennreal_ofReal.indicator (regionBand_measurable _ _ _)
  have hmono : (∫⁻ w in ball 0 R, P {sample | w ∈ sausage (γ sample) v}) ≤
      ∫⁻ w in ball 0 R, F w + ENNReal.ofReal (K*v^(codimension κ))*G w := by
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem measurableSet_ball] with w hw
    have hnorm : ‖w‖ < R := by simpa only [mem_ball,dist_zero_right] using hw
    have hre : w.re ∈ Icc (-R) R := by
      have hh := Complex.abs_re_le_norm w
      exact ⟨by linarith [neg_abs_le w.re],by linarith [le_abs_self w.re]⟩
    by_cases hhigh : A*v < w.im
    · have hwG : w ∈ regionBand R 0 R := ⟨hre,by constructor; nlinarith; exact (Complex.im_le_norm w).trans hnorm.le⟩
      have hh := hb P γ hγ w v hv hhigh
      have hmul : ENNReal.ofReal (K*v^(codimension κ)*w.im^(-codimension κ)) =
          ENNReal.ofReal (K*v^(codimension κ))*G w := by
        rw [show G w = ENNReal.ofReal (w.im^(-codimension κ)) from indicator_of_mem hwG _]
        exact ENNReal.ofReal_mul (by positivity)
      rw [hmul] at hh
      exact hh.trans (le_add_left le_rfl)
    · by_cases hlow : w.im ≤ -v
      · rw [hγ.no_sausage_below hlow]
        exact zero_le
      · have hwF : w ∈ regionBand R (-v) (A*v) := ⟨hre,le_of_lt (not_le.1 hlow),not_lt.1 hhigh⟩
        have hh : P {sample | w ∈ sausage (γ sample) v} ≤ 1 := prob_le_one
        rw [show F w = 1 from indicator_of_mem hwF _]
        exact hh.trans (le_add_right le_rfl)
  apply hmono.trans
  apply (setLIntegral_le_lintegral (ball 0 R) (fun w => F w + ENNReal.ofReal (K*v^(codimension κ))*G w)).trans
  rw [lintegral_add_left hFm,lintegral_const_mul _ hGm]
  rw [show (∫⁻ w, F w) = volume (regionBand R (-v) (A*v)) from
      lintegral_indicator_fun_one (regionBand_measurable _ _ _),
    show (∫⁻ w, G w) = ∫⁻ w in regionBand R 0 R, ENNReal.ofReal (w.im^(-codimension κ)) from
      lintegral_indicator (regionBand_measurable _ _ _) _,volume_regionBand]
  have he : A*v-(-v) = (A+1)*v := by ring
  rw [he]

theorem uniformBoundedRegionCharge (κ : ℝ) (hκ : 0 < κ ∧ κ < 8)
    (R : ℝ) (hR : 0 < R) :
    ∃ C : ℝ≥0, ∀ {Ω : Type u} [MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P] (γ : Ω → ℝ → ℂ)
      (_hγ : IsChordalSLE κ P γ) (v : ℝ) (_hv : 0 < v) (_hv1 : v ≤ 1),
      (∫⁻ sample, sausageCharge κ (γ sample) v (ball 0 R) ∂P) ≤ C := by
  obtain ⟨A,K,hA,hK,hbound⟩ := sausage_point_bound κ hκ
  let p := codimension κ
  have hp : p < 1 := by dsimp [p,codimension,dimension]; linarith [hκ.1]
  let D := ∫⁻ w in regionBand R 0 R, ENNReal.ofReal (w.im^(-p))
  have hD : D < ⊤ := height_kernel_finite R p hR.le hp
  let Z := ENNReal.ofReal (2*R*(A+1))+ENNReal.ofReal K*D
  have hZ : Z ≠ ⊤ := (ENNReal.add_lt_top.2
    ⟨ENNReal.ofReal_lt_top,ENNReal.mul_lt_top ENNReal.ofReal_lt_top hD⟩).ne
  refine ⟨Z.toNNReal,?_⟩
  intro Ω _ P _ γ hγ v hv hv1
  rw [ENNReal.coe_toNNReal hZ]
  change (∫⁻ sample, ENNReal.ofReal (v^(-p))*volume (ball 0 R ∩ sausage (γ sample) v) ∂P) ≤ Z
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply (mul_le_mul_right (expected_sausage_area_bound hR hA hK hbound P γ hγ v hv) _).trans
  change ENNReal.ofReal (v^(-p)) *
    (ENNReal.ofReal (2*R)*ENNReal.ofReal ((A+1)*v)+ENNReal.ofReal (K*v^p)*D) ≤ Z
  rw [mul_add]
  apply add_le_add
  · rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 2*R),← ENNReal.ofReal_mul (Real.rpow_nonneg hv.le _)]
    apply ENNReal.ofReal_le_ofReal
    have hh : v^(-p)*v ≤ 1 := by
      have he : v^(-p)*v = v^(-p+1) := by
        simpa only [Real.rpow_one] using (Real.rpow_add hv (-p) 1).symm
      rw [he]
      exact Real.rpow_le_one hv.le hv1 (by linarith)
    calc
      v^(-p)*(2*R*((A+1)*v)) = (2*R*(A+1))*(v^(-p)*v) := by ring
      _ ≤ (2*R*(A+1))*1 := mul_le_mul_of_nonneg_left hh (by positivity)
      _ = 2*R*(A+1) := mul_one _
  · have he : v^(-p)*(K*v^p) = K := by
      calc
        v^(-p)*(K*v^p) = K*(v^(-p)*v^p) := by ring
        _ = K := by rw [← Real.rpow_add hv,neg_add_cancel,Real.rpow_zero,mul_one]
    rw [← mul_assoc,← ENNReal.ofReal_mul (Real.rpow_nonneg hv.le _),he]

end SLEExactGauge

end

end

end

end

end

end

end

end

end

end

end

end

end

end

end

end

end

end

end

end

end

end

end

end

end

end

end OAI
