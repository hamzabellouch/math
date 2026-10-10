import Mathlib
import OAI.Probability.SLELocalization.ConditionalAngles
import OAI.Probability.SLE.ClippedCoordinates
import OAI.Probability.SLE.IntegralLimits
import OAI.Probability.SLE.ItoIsometry
import OAI.Probability.SLE.StochasticIntegrals

namespace OAI


/-! Conformal localization and Physical Past estimates. -/

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory TopologicalSpace
open scoped Topology NNReal ENNReal unitInterval
namespace SLEExactGauge.PhysicalPast

def sampleTime (T : ℝ≥0) (q : I) : ℝ≥0 := T * ⟨q,q.property.1⟩

lemma sampleTime_le (T : ℝ≥0) (q : I) : sampleTime T q ≤ T := by
  change (T:ℝ)*(q:ℝ) ≤ T
  simpa using mul_le_mul_of_nonneg_left q.property.2 T.coe_nonneg

lemma uniform_margin_iff {F : I → ℝ} (hF : Continuous F) (ε : ℝ) :
    (∃ m : ℕ, ∀ n : ℕ, ε + CanonicalTrace.height m ≤ F (denseSeq I n)) ↔
      ∀ q : I, ε < F q := by
  constructor
  · rintro ⟨m,hm⟩ q
    have hh : ε + CanonicalTrace.height m ≤ F q :=
      (denseRange_denseSeq I).induction_on q (isClosed_le continuous_const hF) hm
    linarith [CanonicalTrace.height_pos m]
  · intro hh
    obtain ⟨q,hq,hmin⟩ := isCompact_univ.exists_isMinOn (univ_nonempty : (univ : Set I).Nonempty) hF.continuousOn
    obtain ⟨m,hm⟩ := exists_nat_one_div_lt (sub_pos.2 (hh q))
    refine ⟨m,fun n => ?_⟩
    have hb := hmin (mem_univ (denseSeq I n))
    change F q ≤ F (denseSeq I n) at hb
    dsimp [CanonicalTrace.height]
    linarith

def avoids {Ω : Type*} (κ : ℝ) (B : ℝ≥0 → Ω → ℝ) (z : ℂ) (ε : ℝ)
    (T : ℝ≥0) : Set Ω :=
  {sample | ∃ m : ℕ, ∀ n : ℕ, ε + CanonicalTrace.height m ≤
    dist z (CanonicalTrace.value κ B (sampleTime T (denseSeq I n)) sample)}

lemma avoids_measurable_past {Ω : Type*} [MeasurableSpace Ω]
    (κ : ℝ) (B : ℝ≥0 → Ω → ℝ) (z : ℂ) (ε : ℝ) (T : ℝ≥0) :
    @MeasurableSet Ω (BrownianPredictable.pastSigma B T) (avoids κ B z ε T) := by
  let : MeasurableSpace Ω := BrownianPredictable.pastSigma B T
  simp only [avoids,ofPred_exists,ofPred_forall]
  apply MeasurableSet.iUnion
  intro m
  apply MeasurableSet.iInter
  intro n
  apply measurableSet_le measurable_const
  exact measurable_const.dist ((CanonicalTrace.measurable_past κ B _).mono
    (BrownianPredictable.pastSigma_mono B (sampleTime_le T (denseSeq I n))) le_rfl)

lemma avoids_nullMeasurable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (κ : ℝ) {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (z : ℂ) (ε : ℝ) (T : ℝ≥0) : NullMeasurableSet (avoids κ B z ε T) P := by
  simp only [avoids,ofPred_exists,ofPred_forall]
  apply NullMeasurableSet.iUnion
  intro m
  apply NullMeasurableSet.iInter
  intro n
  exact nullMeasurableSet_le aemeasurable_const
    (aemeasurable_const.dist (CanonicalTrace.aemeasurable κ hB _))

lemma avoids_eq_source {Ω : Type*} (κ : ℝ) (B : ℝ≥0 → Ω → ℝ) (sample : Ω)
    {γ : ℝ → ℂ} {g f : ℝ → ℂ → ℂ}
    (h : IsLoewnerTraceUsing (fun t => Real.sqrt κ * B t.toNNReal sample) γ g f)
    (hc : Continuous (fun t => B t sample)) (z : ℂ) (ε : ℝ) (T : ℝ≥0) :
    sample ∈ avoids κ B z ε T ↔ ∀ s : ℝ≥0, s ≤ T → ε < dist z (γ s) := by
  have he : (sample ∈ avoids κ B z ε T) ↔
      ∃ m : ℕ, ∀ n : ℕ, ε + CanonicalTrace.height m ≤ dist z (γ (sampleTime T (denseSeq I n))) := by
    simp only [avoids,mem_ofPred_eq,CanonicalTrace.eq_source κ B sample h hc]
  rw [he]
  have hcont : Continuous (fun q : I => dist z (γ (sampleTime T q))) :=
    continuous_const.dist (h.1.comp_continuous (continuous_const.mul continuous_subtype_val)
      (fun q => mul_nonneg T.coe_nonneg q.property.1))
  rw [uniform_margin_iff hcont ε]
  constructor
  · intro hh s hs
    by_cases hT : T = 0
    · have hs0 : s=0 := by simpa only [hT,le_zero_iff] using hs
      have hzero : sampleTime T (0:I) = 0 := by
        apply NNReal.coe_injective
        change (T:ℝ) * (0:ℝ) = 0
        exact mul_zero _
      simpa only [hzero,hs0,NNReal.coe_zero] using hh (0:I)
    · have hTp : 0 < (T:ℝ) := lt_of_le_of_ne T.coe_nonneg (by exact_mod_cast Ne.symm hT)
      let q : I := ⟨(s:ℝ)/(T:ℝ),⟨div_nonneg s.coe_nonneg T.coe_nonneg,
        (div_le_one hTp).2 hs⟩⟩
      have hsq : sampleTime T q = s := by
        apply NNReal.coe_injective
        change (T:ℝ)*((s:ℝ)/(T:ℝ)) = s
        field_simp
      simpa only [hsq] using hh q
  · intro hh q
    exact hh _ (sampleTime_le T q)

end SLEExactGauge.PhysicalPast

end

end

section
noncomputable section
open Set Filter Metric
open scoped Topology NNReal
namespace SLEExactGauge

lemma closedBall_subset_survivingDomain {γ : ℝ → ℂ} {t : ℝ} {z : ℂ} {r : ℝ}
    (hr : 0 ≤ r) (hz : z ∈ localizationDomain γ t)
    (hfree : closedBall z r ⊆ halfPlane \ localizationSegment γ 0 t) :
    closedBall z r ⊆ localizationDomain γ t := by
  have hc := (convex_closedBall z r).isPreconnected.subset_connectedComponentIn
    (mem_closedBall_self hr) hfree
  intro w hw
  refine ⟨hfree hw,?_⟩
  rw [← connectedComponentIn_eq (hc hw)]
  exact hz.2

end SLEExactGauge

end

end

section
noncomputable section
open Set Filter Metric
open scoped Topology NNReal
namespace SLEExactGauge
namespace IsLoewnerTraceUsing
variable {driver : ℝ → ℝ} {γ : ℝ → ℂ} {g f : ℝ → ℂ → ℂ}

lemma radius_ge_half_free_ball (h : IsLoewnerTraceUsing driver γ g f)
    {t : ℝ} (ht : 0 ≤ t) {z : ℂ} {r : ℝ} (hr : 0 < r)
    (hz : z ∈ localizationDomain γ t) (hball : closedBall z r ⊆ localizationDomain γ t) :
    r/2 ≤ loewnerRadius g t z := by
  let y := (g t z).im
  have hy : 0 < y := h.im_pos ht hz
  let F : ℂ → ℂ := fun w => (g t w - (starRingEnd ℂ) (g t z))⁻¹
  have hden (w : ℂ) (hw : w ∈ localizationDomain γ t) :
      y ≤ ‖g t w - (starRingEnd ℂ) (g t z)‖ := by
    have hp := h.im_pos ht hw
    have hh := Complex.im_le_norm (g t w - (starRingEnd ℂ) (g t z))
    simp only [Complex.sub_im,Complex.conj_im] at hh
    dsimp [y]
    linarith
  have hn (w : ℂ) (hw : w ∈ localizationDomain γ t) : g t w-(starRingEnd ℂ) (g t z) ≠ 0 :=
    norm_pos_iff.1 (hy.trans_le (hden w hw))
  have hd (w : ℂ) (hw : w ∈ localizationDomain γ t) : DifferentiableAt ℂ F w :=
    ((h.analytic_eval ht hw).differentiableAt.sub_const _).inv (hn w hw)
  have hF : DiffContOnCl ℂ F (ball z r) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball _ hr.ne']
    exact fun w hw => (hd w (hball hw)).differentiableWithinAt
  have hb : ∀ w ∈ sphere z r, ‖F w‖ ≤ 1/y := by
    intro w hw
    change ‖(g t w - (starRingEnd ℂ) (g t z))⁻¹‖ ≤ 1/y
    rw [norm_inv,one_div]
    exact inv_anti₀ hy (hden w (hball (sphere_subset_closedBall hw)))
  have hc := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr hF hb
  have hdF : HasDerivAt F (-deriv (g t) z / (g t z-(starRingEnd ℂ) (g t z))^2) z := by
    exact ((h.analytic_eval ht hz).differentiableAt.hasDerivAt.sub_const _).inv (hn z hz)
  have hnorm : ‖g t z-(starRingEnd ℂ) (g t z)‖ = 2*y := by
    rw [Complex.sub_conj,norm_mul,Complex.norm_real,Real.norm_eq_abs,Complex.norm_I,mul_one]
    exact abs_of_pos (by dsimp [y] at hy ⊢; positivity)
  rw [hdF.deriv,norm_div,norm_neg,norm_pow,hnorm] at hc
  have hdn := norm_pos_iff.2 (h.deriv_ne_zero ht hz)
  change r/2 ≤ 2*y/‖deriv (g t) z‖
  rw [le_div_iff₀ hdn]
  have hh := (div_le_iff₀ (sq_pos_of_pos (by positivity : 0 < 2*y))).1 hc
  have hh' : ‖deriv (g t) z‖ * r ≤ 4*y := by
    have hrr := (mul_le_mul_of_nonneg_right hh hr.le)
    field_simp at hrr
    nlinarith
  nlinarith

end IsLoewnerTraceUsing

end SLEExactGauge

end

end

section
noncomputable section
open Set Filter Metric
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

def firstLiveDistanceStop (γ : ℝ → ℂ) (z : ℂ) (ε : ℝ) : ℝ≥0∞ :=
  sInf ((fun t : ℝ≥0 => (t : ℝ≥0∞)) ''
    {t : ℝ≥0 | z ∈ localizationDomain γ t ∧ dist z (γ t) ≤ ε})

def physicalStoppedDensity (κ : ℝ) (B : ℝ≥0 → ℝ)
    (γ : ℝ → ℂ) (g : ℝ → ℂ → ℂ) (z : ℂ) (ε : ℝ) : ℝ≥0∞ :=
  let τ := firstLiveDistanceStop γ z ε
  if τ = ⊤ then 0 else
    ENNReal.ofReal ((loewnerRadius g τ.toReal z)^(-codimension κ) *
      (loewnerAngleSine κ B g τ.toReal z)^(8/κ-1))

end SLEExactGauge

end

end

section
noncomputable section
open Set Filter Metric
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
namespace PhysicalStop
variable {γ : ℝ → ℂ} {z : ℂ} {ε : ℝ}

lemma le_of_hit {t : ℝ≥0} (hz : z ∈ localizationDomain γ t) (hd : dist z (γ t) ≤ ε) :
    firstLiveDistanceStop γ z ε ≤ (t:ℝ≥0∞) :=
  sInf_le ⟨t,⟨hz,hd⟩,rfl⟩

lemma eq_top_iff : firstLiveDistanceStop γ z ε = ⊤ ↔
    ∀ t : ℝ≥0, z ∈ localizationDomain γ t → ε < dist z (γ t) := by
  constructor
  · intro he t hz
    by_contra hn
    have hh := le_of_hit hz (not_lt.1 hn)
    rw [he] at hh
    exact ENNReal.coe_ne_top (top_le_iff.1 hh)
  · intro hn
    have he : {t : ℝ≥0 | z ∈ localizationDomain γ t ∧ dist z (γ t) ≤ ε} = ∅ := by
      exact Set.eq_empty_iff_forall_notMem.2 (fun t ht => (not_lt_of_ge ht.2) (hn t ht.1))
    simp only [firstLiveDistanceStop,he,image_empty,sInf_empty]

lemma finite_spec (hγ : ContinuousOn γ (Ici 0))
    (hfin : firstLiveDistanceStop γ z ε ≠ ⊤) :
    ∃ t : ℝ≥0, firstLiveDistanceStop γ z ε = (t:ℝ≥0∞) ∧
      z ∈ localizationDomain γ t ∧ dist z (γ t) ≤ ε ∧
      ∀ s : ℝ≥0, s < t → ε < dist z (γ s) := by
  have hex : ∃ T : ℝ≥0, z ∈ localizationDomain γ T ∧ dist z (γ T) ≤ ε := by
    by_contra hn
    push Not at hn
    exact hfin (eq_top_iff.2 hn)
  obtain ⟨T,hTlive,hTdist⟩ := hex
  have hc : Continuous (fun s : ℝ≥0 => dist z (γ s)) :=
    continuous_const.dist (hγ.comp_continuous continuous_subtype_val (fun s => s.coe_nonneg))
  let A : Set ℝ≥0 := Icc 0 T ∩ {s | dist z (γ s) ≤ ε}
  have hA : IsCompact A := isCompact_Icc.inter_right (isClosed_le hc continuous_const)
  obtain ⟨t,ht,hmin⟩ := hA.exists_isLeast ⟨T,⟨⟨zero_le,le_rfl⟩,hTdist⟩⟩
  have htlive : z ∈ localizationDomain γ t := survivingDomain_mono ht.1.2 hTlive
  have hleast (s : ℝ≥0) (hs : z ∈ localizationDomain γ s ∧ dist z (γ s) ≤ ε) : t ≤ s := by
    by_cases hsT : s ≤ T
    · exact hmin ⟨⟨zero_le,hsT⟩,hs.2⟩
    · exact ht.1.2.trans (le_of_not_ge hsT)
  have he : firstLiveDistanceStop γ z ε = (t:ℝ≥0∞) := by
    apply le_antisymm (le_of_hit htlive ht.2)
    apply le_sInf
    rintro _ ⟨s,hs,rfl⟩
    exact ENNReal.coe_le_coe.2 (hleast s hs)
  refine ⟨t,he,htlive,ht.2,?_⟩
  intro s hs
  by_contra hn
  exact (not_le_of_gt hs) (hleast s ⟨survivingDomain_mono hs.le htlive,not_lt.1 hn⟩)

lemma lt_stop_distance {t : ℝ≥0} (ht : (t:ℝ≥0∞) < firstLiveDistanceStop γ z ε)
    (hlive : z ∈ localizationDomain γ t) : ε < dist z (γ t) := by
  by_contra hn
  exact (not_le_of_gt ht) (le_of_hit hlive (not_lt.1 hn))

lemma stopped_survival_iff (hγ : ContinuousOn γ (Ici 0)) {t : ℝ≥0}
    (hlive : z ∈ localizationDomain γ t) :
    (t:ℝ≥0∞) < firstLiveDistanceStop γ z ε ↔
      ∀ s : ℝ≥0, s ≤ t → ε < dist z (γ s) := by
  constructor
  · intro ht s hs
    exact lt_stop_distance ((ENNReal.coe_le_coe.2 hs).trans_lt ht) (survivingDomain_mono hs hlive)
  · intro hh
    by_contra hn
    have he : firstLiveDistanceStop γ z ε ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.coe_ne_top (not_lt.1 hn)
    obtain ⟨s,hs,hslive,hsdist,hmin⟩ := finite_spec hγ he
    rw [hs] at hn
    have hst : s ≤ t := ENNReal.coe_le_coe.1 (not_lt.1 hn)
    exact (not_lt_of_ge hsdist) (hh s hst)

lemma finite_dist_eq (hγ : ContinuousOn γ (Ici 0))
    (hinit : ε < dist z (γ 0)) (hfin : firstLiveDistanceStop γ z ε ≠ ⊤) :
    dist z (γ (firstLiveDistanceStop γ z ε).toReal) = ε := by
  obtain ⟨t,he,hlive,hdist,hmin⟩ := finite_spec hγ hfin
  rw [he,ENNReal.coe_toReal]
  apply le_antisymm hdist
  by_contra hn
  have hlt : dist z (γ t) < ε := not_le.1 hn
  have hc : ContinuousOn (fun s : ℝ => dist z (γ s)) (Icc 0 (t:ℝ)) :=
    (continuous_const.dist continuous_id).comp_continuousOn (hγ.mono Icc_subset_Ici_self)
  obtain ⟨s,hs,hseq⟩ := intermediate_value_Icc' t.coe_nonneg hc ⟨hlt.le,hinit.le⟩
  have hst : s < (t:ℝ) := lt_of_le_of_ne hs.2 (by intro hst; subst s; linarith)
  have hh := hmin ⟨s,hs.1⟩ hst
  exact (not_lt_of_ge hseq.le) hh

lemma trace_distance_ge_before (hγ : ContinuousOn γ (Ici 0))
    (hinit : ε < dist z (γ 0)) {t : ℝ≥0}
    (ht : (t:ℝ≥0∞) ≤ firstLiveDistanceStop γ z ε)
    (hlive : z ∈ localizationDomain γ t) {s : ℝ} (hs : s ∈ Icc 0 (t:ℝ)) :
    ε ≤ dist z (γ s) := by
  rcases lt_or_eq_of_le ((ENNReal.coe_le_coe.2 (show (⟨s,hs.1⟩:ℝ≥0) ≤ t from hs.2)).trans ht) with hlt | he
  · exact (lt_stop_distance hlt (survivingDomain_mono hs.2 hlive)).le
  · have hfin : firstLiveDistanceStop γ z ε ≠ ⊤ := he ▸ ENNReal.coe_ne_top
    have hh := finite_dist_eq hγ hinit hfin
    rw [← he] at hh
    change dist z (γ s) = ε at hh
    exact hh.symm.le

end PhysicalStop

end SLEExactGauge

end

end

section
noncomputable section
open Set Filter Metric
open scoped Topology NNReal ENNReal
namespace SLEExactGauge.IsLoewnerTraceUsing
open Set Metric
variable {driver : ℝ → ℝ} {γ : ℝ → ℂ} {g f : ℝ → ℂ → ℂ}

lemma radius_ge_before_distance_stop (h : IsLoewnerTraceUsing driver γ g f)
    {z : ℂ} {ε : ℝ} (hε : 0 < ε) (hsmall : ε < z.im) {t : ℝ≥0}
    (ht : (t:ℝ≥0∞) ≤ firstLiveDistanceStop γ z ε) (hlive : z ∈ localizationDomain γ t) :
    ε/4 ≤ loewnerRadius g t z := by
  have hinit : ε < dist z (γ 0) := by
    rw [h.2.1,dist_zero_right]
    exact hsmall.trans_le (Complex.im_le_norm z)
  have hdist (s : ℝ) (hs : s ∈ Icc 0 (t:ℝ)) : ε ≤ dist z (γ s) :=
    PhysicalStop.trace_distance_ge_before h.1 hinit ht hlive hs
  have hfree : closedBall z (ε/2) ⊆ halfPlane \ localizationSegment γ 0 t := by
    intro w hw
    have hnorm : ‖w-z‖ ≤ ε/2 := by simpa only [mem_closedBall,dist_eq_norm] using hw
    constructor
    · have hh := Complex.abs_im_le_norm (w-z)
      have hn := neg_abs_le (w-z).im
      change 0 < w.im
      simp only [Complex.sub_im] at hh hn
      linarith
    · rintro ⟨s,hs,rfl⟩
      have hh := hdist s hs
      have hh' := mem_closedBall.1 hw
      rw [dist_comm] at hh'
      linarith
  have hb := closedBall_subset_survivingDomain (by linarith : 0 ≤ ε/2) hlive hfree
  have hh := h.radius_ge_half_free_ball t.coe_nonneg (by linarith : 0 < ε/2) hlive hb
  convert hh using 1
  ring

end SLEExactGauge.IsLoewnerTraceUsing

end

end

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal unitInterval
namespace SLEExactGauge.PhysicalStop

def cap (tauE : ℝ≥0∞) (a : ℝ) : ℝ := if tauE = ⊤ then a else min tauE.toReal a

lemma cap_bounds (tauE : ℝ≥0∞) {a : ℝ} (ha : 0 ≤ a) : 0 ≤ cap tauE a ∧ cap tauE a ≤ a := by
  unfold cap
  split_ifs
  · exact ⟨ha,le_rfl⟩
  · exact ⟨le_min ENNReal.toReal_nonneg ha,min_le_right _ _⟩

lemma lt_cap (tauE : ℝ≥0∞) (a : ℝ) (s : ℝ≥0) :
    (s:ℝ) < cap tauE a ↔ (s:ℝ) < a ∧ (s:ℝ≥0∞) < tauE := by
  by_cases htauE : tauE = ⊤
  · simp [cap,htauE]
  · rw [cap,ite_eq_right htauE,lt_min_iff,and_comm]
    apply and_congr_right
    intro _
    simpa only [ENNReal.coe_toReal] using ENNReal.toReal_lt_toReal (a := (s:ℝ≥0∞)) ENNReal.coe_ne_top htauE

lemma cap_coe {t : ℝ≥0} {a : ℝ} (hta : (t:ℝ) ≤ a) : cap (t:ℝ≥0∞) a = t := by
  simp only [cap,ite_eq_right ENNReal.coe_ne_top,ENNReal.coe_toReal,min_eq_left hta]

end SLEExactGauge.PhysicalStop

end

end

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal unitInterval
namespace SLEExactGauge.BrownianField.FieldRegular

lemma restrict {F V : ℝ → ℝ → ℝ} {b : ℝ → ℝ} {s t : ℝ}
    (h : FieldRegular F V b t) (hst : s ≤ t) : FieldRegular F V b s := by
  refine ⟨h.smooth,h.third_bound,?_,?_,?_,?_⟩
  · exact fun x => (h.time_cont x).mono (Icc_subset_Icc le_rfl hst)
  · exact fun r hr => h.time_deriv r ⟨hr.1,hr.2.trans_le hst⟩
  · exact h.drift_cont.mono (prod_mono (Icc_subset_Icc le_rfl hst) (Icc_subset_Icc le_rfl hst))
  · exact h.second_cont.mono (Icc_subset_Icc le_rfl hst)

end SLEExactGauge.BrownianField.FieldRegular

end

end

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal unitInterval
namespace SLEExactGauge.LoewnerLocalized
open LoewnerCutoff LoewnerField LoewnerExit

lemma integral_drift_cancel_before {ε T : ℝ} (hε : 0 < ε) (hT : 0 < T) (κ : ℝ) (hκ : 0 < κ)
    (U : C(I, ℝ)) (z : ℂ) (ρ δ : ℝ) (b : ℝ → ℝ)
    (hU : ∀ s ∈ Icc 0 T, extendDriver T U s = Real.sqrt κ * b s)
    {τ : ℝ} (hτ0 : 0 ≤ τ) (hτ : τ ≤ stop hε hT.le U z ρ δ) :
    (∫ t in (0:ℝ)..τ, drift hε hT.le (1-κ/8) (8/κ-1) (Real.sqrt κ) U z t (b t)) +
      (1/2 : ℝ)*∫ t in (0:ℝ)..τ,
        iteratedDeriv 2 (field hε hT.le (1-κ/8) (8/κ-1) (Real.sqrt κ) U z t) (b t) = 0 := by
  have he : (∫ t in (0:ℝ)..τ, drift hε hT.le (1-κ/8) (8/κ-1) (Real.sqrt κ) U z t (b t)) =
      ∫ t in (0:ℝ)..τ,
        -(1/2 : ℝ)*iteratedDeriv 2 (field hε hT.le (1-κ/8) (8/κ-1) (Real.sqrt κ) U z t) (b t) := by
    apply intervalIntegral.integral_congr_Ioo_of_le hτ0
    intro t ht
    have htT : t ∈ Icc 0 T := ⟨ht.1.le,ht.2.le.trans (hτ.trans (stop_bounds hε hT.le U z ρ δ).2)⟩
    have hh := (deficit_pos_iff hε hT.le U z ρ δ t).1
      (positive_before hε hT.le hT U z ρ δ ht.1.le (ht.2.trans_le hτ))
    have hc := drift_cancellation hε hT.le κ hκ U z t (b t) hh.2.1.le (hU t htT)
    linarith
  rw [he, intervalIntegral.integral_const_mul]
  ring

end SLEExactGauge.LoewnerLocalized

end

end

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal unitInterval
namespace SLEExactGauge.FiniteTilt.Cutoff
open LoewnerCutoff LoewnerField LoewnerExit LoewnerLocalized GreenPhysical
variable {z : ℂ} {u : ℝ} (C : Cutoff z u)

def physicalTime {Ω : Type*} (κ : ℝ) (B : ℝ≥0 → Ω → ℝ) (γ : Ω → ℝ → ℂ) (ε : ℝ) (sample : Ω) : ℝ :=
  PhysicalStop.cap (firstLiveDistanceStop (γ sample) z ε) (C.stopTime κ B sample)

def physicalValue {Ω : Type*} (κ : ℝ) (B : ℝ≥0 → Ω → ℝ) (γ : Ω → ℝ → ℂ) (ε : ℝ) (sample : Ω) : ℝ :=
  field C.height_pos C.horizon.coe_nonneg (1-κ/8) (8/κ-1) (Real.sqrt κ) (C.paths κ B sample) z
    (C.physicalTime κ B γ ε sample) (B (C.physicalTime κ B γ ε sample).toNNReal sample)

lemma physicalTime_bounds {Ω : Type*} (κ : ℝ) (B : ℝ≥0 → Ω → ℝ) (γ : Ω → ℝ → ℂ) (ε : ℝ) (sample : Ω) :
    0 ≤ C.physicalTime κ B γ ε sample ∧ C.physicalTime κ B γ ε sample ≤ C.stopTime κ B sample :=
  PhysicalStop.cap_bounds _ (C.bounds κ B sample).1

lemma physicalValue_nonneg {Ω : Type*} (κ : ℝ) (B : ℝ≥0 → Ω → ℝ) (γ : Ω → ℝ → ℂ) (ε : ℝ) (sample : Ω) :
    0 ≤ C.physicalValue κ B γ ε sample := (green_pos _ _ _ _ _).le

lemma physicalValue_bound {Ω : Type*} (κ : ℝ) (hκ : 0 < κ ∧ κ < 8)
    (B : ℝ≥0 → Ω → ℝ) (γ : Ω → ℝ → ℂ) (ε : ℝ) (sample : Ω) (hz : z ∈ halfPlane) (hu : 0 < u)
    (hc : Continuous (fun t => B t sample)) (hb0 : B 0 sample = 0) :
    C.physicalValue κ B γ ε sample ≤ ((2*z.im)*Real.exp (-u))^(-(1-κ/8)) := by
  have hy0 : 0 < z.im := hz
  have hp : 0 ≤ 1-κ/8 := by linarith [hκ.2]
  have ha : 0 ≤ 8/κ-1 := by
    have hh : (1:ℝ) ≤ 8/κ := (le_div_iff₀ hκ.1).2 (by simpa using hκ.2.le)
    linarith
  have h0 := C.initial_deficit_brownian κ B sample hz hu hc hb0
  have hd := (deficit_nonneg_iff C.height_pos C.horizon.coe_nonneg _ z _ C.angle _).1
    (nonneg_until C.height_pos C.horizon.coe_nonneg C.horizon_pos _ z _ C.angle h0
      (C.physicalTime_bounds κ B γ ε sample))
  apply green_le_fixed_radius _ _ _ _ _ _ (LoewnerField.height_pos _ _ _ _ _) ha hp (by positivity)
  simpa only [LoewnerExit.radius,LoewnerField.height,max_eq_right hd.2.1] using hd.1

def physicalCoeff {Ω : Type*} (k : ℕ) (κ : ℝ) (B : ℝ≥0 → Ω → ℝ) (ε : ℝ) (s : ℝ≥0) (sample : Ω) : ℝ :=
  by
  classical
  exact if sample ∈ PhysicalPast.avoids κ B z ε s then
    rawCoeff C.height_pos k B C.horizon s (1-κ/8) (8/κ-1) (Real.sqrt κ) z ((2*z.im)*Real.exp (-u)) C.angle sample
  else 0

lemma physicalCoeff_measurable_past {Ω : Type*} [MeasurableSpace Ω]
    (k : ℕ) (hk : k=1 ∨ k=2) (κ : ℝ) (B : ℝ≥0 → Ω → ℝ) (ε : ℝ) (s : ℝ≥0) :
    Measurable[BrownianPredictable.pastSigma B s] (C.physicalCoeff k κ B ε s) := by
  classical
  exact (rawCoeff_measurable_past C.height_pos k hk B C.horizon s _ _ _ _ _ _).ite
    (PhysicalPast.avoids_measurable_past κ B z ε s) measurable_const

lemma physicalCoeff_aemeasurable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (k : ℕ) (hk : k=1 ∨ k=2) (κ : ℝ) (ε : ℝ) (s : ℝ≥0) :
    AEMeasurable (C.physicalCoeff k κ B ε s) P := by
  classical
  exact (rawCoeff_aemeasurable C.height_pos hB k hk C.horizon s _ _ _ _ _ _).indicator₀
    (PhysicalPast.avoids_nullMeasurable κ hB z ε s)

lemma physicalCoeff_eq {Ω : Type*} (κ : ℝ) (B : ℝ≥0 → Ω → ℝ) (γ : Ω → ℝ → ℂ)
    (g f : Ω → ℝ → ℂ → ℂ) (sample : Ω)
    (h : IsLoewnerTraceUsing (fun t => Real.sqrt κ*B t.toNNReal sample) (γ sample) (g sample) (f sample))
    (hc : Continuous (fun t => B t sample)) (hb0 : B 0 sample = 0)
    (hz : z ∈ halfPlane) (hu : 0 < u) (ε : ℝ) (k : ℕ) (s : ℝ≥0) :
    C.physicalCoeff k κ B ε s sample =
      if (s:ℝ) < C.physicalTime κ B γ ε sample then
        iteratedDeriv k (field C.height_pos C.horizon.coe_nonneg (1-κ/8) (8/κ-1) (Real.sqrt κ)
          (C.paths κ B sample) z s) (B s sample) else 0 := by
  classical
  have he := rawCoeff_eq C.height_pos k B C.horizon s C.horizon_pos (1-κ/8) (8/κ-1)
    (Real.sqrt κ) z ((2*z.im)*Real.exp (-u)) C.angle sample hc
  change rawCoeff _ _ _ _ _ _ _ _ _ _ _ _ =
    (if (s:ℝ) < C.stopTime κ B sample then _ else 0) at he
  have ht := PhysicalStop.lt_cap (firstLiveDistanceStop (γ sample) z ε) (C.stopTime κ B sample) s
  change ((s:ℝ) < C.physicalTime κ B γ ε sample) ↔ _ at ht
  by_cases hs : (s:ℝ) < C.stopTime κ B sample
  · have hlive := survivingDomain_mono hs.le (C.source_live κ B sample h hz hu hc hb0)
    have hav := (PhysicalPast.avoids_eq_source κ B sample h hc z ε s).trans
      (PhysicalStop.stopped_survival_iff h.1 hlive).symm
    simp only [physicalCoeff,he,hav,ht,hs,ite_true,true_and,paths]
  · have hcap : ¬ (s:ℝ) < C.physicalTime κ B γ ε sample := fun hh => hs (ht.1 hh).1
    simp only [physicalCoeff,he,ite_eq_right hs,ite_eq_right hcap,ite_self]

end SLEExactGauge.FiniteTilt.Cutoff

end

end

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal unitInterval
namespace SLEExactGauge.FiniteTilt.Cutoff
open LoewnerCutoff LoewnerField LoewnerExit LoewnerLocalized GreenPhysical
open BrownianPredictable BrownianStopped BrownianIto TaylorMeshes
variable {z : ℂ} {u : ℝ} (C : Cutoff z u)

theorem physical_centered {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ}
    (hB : IsBrownianReal B P) (κ : ℝ) (hκ : 0 < κ ∧ κ < 8)
    (γ : Ω → ℝ → ℂ) (g f : Ω → ℝ → ℂ → ℂ)
    (hmaps : ∀ᵐ sample ∂P, IsLoewnerTraceUsing
      (fun t => Real.sqrt κ * B t.toNNReal sample) (γ sample) (g sample) (f sample))
    (hz : z ∈ halfPlane) (hu : 0 < u) (ε : ℝ) :
    let F := fun sample => field C.height_pos C.horizon.coe_nonneg (1-κ/8) (8/κ-1) (Real.sqrt κ) (C.paths κ B sample) z
    Integrable (fun sample => C.physicalValue κ B γ ε sample - F sample 0 (B 0 sample)) P ∧
      (∫ sample, C.physicalValue κ B γ ε sample - F sample 0 (B 0 sample) ∂P) = 0 := by
  let T := C.horizon
  let hT := C.horizon_pos
  let hε := C.height_pos
  let ρ := (2*z.im)*Real.exp (-u)
  let δ := C.angle
  let U := C.paths κ B
  let τ := C.physicalTime κ B γ ε
  let F := fun sample => field hε T.coe_nonneg (1-κ/8) (8/κ-1) (Real.sqrt κ) (U sample) z
  let V := fun sample => drift hε T.coe_nonneg (1-κ/8) (8/κ-1) (Real.sqrt κ) (U sample) z
  have hp : 0 ≤ 1-κ/8 := by linarith [hκ.2]
  have ha : 0 ≤ 8/κ-1 := by
    have hh : (1:ℝ) ≤ 8/κ := (le_div_iff₀ hκ.1).2 (by simpa using hκ.2.le)
    linarith
  have hreg : ∀ᵐ sample ∂P, BrownianField.FieldRegular (F sample) (V sample)
      (fun t => B t.toNNReal sample) (τ sample) := by
    filter_upwards [hB.cont] with sample hc
    exact (regular hε hT (1-κ/8) (8/κ-1) (Real.sqrt κ) hp ha (U sample) z ρ δ _
      (hc.comp continuous_real_toNNReal)).restrict (C.physicalTime_bounds κ B γ ε sample).2
  have htau : ∀ᵐ sample ∂P, 0 ≤ τ sample ∧ τ sample ≤ T :=
    Filter.Eventually.of_forall (fun sample => ⟨(C.physicalTime_bounds κ B γ ε sample).1,
      (C.physicalTime_bounds κ B γ ε sample).2.trans (C.bounds κ B sample).2⟩)
  obtain ⟨K₁,hK₁,hb₁⟩ := coeff_uniform_bound hε T.coe_nonneg 1 (Or.inl rfl)
    (1-κ/8) (8/κ-1) (Real.sqrt κ) hp ha z
  obtain ⟨K₂,hK₂,hb₂⟩ := coeff_uniform_bound hε T.coe_nonneg 2 (Or.inr rfl)
    (1-κ/8) (8/κ-1) (Real.sqrt κ) hp ha z
  have hsbound (k : ℕ) (K : ℝ) (hK : 0 ≤ K)
      (hb : ∀ (W : C(I, ℝ)) (t b : ℝ),
        |iteratedDeriv k (field hε T.coe_nonneg (1-κ/8) (8/κ-1) (Real.sqrt κ) W z t) b| ≤ K)
      (n i : ℕ) : ∀ᵐ sample ∂P, |stoppedCoeff k B T τ F n i sample| ≤ K := by
    apply Filter.Eventually.of_forall
    intro sample
    unfold stoppedCoeff
    split_ifs
    · exact hb _ _ _
    · simpa only [abs_zero] using hK
  let A := fun n i => C.physicalCoeff 1 κ B ε (dyadicTime T n i)
  let Q := fun n i => C.physicalCoeff 2 κ B ε (dyadicTime T n i)
  have hAe (n i : ℕ) : A n i =ᵐ[P] stoppedCoeff 1 B T τ F n i := by
    filter_upwards [hB.cont,hB.toIsPreBrownianReal.eval_zero_ae_eq_zero,hmaps] with sample hc hb0 h
    simpa only [A,stoppedCoeff,coe_dyadicTime] using
      C.physicalCoeff_eq κ B γ g f sample h hc hb0 hz hu ε 1 (dyadicTime T n i)
  have hCe (n i : ℕ) : Q n i =ᵐ[P] stoppedCoeff 2 B T τ F n i := by
    filter_upwards [hB.cont,hB.toIsPreBrownianReal.eval_zero_ae_eq_zero,hmaps] with sample hc hb0 h
    simpa only [Q,stoppedCoeff,coe_dyadicTime] using
      C.physicalCoeff_eq κ B γ g f sample h hc hb0 hz hu ε 2 (dyadicTime T n i)
  have hAm (n i : ℕ) : Measurable[pastSigma B (dyadicTime T n i)] (A n i) :=
    C.physicalCoeff_measurable_past 1 (Or.inl rfl) κ B ε _
  have hCm (n i : ℕ) : Measurable[pastSigma B (dyadicTime T n i)] (Q n i) :=
    C.physicalCoeff_measurable_past 2 (Or.inr rfl) κ B ε _
  have hA2 (n i : ℕ) : MemLp (A n i) 2 P := by
    apply MemLp.of_bound (C.physicalCoeff_aemeasurable hB 1 (Or.inl rfl) κ ε _).aestronglyMeasurable K₁
    filter_upwards [hAe n i, hsbound 1 K₁ hK₁ hb₁ n i] with sample he hb
    rw [Real.norm_eq_abs]
    change |A n i sample| ≤ K₁
    rw [he]
    exact hb
  have hC2 (n i : ℕ) : MemLp (Q n i) 2 P := by
    apply MemLp.of_bound (C.physicalCoeff_aemeasurable hB 2 (Or.inr rfl) κ ε _).aestronglyMeasurable K₂
    filter_upwards [hCe n i, hsbound 2 K₂ hK₂ hb₂ n i] with sample he hb
    rw [Real.norm_eq_abs]
    change |Q n i sample| ≤ K₂
    rw [he]
    exact hb
  have hi := stopped_field_ito_centered_ae hB T τ F V htau hreg A Q hAe hCe hCm hC2
    K₂ hK₂ (hsbound 2 K₂ hK₂ hb₂) hAm hA2 K₁ hK₁ (hsbound 1 K₁ hK₁ hb₁)
  have he : (fun sample => F sample (τ sample) (B (τ sample).toNNReal sample) - F sample 0 (B 0 sample) -
      (∫ t in (0:ℝ)..(τ sample), V sample t (B t.toNNReal sample)) -
      (1/2:ℝ)*∫ t in (0:ℝ)..(τ sample), iteratedDeriv 2 (F sample t) (B t.toNNReal sample)) =ᵐ[P]
      (fun sample => F sample (τ sample) (B (τ sample).toNNReal sample) - F sample 0 (B 0 sample)) := by
    filter_upwards [hB.cont] with sample hc
    have hcanc := integral_drift_cancel_before hε hT κ hκ.1 (U sample) z ρ δ
      (fun t => B t.toNNReal sample) (fun t ht => BrownianDriver.extend_eq B _ T sample hc ht)
      (C.physicalTime_bounds κ B γ ε sample).1 (C.physicalTime_bounds κ B γ ε sample).2
    dsimp only [F,V,τ]
    linarith
  exact ⟨hi.1.congr he, (integral_congr_ae he).symm.trans hi.2⟩

theorem physical_expectation {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ}
    (hB : IsBrownianReal B P) (κ : ℝ) (hκ : 0 < κ ∧ κ < 8)
    (γ : Ω → ℝ → ℂ) (g f : Ω → ℝ → ℂ → ℂ)
    (hmaps : ∀ᵐ sample ∂P, IsLoewnerTraceUsing
      (fun t => Real.sqrt κ * B t.toNNReal sample) (γ sample) (g sample) (f sample))
    (hz : z ∈ halfPlane) (hu : 0 < u) (ε : ℝ) :
    Integrable (C.physicalValue κ B γ ε) P ∧
      (∫ sample, C.physicalValue κ B γ ε sample ∂P) = green (1-κ/8) (8/κ-1) z.re z.im 0 := by
  let F := fun sample => field C.height_pos C.horizon.coe_nonneg (1-κ/8) (8/κ-1) (Real.sqrt κ) (C.paths κ B sample) z
  let M := C.physicalValue κ B γ ε
  let G := green (1-κ/8) (8/κ-1) z.re z.im 0
  have hi := C.physical_centered hB κ hκ γ g f hmaps hz hu ε
  have he : (fun sample => M sample - F sample 0 (B 0 sample)) =ᵐ[P]
      (fun sample => M sample - G) := by
    filter_upwards [hB.toIsPreBrownianReal.eval_zero_ae_eq_zero] with sample hb
    rw [hb]
    congr 1
    exact field_initial C.height_pos C.horizon.coe_nonneg _ _ _ _ z (C.height_initial hz hu.le).le
  have hd : Integrable (fun sample => M sample-G) P := hi.1.congr he
  have hv : (∫ sample, M sample-G ∂P) = 0 := (integral_congr_ae he).symm.trans hi.2
  have hm : Integrable M P := by
    exact (hd.add (integrable_const G)).congr
      (Filter.Eventually.of_forall (fun sample => sub_add_cancel (M sample) G))
  refine ⟨hm, ?_⟩
  have hh := integral_sub hm (integrable_const (μ := P) G)
  simp only [integral_const, Measure.real, measure_univ, ENNReal.toReal_one, one_smul] at hh
  rw [hh] at hv
  change (∫ sample, M sample ∂P) = G
  linarith

end SLEExactGauge.FiniteTilt.Cutoff

end

end

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal unitInterval
namespace SLEExactGauge.FiniteTilt.Cutoff
open LoewnerCutoff LoewnerField LoewnerExit LoewnerLocalized GreenPhysical
open BrownianPredictable BrownianStopped BrownianIto TaylorMeshes PredictableLimit
variable {z : ℂ} {u : ℝ} (C : Cutoff z u)

theorem physical_sum_tendsto {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ}
    (hB : IsBrownianReal B P) (κ : ℝ) (hκ : 0 < κ ∧ κ < 8)
    (γ : Ω → ℝ → ℂ) (g f : Ω → ℝ → ℂ → ℂ)
    (hmaps : ∀ᵐ sample ∂P, IsLoewnerTraceUsing
      (fun t => Real.sqrt κ * B t.toNNReal sample) (γ sample) (g sample) (f sample))
    (hz : z ∈ halfPlane) (hu : 0 < u) (ε : ℝ) :
    let F := fun sample => field C.height_pos C.horizon.coe_nonneg (1-κ/8) (8/κ-1)
      (Real.sqrt κ) (C.paths κ B sample) z
    ∀ᵐ sample ∂P, Tendsto (fun n => dyadicDriverSum B C.horizon
      (fun n i => C.physicalCoeff 1 κ B ε (dyadicTime C.horizon n i)) n sample) atTop
      (𝓝 (C.physicalValue κ B γ ε sample-F sample 0 (B 0 sample))) := by
  let T := C.horizon
  let hT := C.horizon_pos
  let hε := C.height_pos
  let ρ := (2*z.im)*Real.exp (-u)
  let δ := C.angle
  let U := C.paths κ B
  let τ := C.physicalTime κ B γ ε
  let F := fun sample => field hε T.coe_nonneg (1-κ/8) (8/κ-1) (Real.sqrt κ) (U sample) z
  let V := fun sample => drift hε T.coe_nonneg (1-κ/8) (8/κ-1) (Real.sqrt κ) (U sample) z
  have hp : 0 ≤ 1-κ/8 := by linarith [hκ.2]
  have ha : 0 ≤ 8/κ-1 := by
    have hh : (1:ℝ) ≤ 8/κ := (le_div_iff₀ hκ.1).2 (by simpa using hκ.2.le)
    linarith
  have hreg : ∀ᵐ sample ∂P, BrownianField.FieldRegular (F sample) (V sample)
      (fun t => B t.toNNReal sample) (τ sample) := by
    filter_upwards [hB.cont] with sample hc
    exact (regular hε hT (1-κ/8) (8/κ-1) (Real.sqrt κ) hp ha (U sample) z ρ δ _
      (hc.comp continuous_real_toNNReal)).restrict (C.physicalTime_bounds κ B γ ε sample).2
  have htau : ∀ᵐ sample ∂P, 0 ≤ τ sample ∧ τ sample ≤ T :=
    Filter.Eventually.of_forall (fun sample => ⟨(C.physicalTime_bounds κ B γ ε sample).1,
      (C.physicalTime_bounds κ B γ ε sample).2.trans (C.bounds κ B sample).2⟩)
  obtain ⟨K₁,hK₁,hb₁⟩ := coeff_uniform_bound hε T.coe_nonneg 1 (Or.inl rfl)
    (1-κ/8) (8/κ-1) (Real.sqrt κ) hp ha z
  obtain ⟨K₂,hK₂,hb₂⟩ := coeff_uniform_bound hε T.coe_nonneg 2 (Or.inr rfl)
    (1-κ/8) (8/κ-1) (Real.sqrt κ) hp ha z
  have hsbound (k : ℕ) (K : ℝ) (hK : 0 ≤ K)
      (hb : ∀ (W : C(I, ℝ)) (t b : ℝ),
        |iteratedDeriv k (field hε T.coe_nonneg (1-κ/8) (8/κ-1) (Real.sqrt κ) W z t) b| ≤ K)
      (n i : ℕ) : ∀ᵐ sample ∂P, |stoppedCoeff k B T τ F n i sample| ≤ K := by
    apply Filter.Eventually.of_forall
    intro sample
    unfold stoppedCoeff
    split_ifs
    · exact hb _ _ _
    · simpa only [abs_zero] using hK
  let A := fun n i => C.physicalCoeff 1 κ B ε (dyadicTime T n i)
  let Q := fun n i => C.physicalCoeff 2 κ B ε (dyadicTime T n i)
  have hAe (n i : ℕ) : A n i =ᵐ[P] stoppedCoeff 1 B T τ F n i := by
    filter_upwards [hB.cont,hB.toIsPreBrownianReal.eval_zero_ae_eq_zero,hmaps] with sample hc hb0 h
    simpa only [A,stoppedCoeff,coe_dyadicTime] using
      C.physicalCoeff_eq κ B γ g f sample h hc hb0 hz hu ε 1 (dyadicTime T n i)
  have hCe (n i : ℕ) : Q n i =ᵐ[P] stoppedCoeff 2 B T τ F n i := by
    filter_upwards [hB.cont,hB.toIsPreBrownianReal.eval_zero_ae_eq_zero,hmaps] with sample hc hb0 h
    simpa only [Q,stoppedCoeff,coe_dyadicTime] using
      C.physicalCoeff_eq κ B γ g f sample h hc hb0 hz hu ε 2 (dyadicTime T n i)
  have hAm (n i : ℕ) : Measurable[pastSigma B (dyadicTime T n i)] (A n i) :=
    C.physicalCoeff_measurable_past 1 (Or.inl rfl) κ B ε _
  have hCm (n i : ℕ) : Measurable[pastSigma B (dyadicTime T n i)] (Q n i) :=
    C.physicalCoeff_measurable_past 2 (Or.inr rfl) κ B ε _
  have hA2 (n i : ℕ) : MemLp (A n i) 2 P := by
    apply MemLp.of_bound (C.physicalCoeff_aemeasurable hB 1 (Or.inl rfl) κ ε _).aestronglyMeasurable K₁
    filter_upwards [hAe n i, hsbound 1 K₁ hK₁ hb₁ n i] with sample he hb
    rw [Real.norm_eq_abs]
    change |A n i sample| ≤ K₁
    rw [he]
    exact hb
  have hC2 (n i : ℕ) : MemLp (Q n i) 2 P := by
    apply MemLp.of_bound (C.physicalCoeff_aemeasurable hB 2 (Or.inr rfl) κ ε _).aestronglyMeasurable K₂
    filter_upwards [hCe n i, hsbound 2 K₂ hK₂ hb₂ n i] with sample he hb
    rw [Real.norm_eq_abs]
    change |Q n i sample| ≤ K₂
    rw [he]
    exact hb
  have hi := stopped_fieldSum_tendsto_ae hB T τ F V htau hreg Q hCe hCm hC2
    K₂ hK₂ (hsbound 2 K₂ hK₂ hb₂) K₁ hK₁ (hsbound 1 K₁ hK₁ hb₁)
  have he : (fun sample => F sample (τ sample) (B (τ sample).toNNReal sample) - F sample 0 (B 0 sample) -
      (∫ t in (0:ℝ)..(τ sample), V sample t (B t.toNNReal sample)) -
      (1/2:ℝ)*∫ t in (0:ℝ)..(τ sample), iteratedDeriv 2 (F sample t) (B t.toNNReal sample)) =ᵐ[P]
      (fun sample => F sample (τ sample) (B (τ sample).toNNReal sample) - F sample 0 (B 0 sample)) := by
    filter_upwards [hB.cont] with sample hc
    have hcanc := integral_drift_cancel_before hε hT κ hκ.1 (U sample) z ρ δ
      (fun t => B t.toNNReal sample) (fun t ht => BrownianDriver.extend_eq B _ T sample hc ht)
      (C.physicalTime_bounds κ B γ ε sample).1 (C.physicalTime_bounds κ B γ ε sample).2
    dsimp only [F,V,τ]
    linarith
  have hAeall : ∀ᵐ sample ∂P, ∀ n i, A n i sample = stoppedCoeff 1 B T τ F n i sample :=
    ae_all_iff.2 (fun n => ae_all_iff.2 (hAe n))
  filter_upwards [hi,he,hAeall] with sample hi he ha
  rw [he] at hi
  convert hi using 1
  · funext n
    unfold dyadicDriverSum
    simp only [← ha]
    rfl
  · rfl

end SLEExactGauge.FiniteTilt.Cutoff

end

end

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge.BrownianPredictable
open PredictableLimit

lemma delayed_indicator_difference_centered {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ}
    (hB : IsBrownianReal B P) (T S : ℝ≥0)
    (A D : ℕ → ℕ → Ω → ℝ)
    (hA : ∀ n i, Measurable[pastSigma B (dyadicTime T n i)] (A n i))
    (hD : ∀ n i, Measurable[pastSigma B (dyadicTime T n i)] (D n i))
    (hA2 : ∀ n i, MemLp (A n i) 2 P) (hD2 : ∀ n i, MemLp (D n i) 2 P)
    (K : ℝ) (hK : 0 ≤ K)
    (hbA : ∀ n i, ∀ᵐ sample ∂P, |A n i sample| ≤ K)
    (hbD : ∀ n i, ∀ᵐ sample ∂P, |D n i sample| ≤ K)
    (E : Set Ω) (hE : NullMeasurableSet E P)
    (hEm : MeasurableSet[pastSigma B S] E)
    (hsupport : ∀ n i, dyadicTime T n i < S → ∀ᵐ sample ∂P,
      sample ∈ E → A n i sample = D n i sample)
    (YA YD : Ω → ℝ)
    (hlA : ∀ᵐ sample ∂P, Tendsto (fun n => dyadicDriverSum B T A n sample) atTop (𝓝 (YA sample)))
    (hlD : ∀ᵐ sample ∂P, Tendsto (fun n => dyadicDriverSum B T D n sample) atTop (𝓝 (YD sample))) :
    Integrable (E.indicator (fun sample => YA sample-YD sample)) P ∧
      (∫ sample, E.indicator (fun sample => YA sample-YD sample) sample ∂P) = 0 := by
  classical
  let Q := fun n i => if S ≤ dyadicTime T n i then
    E.indicator (fun sample => A n i sample-D n i sample) else (fun _ => 0)
  have hQm (n i : ℕ) : Measurable[pastSigma B (dyadicTime T n i)] (Q n i) := by
    dsimp only [Q]
    split_ifs with ht
    · exact ((hA n i).sub (hD n i)).indicator (pastSigma_mono B ht _ hEm)
    · exact measurable_const
  have heq (n i : ℕ) : Q n i =ᵐ[P] E.indicator (fun sample => A n i sample-D n i sample) := by
    by_cases ht : S ≤ dyadicTime T n i
    · exact Filter.Eventually.of_forall (fun _ => by simp only [Q,ite_eq_left ht])
    · filter_upwards [hsupport n i (lt_of_not_ge ht)] with sample hs
      simp only [Q,ite_eq_right ht,Set.indicator_apply]
      split_ifs with hmem
      · simp only [hs hmem,sub_self]
      · rfl
  have hQ2 (n i : ℕ) : MemLp (Q n i) 2 P := by
    have hd := (hA2 n i).sub (hD2 n i)
    have hm : MemLp (E.indicator (fun sample => A n i sample-D n i sample)) 2 P :=
      hd.of_le (hd.aestronglyMeasurable.indicator₀ hE)
        (Filter.Eventually.of_forall (fun sample => norm_indicator_le_norm_self _ sample))
    exact hm.ae_eq (heq n i).symm
  have hQb (n i : ℕ) : ∀ᵐ sample ∂P, |Q n i sample| ≤ 2*K := by
    filter_upwards [hbA n i,hbD n i,heq n i] with sample ha hd he
    rw [he,Set.indicator_apply]
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
open scoped Topology NNReal ENNReal unitInterval
namespace SLEExactGauge.FiniteTilt.Cutoff
open LoewnerCutoff LoewnerField LoewnerExit LoewnerLocalized BrownianPredictable
  BrownianStopped BrownianIto TaylorMeshes PredictableLimit

lemma physical_avoidance_setIntegral {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ}
    (hB : IsBrownianReal B P) (κ : ℝ) (hκ : 0 < κ ∧ κ < 8)
    {z : ℂ} (hz : z ∈ halfPlane) {u : ℝ} (hu : 0 < u)
    (C : Cutoff z u) (γ : Ω → ℝ → ℂ) (g f : Ω → ℝ → ℂ → ℂ)
    (hmaps : ∀ᵐ sample ∂P, IsLoewnerTraceUsing
      (fun t => Real.sqrt κ*B t.toNNReal sample) (γ sample) (g sample) (f sample))
    (e : ℝ) (S : ℝ≥0) :
    (∫ sample in PhysicalPast.avoids κ B z e S, C.value κ B sample ∂P) =
      ∫ sample in PhysicalPast.avoids κ B z e S, C.physicalValue κ B γ e sample ∂P := by
  let F := fun sample => field C.height_pos C.horizon.coe_nonneg (1-κ/8) (8/κ-1)
    (Real.sqrt κ) (C.paths κ B sample) z
  let A := fun n i => rawCoeff C.height_pos 1 B C.horizon (dyadicTime C.horizon n i)
    (1-κ/8) (8/κ-1) (Real.sqrt κ) z ((2*z.im)*Real.exp (-u)) C.angle
  let D := fun n i => C.physicalCoeff 1 κ B e (dyadicTime C.horizon n i)
  have hAe (n i : ℕ) : A n i =ᵐ[P] stoppedCoeff 1 B C.horizon (C.stopTime κ B) F n i :=
    rawCoeff_stoppedCoeff_ae C.height_pos hB 1 C.horizon C.horizon_pos
      (1-κ/8) (8/κ-1) (Real.sqrt κ) z ((2*z.im)*Real.exp (-u)) C.angle n i
  have hp : 0 ≤ 1-κ/8 := by linarith [hκ.2]
  have ha : 0 ≤ 8/κ-1 := sub_nonneg.2 ((le_div_iff₀ hκ.1).2 (by linarith [hκ.2]))
  obtain ⟨K,hK,hKb⟩ := coeff_uniform_bound C.height_pos C.horizon.coe_nonneg 1 (Or.inl rfl)
    (1-κ/8) (8/κ-1) (Real.sqrt κ) hp ha z
  have hAb (n i : ℕ) : ∀ᵐ sample ∂P, |A n i sample| ≤ K := by
    filter_upwards [hAe n i] with sample he
    rw [he]
    unfold stoppedCoeff
    split_ifs
    · exact hKb _ _ _
    · simpa only [abs_zero] using hK
  have hDb (n i : ℕ) : ∀ᵐ sample ∂P, |D n i sample| ≤ K := by
    filter_upwards [hAb n i] with sample ha
    dsimp only [D,physicalCoeff]
    split_ifs
    · exact ha
    · simpa only [abs_zero] using hK
  have hAm (n i : ℕ) : Measurable[pastSigma B (dyadicTime C.horizon n i)] (A n i) :=
    rawCoeff_measurable_past C.height_pos 1 (Or.inl rfl) B C.horizon _ _ _ _ z _ C.angle
  have hDm (n i : ℕ) : Measurable[pastSigma B (dyadicTime C.horizon n i)] (D n i) :=
    C.physicalCoeff_measurable_past 1 (Or.inl rfl) κ B e _
  have hA2 (n i : ℕ) : MemLp (A n i) 2 P := by
    apply MemLp.of_bound (rawCoeff_aemeasurable C.height_pos hB 1 (Or.inl rfl) C.horizon
      (dyadicTime C.horizon n i) (1-κ/8) (8/κ-1) (Real.sqrt κ) z _ C.angle).aestronglyMeasurable K
    simpa only [Real.norm_eq_abs] using hAb n i
  have hD2 (n i : ℕ) : MemLp (D n i) 2 P := by
    apply MemLp.of_bound (C.physicalCoeff_aemeasurable hB 1 (Or.inl rfl) κ e _).aestronglyMeasurable K
    simpa only [Real.norm_eq_abs] using hDb n i
  have hsupport (n i : ℕ) (ht : dyadicTime C.horizon n i < S) : ∀ᵐ sample ∂P,
      sample ∈ PhysicalPast.avoids κ B z e S → A n i sample = D n i sample := by
    filter_upwards [hmaps,hB.cont] with sample hm hc he
    have hh := (PhysicalPast.avoids_eq_source κ B sample hm hc z e S).1 he
    have hs : sample ∈ PhysicalPast.avoids κ B z e (dyadicTime C.horizon n i) :=
      (PhysicalPast.avoids_eq_source κ B sample hm hc z e _).2 (fun s hs => hh s (hs.trans ht.le))
    simp only [D,physicalCoeff,ite_eq_left hs]
    rfl
  have hlA := localized_sum_tendsto hB κ hκ C.height_pos C.horizon C.horizon_pos z
    ((2*z.im)*Real.exp (-u)) C.angle
  have hlD := C.physical_sum_tendsto hB κ hκ γ g f hmaps hz hu e
  have hE := PhysicalPast.avoids_nullMeasurable κ hB z e S
  have hh := delayed_indicator_difference_centered hB C.horizon S A D hAm hDm hA2 hD2 K hK hAb hDb
    (PhysicalPast.avoids κ B z e S) hE (PhysicalPast.avoids_measurable_past κ B z e S) hsupport
    (fun sample => C.value κ B sample-F sample 0 (B 0 sample))
    (fun sample => C.physicalValue κ B γ e sample-F sample 0 (B 0 sample)) hlA hlD
  have hdiff : (∫ sample in PhysicalPast.avoids κ B z e S,
      C.value κ B sample-C.physicalValue κ B γ e sample ∂P) = 0 := by
    simpa only [sub_sub_sub_cancel_right,integral_indicator₀ hE] using hh.2
  rw [integral_sub ((C.expectation hB κ hκ hz hu.le).1.integrableOn)
    ((C.physical_expectation hB κ hκ γ g f hmaps hz hu e).1.integrableOn)] at hdiff
  exact sub_eq_zero.1 hdiff

end SLEExactGauge.FiniteTilt.Cutoff

end

end

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal unitInterval
namespace SLEExactGauge.FiniteTilt.Cutoff
open LoewnerCutoff LoewnerField LoewnerExit LoewnerLocalized GreenPhysical
variable {z : ℂ} {u : ℝ} (C : Cutoff z u)
variable {Ω : Type*} (κ : ℝ) (B : ℝ≥0 → Ω → ℝ) (γ : Ω → ℝ → ℂ)
variable (g f : Ω → ℝ → ℂ → ℂ) (sample : Ω)
variable (h : IsLoewnerTraceUsing (fun t => Real.sqrt κ*B t.toNNReal sample) (γ sample) (g sample) (f sample))
variable (hz : z ∈ halfPlane) (hu : 0 < u)
variable (hc : Continuous (fun t => B t sample)) (hb0 : B 0 sample = 0)
include h hz hu hc hb0

lemma physicalValue_eq_source (ε : ℝ) : C.physicalValue κ B γ ε sample =
    (loewnerRadius (g sample) (C.physicalTime κ B γ ε sample) z)^(-(1-κ/8)) *
      (loewnerAngleSine κ (fun t => B t sample) (g sample) (C.physicalTime κ B γ ε sample) z)^(8/κ-1) := by
  have ht := C.physicalTime_bounds κ B γ ε sample
  have h0 := C.initial_deficit_brownian κ B sample hz hu hc hb0
  have hh := ((deficit_nonneg_iff C.height_pos C.horizon.coe_nonneg _ z _ C.angle _).1
    (nonneg_until C.height_pos C.horizon.coe_nonneg C.horizon_pos _ z _ C.angle h0 ht)).2.1
  have hr := radius_eq_source C.height_pos C.horizon_pos h
    ((continuous_const.mul (hc.comp continuous_real_toNNReal)).continuousOn) _ z _ C.angle
    (C.path_eq κ B sample hc) h0 ht
  have hs := sine_eq_source C.height_pos C.horizon_pos h _ z _ C.angle
    (C.path_eq κ B sample hc) h0 ht
  change _ = loewnerRadius (g sample) (C.physicalTime κ B γ ε sample) z at hr
  have hs' : sine C.height_pos C.horizon.coe_nonneg (C.paths κ B sample) z
      (C.physicalTime κ B γ ε sample) =
      loewnerAngleSine κ (fun t => B t sample) (g sample) (C.physicalTime κ B γ ε sample) z := by
    simpa only [loewnerAngleSine,Complex.ofReal_mul] using hs
  rw [physicalValue,field_eq_radius_sine C.height_pos C.horizon_pos _ _ _ _ z _ _ hh
    (C.path_eq κ B sample hc ⟨ht.1,ht.2.trans (C.bounds κ B sample).2⟩),hr,hs']

end SLEExactGauge.FiniteTilt.Cutoff

end

end

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal unitInterval
namespace SLEExactGauge.FiniteTilt
variable {Ω : Type*} (κ : ℝ) (B : ℝ≥0 → Ω → ℝ) (γ : Ω → ℝ → ℂ)
variable (g f : Ω → ℝ → ℂ → ℂ) (sample : Ω)
variable (h : IsLoewnerTraceUsing (fun t => Real.sqrt κ*B t.toNNReal sample) (γ sample) (g sample) (f sample))
variable {z : ℂ} (hz : z ∈ halfPlane) {u : ℝ} (hu : 0 < u)
variable (hc : Continuous (fun t => B t sample)) (hb0 : B 0 sample = 0)
variable {ε : ℝ} (hε : 0 < ε) (hsmall : ε < z.im)
variable (hρ : (2*z.im)*Real.exp (-u) < ε/4)
include h hz hu hc hb0 hε hsmall hρ

lemma eventually_physicalValue_at_hit (hfin : firstLiveDistanceStop (γ sample) z ε ≠ ⊤) :
    ∀ᶠ n : ℕ in atTop, ENNReal.ofReal ((cutoffs hz u hu.le n).physicalValue κ B γ ε sample) =
      physicalStoppedDensity κ (fun t => B t sample) (γ sample) (g sample) z ε := by
  obtain ⟨t,ht,hzt,hd,hmin⟩ := PhysicalStop.finite_spec h.1 hfin
  obtain ⟨η,hη,hm⟩ := h.sine_positive_minimum (κ := κ) (B := fun t => B t sample) hc t.coe_nonneg hzt
  have hδ : ∀ᶠ n : ℕ in atTop, shrinkingAngle z n < η :=
    (shrinkingAngle_tendsto z).eventually (gt_mem_nhds hη)
  filter_upwards [hδ] with n hn
  let C := cutoffs hz u hu.le n
  have htc : (t:ℝ) ≤ C.stopTime κ B sample := by
    by_contra hnot
    have hlt : C.stopTime κ B sample < t := lt_of_not_ge hnot
    rcases C.source_terminal κ B sample h hz hu hc hb0 with hr | hs
    · have hh := h.radius_ge_before_distance_stop hε hsmall
        (t := ⟨C.stopTime κ B sample,(C.bounds κ B sample).1⟩)
        (by rw [ht]; exact ENNReal.coe_le_coe.2 hlt.le)
        (C.source_live κ B sample h hz hu hc hb0)
      change ε/4 ≤ loewnerRadius (g sample) (C.stopTime κ B sample) z at hh
      rw [hr] at hh
      exact (not_lt_of_ge hh) hρ
    · have hh := hm (C.stopTime κ B sample) ⟨(C.bounds κ B sample).1,hlt.le⟩
      rw [hs] at hh
      exact (not_lt_of_ge hh) hn
  have he : C.physicalTime κ B γ ε sample = t := by
    rw [Cutoff.physicalTime,ht,PhysicalStop.cap_coe htc]
  have hp : codimension κ = 1-κ/8 := by unfold codimension dimension; ring
  rw [physicalStoppedDensity,ht,ite_eq_right ENNReal.coe_ne_top,ENNReal.coe_toReal,hp,
    C.physicalValue_eq_source κ B γ g f sample h hz hu hc hb0 ε,he]

lemma tendsto_physicalValue_killed (hκ : 0 < κ ∧ κ < 8) :
    Tendsto (fun n : ℕ => ENNReal.ofReal ((cutoffs hz u hu.le n).physicalValue κ B γ ε sample)) atTop
      (𝓝 (physicalStoppedDensity κ (fun t => B t sample) (γ sample) (g sample) z ε)) := by
  by_cases he : firstLiveDistanceStop (γ sample) z ε = ⊤
  · rw [physicalStoppedDensity,he,ite_eq_left rfl]
    have ha : 0 < 8/κ-1 := sub_pos.2 ((lt_div_iff₀ hκ.1).2 (by simpa using hκ.2))
    have hlim := (shrinkingAngle_tendsto z).rpow_const_nhds_zero ha
    have hlim' : Tendsto (fun n : ℕ => ((2*z.im)*Real.exp (-u))^(-(1-κ/8)) *
        (shrinkingAngle z n)^(8/κ-1)) atTop (𝓝 0) := by
      simpa only [mul_zero] using tendsto_const_nhds.mul hlim
    have hl : Tendsto (fun n : ℕ => (cutoffs hz u hu.le n).physicalValue κ B γ ε sample) atTop (𝓝 0) := by
      apply squeeze_zero (fun n => (cutoffs hz u hu.le n).physicalValue_nonneg κ B γ ε sample) _ hlim'
      intro n
      let C := cutoffs hz u hu.le n
      have ht : C.physicalTime κ B γ ε sample = C.stopTime κ B sample := by
        simp only [Cutoff.physicalTime,PhysicalStop.cap,he,ite_true]
      have hv : C.physicalValue κ B γ ε sample = C.value κ B sample := by
        simp only [Cutoff.physicalValue,ht,Cutoff.value]
      rw [hv]
      have hs : loewnerAngleSine κ (fun t => B t sample) (g sample) (C.stopTime κ B sample) z = C.angle := by
        rcases C.source_terminal κ B sample h hz hu hc hb0 with hr | hs
        · have hh := h.radius_ge_before_distance_stop hε hsmall
            (t := ⟨C.stopTime κ B sample,(C.bounds κ B sample).1⟩)
            (by rw [he]; exact le_top) (C.source_live κ B sample h hz hu hc hb0)
          change ε/4 ≤ loewnerRadius (g sample) (C.stopTime κ B sample) z at hh
          rw [hr] at hh
          exact False.elim ((not_lt_of_ge hh) hρ)
        · exact hs
      exact C.angle_exit_bound κ B sample h hz hu hc hb0 hκ hs
    simpa only [ENNReal.ofReal_zero,Function.comp_def] using ENNReal.continuous_ofReal.continuousAt.tendsto.comp hl
  · have hh := eventually_physicalValue_at_hit κ B γ g f sample h hz hu hc hb0 hε hsmall hρ he
    exact tendsto_const_nhds.congr' (hh.mono (fun _ heq => heq.symm))

end SLEExactGauge.FiniteTilt

end

end

end OAI
