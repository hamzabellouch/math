import Mathlib
import OAI.Analysis.CoulombIonization.RadialBounds.MomentumBall

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped BigOperators ContDiff

namespace CoulombAtom

def fermiRegion (ρ : Space → ℝ) : Set (Space × Space) :=
  {q | ‖q.2‖ < fermiRadius ρ q.1}

def fermiMeasure (ρ : Space → ℝ) : Measure (Space × Space) := volume.restrict (fermiRegion ρ)

lemma fermiRadius_measurable {ρ : Space → ℝ} (hm : Measurable ρ) : Measurable (fermiRadius ρ) := by
  unfold fermiRadius
  fun_prop

lemma fermiRegion_measurable {ρ : Space → ℝ} (hm : Measurable ρ) : MeasurableSet (fermiRegion ρ) :=
  measurableSet_lt measurable_snd.norm ((fermiRadius_measurable hm).comp measurable_fst)

lemma fermiMeasure_le (ρ : Space → ℝ) : fermiMeasure ρ ≤ volume := Measure.restrict_le_self

lemma fermiRegion_subset {ρ : Space → ℝ} (hn : ∀ z, 0 ≤ ρ z) {J : Set Space}
    (hs : Function.support ρ ⊆ J) {B : ℝ} (hb : ∀ z, ρ z ≤ B) :
    fermiRegion ρ ⊆ J ×ˢ closedBall 0 ((3*Real.pi^2*B)^(1/3 : ℝ)) := by
  intro q hq
  have hq' : ‖q.2‖ < fermiRadius ρ q.1 := hq
  have hz : ρ q.1 ≠ 0 := by
    intro hz
    simp only [fermiRadius,hz,mul_zero,Real.zero_rpow (by norm_num : (1/3 : ℝ) ≠ 0)] at hq'
    exact (not_lt_of_ge (norm_nonneg _)) hq'
  refine ⟨hs hz,?_⟩
  rw [mem_closedBall,dist_zero_right]
  apply hq'.le.trans
  exact Real.rpow_le_rpow (mul_nonneg (by positivity) (hn q.1))
    (mul_le_mul_of_nonneg_left (hb q.1) (by positivity)) (by norm_num)

lemma fermiMeasure_finite {ρ : Space → ℝ} (hn : ∀ z, 0 ≤ ρ z) {J : Set Space}
    (hJ : IsCompact J) (hs : Function.support ρ ⊆ J) {B : ℝ} (hb : ∀ z, ρ z ≤ B) :
    IsFiniteMeasure (fermiMeasure ρ) := by
  constructor
  rw [fermiMeasure,Measure.restrict_apply_univ]
  exact (measure_mono (fermiRegion_subset hn hs hb)).trans_lt
    (hJ.prod (isCompact_closedBall _ _)).measure_lt_top

lemma fermiMeasure_mem {ρ : Space → ℝ} (hm : Measurable ρ) (hn : ∀ z, 0 ≤ ρ z) {J : Set Space}
    (hs : Function.support ρ ⊆ J) {B : ℝ} (hb : ∀ z, ρ z ≤ B) :
    ∀ᵐ q ∂fermiMeasure ρ, q ∈ J ×ˢ closedBall 0 ((3*Real.pi^2*B)^(1/3 : ℝ)) :=
  (ae_restrict_mem (fermiRegion_measurable hm)).mono (fun _ hq => fermiRegion_subset hn hs hb hq)

lemma fermiMeasure_integral {ρ : Space → ℝ} (hm : Measurable ρ)
    {f : Space × Space → ℝ} (hf : Integrable f (fermiMeasure ρ)) :
    (∫ q, f q ∂fermiMeasure ρ) =
      ∫ z : Space, ∫ p : Space in ball 0 (fermiRadius ρ z), f (z,p) := by
  have hi : Integrable ((fermiRegion ρ).indicator f) :=
    (integrable_indicator_iff (fermiRegion_measurable hm)).2 hf
  rw [Measure.volume_eq_prod] at hi
  rw [fermiMeasure,← integral_indicator (fermiRegion_measurable hm),Measure.volume_eq_prod,integral_prod _ hi]
  apply integral_congr_ae
  filter_upwards [] with z
  rw [← integral_indicator measurableSet_ball]
  apply integral_congr_ae
  filter_upwards [] with p
  simp only [Set.indicator,fermiRegion,mem_ofPred_eq,mem_ball,dist_zero_right]
  rfl

lemma fermiMeasure_integrable_continuous {ρ : Space → ℝ} (hn : ∀ z, 0 ≤ ρ z)
    {J : Set Space} (hJ : IsCompact J) (hs : Function.support ρ ⊆ J) {B : ℝ}
    (hb : ∀ z, ρ z ≤ B) {f : Space × Space → ℝ} (hf : Continuous f) :
    Integrable f (fermiMeasure ρ) :=
  (hf.continuousOn.integrableOn_compact (hJ.prod (isCompact_closedBall _ _))).mono_set
    (fermiRegion_subset hn hs hb)

lemma fermiMeasure_mass {ρ : Space → ℝ} (hm : Measurable ρ) (hn : ∀ z, 0 ≤ ρ z)
    {J : Set Space} (hJ : IsCompact J) (hs : Function.support ρ ⊆ J) {B : ℝ}
    (hb : ∀ z, ρ z ≤ B) :
    2*coherentFactor*(fermiMeasure ρ).real univ = ∫ z, ρ z := by
  have hi := fermiMeasure_integrable_continuous hn hJ hs hb (continuous_const : Continuous (fun _ : Space × Space => (1:ℝ)))
  have he := fermiMeasure_integral hm hi
  simp only [integral_const,smul_eq_mul,mul_one] at he
  rw [he,← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with z
  simpa only [Measure.real,Measure.restrict_apply_univ] using fermiRadius_ball_mass hn z

lemma fermiMeasure_kinetic {ρ : Space → ℝ} (hm : Measurable ρ) (hn : ∀ z, 0 ≤ ρ z)
    {J : Set Space} (hJ : IsCompact J) (hs : Function.support ρ ⊆ J) {B : ℝ}
    (hb : ∀ z, ρ z ≤ B) :
    coherentFactor*(∫ q, ‖q.2‖^2 ∂fermiMeasure ρ) = tfKinetic*∫ z, (ρ z)^(5/3 : ℝ) := by
  rw [fermiMeasure_integral hm (fermiMeasure_integrable_continuous hn hJ hs hb (by fun_prop)),
    ← integral_const_mul,← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with z
  exact fermiRadius_ball_kinetic hn z

end CoulombAtom

end

end OAI
