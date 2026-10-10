import OAI.MathematicalPhysics.Boltzmann.Approximation.PositiveSourceFormula
import OAI.MathematicalPhysics.Boltzmann.Branching.CharacteristicProductTest
import OAI.MathematicalPhysics.Boltzmann.Branching.CumulativeIntervalBalance
import OAI.MathematicalPhysics.Boltzmann.Branching.PublishedInputs
import OAI.MathematicalPhysics.Boltzmann.Compactness.KineticDensityMeasurable
import OAI.MathematicalPhysics.Boltzmann.Compactness.WeakL1Operations
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

namespace OAI

section

/-! # Almost-everywhere integrable prefixes imply integrability on smaller windows -/
noncomputable section
open MeasureTheory Set
namespace BoltzmannNonuniqueness.Published
variable {P : Type*} [MeasurableSpace P] {ν : Measure P} [SFinite ν]

theorem integrable_window_of_ae_prefix {T : ℝ} (hT : 0 ≤ T) {g : ℝ × P → ℝ}
    (h : ∀ᵐ z ∂(volume.restrict (Icc 0 (T+1))).prod ν,
      Integrable (fun s => if s ≤ z.1 then g (s,z.2) else 0) (volume.restrict (Icc 0 (T+1)))) :
    ∀ᵐ p ∂ν, Integrable (fun s => g (s,p)) (volume.restrict (Icc 0 T)) := by
  have hp := Measure.ae_ae_of_ae_prod (Measure.measurePreserving_swap.quasiMeasurePreserving.ae h)
  filter_upwards [hp] with p hpi
  have hs : Ioo T (T+1) ⊆ Icc 0 (T+1) := by
    intro t ht
    exact ⟨hT.trans ht.1.le,ht.2.le⟩
  have hpos : (volume : Measure ℝ) (Ioo T (T+1)) ≠ 0 := by
    rw [Real.volume_Ioo]
    norm_num
  have ht : ∀ᵐ t ∂volume.restrict (Ioo T (T+1)),
      Integrable (fun s => if s ≤ t then g (s,p) else 0) (volume.restrict (Icc 0 (T+1))) :=
    hpi.filter_mono (ae_mono (Measure.restrict_mono hs le_rfl))
  obtain ⟨t,ht,hint⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hpos ht
  have hsmall : Integrable (fun s => if s ≤ t then g (s,p) else 0)
      (volume.restrict (Icc 0 T)) :=
    hint.mono_measure (Measure.restrict_mono (Icc_subset_Icc le_rfl (by linarith)) le_rfl)
  apply hsmall.congr
  filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
  simp only [hs.2.trans ht.1.le,ite_true]

end BoltzmannNonuniqueness.Published

end

end

section

/-! # The time primitive on the common closed time interval -/

noncomputable section

open MeasureTheory Set Filter

namespace BoltzmannNonuniqueness.Published

variable {P : Type*} [MeasurableSpace P]

omit [MeasurableSpace P] in
theorem timePrimitive_eq_interval {T t : ℝ} (ht : t ∈ Icc 0 T)
    (f : ℝ × P → ℝ) (p : P) :
    timePrimitive (volume.restrict (Icc 0 T)) f (t,p) = ∫ s in 0..t, f (s,p) := by
  change (∫ s, (Iic t).indicator (fun s => f (s,p)) s ∂volume.restrict (Icc 0 T)) = _
  rw [integral_indicator measurableSet_Iic,Measure.restrict_restrict measurableSet_Iic]
  have he : Iic t ∩ Icc 0 T = Icc 0 t := by
    ext s
    simp only [mem_inter_iff,mem_Iic,mem_Icc]
    constructor
    · rintro ⟨hs,h0,_⟩; exact ⟨h0,hs⟩
    · rintro ⟨h0,hs⟩; exact ⟨hs,h0,hs.trans ht.2⟩
  rw [he,integral_Icc_eq_integral_Ioc,intervalIntegral.integral_of_le ht.1]

theorem timePrimitive_measurable (μ : Measure ℝ) [SFinite μ] {f : ℝ × P → ℝ}
    (hf : Measurable f) : Measurable (timePrimitive μ f) := by
  have hm : Measurable (fun z : (ℝ × P) × ℝ => if z.2 ≤ z.1.1 then f (z.2,z.1.2) else 0) :=
    (hf.comp (measurable_snd.prodMk measurable_fst.snd)).ite
      (measurableSet_le measurable_snd measurable_fst.fst) measurable_const
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

theorem timePrimitive_integrable {μ : Measure ℝ} {ν : Measure P}
    [IsFiniteMeasure μ] [SFinite ν] {f : ℝ × P → ℝ}
    (hfm : Measurable f) (hfi : Integrable f (μ.prod ν)) :
    Integrable (timePrimitive μ f) (μ.prod ν) := by
  have h : WeakL1Converges (μ.prod ν) (fun _ : ℕ => f) f :=
    ⟨hfm,hfi,fun _ _ _ => tendsto_const_nhds⟩
  exact (h.timePrimitive (fun _ => hfm) (fun _ => hfi)).2.1

end BoltzmannNonuniqueness.Published

end

end

section

/-! # Finite time measures obtained by testing characteristic phase -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.WeakTime

abbrev Phase := Velocity × Velocity

def timeSource (μ : Measure (ℝ × Phase)) (φ : Phase → ℝ) : Measure ℝ :=
  (positiveDensityMeasure μ (fun z => φ z.2)).map Prod.fst

theorem timeSource_finite (μ : Measure (ℝ × Phase)) [IsFiniteMeasure μ]
    {φ : Phase → ℝ} (hφ : Measurable φ) (hn : ∀ p, 0 ≤ φ p)
    {B : ℝ} (hB : ∀ p, |φ p| ≤ B) : IsFiniteMeasure (timeSource μ φ) := by
  have hi : Integrable (fun z : ℝ × Phase => φ z.2) μ :=
    (integrable_const B).mono' (hφ.comp measurable_snd).aestronglyMeasurable
      (ae_of_all _ (fun z => hB _))
  let _ := positiveDensityMeasure_finite hi (ae_of_all _ (fun z => hn z.2))
  unfold timeSource
  infer_instance

theorem timeSource_integral (μ : Measure (ℝ × Phase)) {φ : Phase → ℝ}
    (hφ : Measurable φ) (hn : ∀ p, 0 ≤ φ p) {θ : ℝ → ℝ} (hθ : Measurable θ) :
    (∫ t, θ t ∂timeSource μ φ) = ∫ z, θ z.1*φ z.2 ∂μ := by
  rw [timeSource,integral_map measurable_fst.aemeasurable hθ.aestronglyMeasurable]
  have hm : AEMeasurable (fun z : ℝ × Phase => φ z.2) μ :=
    (hφ.comp measurable_snd).aemeasurable
  exact positiveDensityMeasure_integral hm (ae_of_all _ (fun z => hn z.2)) (fun z => θ z.1)

def phaseProjection (F : ℝ × Phase → ℝ) (φ : Phase → ℝ) (t : ℝ) : ℝ :=
  ∫ p, φ p*F (t,p)

theorem phaseProjection_integrable {F : ℝ × Phase → ℝ}
    (hF : Integrable F (volume : Measure (ℝ × Phase))) {φ : Phase → ℝ}
    (hφ : Measurable φ) {B : ℝ} (hB : ∀ p, |φ p| ≤ B) :
    Integrable (phaseProjection F φ) := by
  have hi := hF.bdd_mul (hφ.comp measurable_snd).aestronglyMeasurable
    (ae_of_all _ (fun z => hB z.2))
  change Integrable (fun t => ∫ p, φ p*F (t,p))
  exact hi.integral_prod_left

theorem phaseProjection_test_integral {F : ℝ × Phase → ℝ}
    (hF : Integrable F (volume : Measure (ℝ × Phase))) {φ : Phase → ℝ}
    (hφ : Measurable φ) {B : ℝ} (hB : ∀ p, |φ p| ≤ B)
    {θ : ℝ → ℝ} (hθ : Measurable θ) {C : ℝ} (hC : ∀ t, |θ t| ≤ C) :
    (∫ t, θ t*phaseProjection F φ t) = ∫ z, (θ z.1*φ z.2)*F z := by
  have hi := hF.bdd_mul (hφ.comp measurable_snd).aestronglyMeasurable
    (ae_of_all _ (fun z => hB z.2))
  have hit := hi.bdd_mul (hθ.comp measurable_fst).aestronglyMeasurable
    (ae_of_all _ (fun z => hC z.1))
  change Integrable (fun z : ℝ × Phase => θ z.1*(φ z.2*F z))
    ((volume : Measure ℝ).prod volume) at hit
  have hip : Integrable (fun z : ℝ × Phase => (θ z.1*φ z.2)*F z)
      ((volume : Measure ℝ).prod volume) := by
    convert hit using 1
    funext z
    ring
  change (∫ t, θ t*phaseProjection F φ t) =
    ∫ z, (θ z.1*φ z.2)*F z ∂(volume : Measure ℝ).prod volume
  rw [integral_prod _ hip]
  apply integral_congr_ae
  exact ae_of_all _ (fun t => by
    simp only [phaseProjection]
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact ae_of_all _ (fun p => by ring))

end BoltzmannNonuniqueness.WeakTime

end

end

section

/-! # Measure-preserving time translations of kinetic half-lines and intervals -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness

theorem phaseHalfLine_measure (a : ℝ) :
    (volume.restrict (Ici a)).prod (volume : Measure Phase) =
      volume.restrict (Ici a ×ˢ (univ : Set Phase)) := by
  rw [Measure.restrict_prod_eq_prod_univ,← Measure.volume_eq_prod]

def timeTranslation (τ : ℝ) : (ℝ × Phase) ≃ᵐ (ℝ × Phase) :=
  (MeasurableEquiv.addRight τ).prodCongr (MeasurableEquiv.refl Phase)

@[simp] theorem timeTranslation_apply (τ : ℝ) (z : ℝ × Phase) :
    timeTranslation τ z = (z.1+τ,z.2) := rfl

theorem timeTranslation_halfLine (τ a : ℝ) :
    MeasurePreserving (timeTranslation τ)
      ((volume.restrict (Ici a)).prod (volume : Measure Phase))
      ((volume.restrict (Ici (a+τ))).prod (volume : Measure Phase)) := by
  have h := (measurePreserving_add_right (volume : Measure ℝ) τ).restrict_preimage
    (measurableSet_Ici : MeasurableSet (Ici (a+τ)))
  have he : (fun t : ℝ => t+τ) ⁻¹' Ici (a+τ) = Ici a := by
    ext t
    simp only [mem_preimage,mem_Ici]
    constructor <;> intro ht <;> linarith
  rw [he] at h
  exact h.prod (MeasurePreserving.id (volume : Measure Phase))

theorem timeTranslation_interval (τ a b : ℝ) :
    MeasurePreserving (timeTranslation τ)
      ((volume.restrict (Icc a b)).prod (volume : Measure Phase))
      ((volume.restrict (Icc (a+τ) (b+τ))).prod (volume : Measure Phase)) := by
  have h := (measurePreserving_add_right (volume : Measure ℝ) τ).restrict_preimage
    (measurableSet_Icc : MeasurableSet (Icc (a+τ) (b+τ)))
  have he : (fun t : ℝ => t+τ) ⁻¹' Icc (a+τ) (b+τ) = Icc a b := by
    ext t
    simp only [mem_preimage,mem_Icc]
    constructor <;> rintro ⟨h₁,h₂⟩ <;> constructor <;> linarith
  rw [he] at h
  exact h.prod (MeasurePreserving.id (volume : Measure Phase))

theorem integral_timeTranslation_halfLine (τ a : ℝ) (f : ℝ × Phase → ℝ) :
    (∫ z, f (z.1+τ,z.2) ∂(volume.restrict (Ici a)).prod volume) =
      ∫ z, f z ∂(volume.restrict (Ici (a+τ))).prod volume :=
  (timeTranslation_halfLine τ a).integral_comp (timeTranslation τ).measurableEmbedding f

theorem integral_timeTranslation_interval (τ a b : ℝ) (f : ℝ × Phase → ℝ) :
    (∫ z, f (z.1+τ,z.2) ∂(volume.restrict (Icc a b)).prod volume) =
      ∫ z, f z ∂(volume.restrict (Icc (a+τ) (b+τ))).prod volume :=
  (timeTranslation_interval τ a b).integral_comp (timeTranslation τ).measurableEmbedding f

end BoltzmannNonuniqueness

end

end

section

/-! # Strong L¹ continuity of the integrable time primitive -/

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace BoltzmannNonuniqueness.Published

variable {P : Type*} [MeasurableSpace P]

theorem timePrimitive_L1_continuous {ν : Measure P} [SFinite ν] {T : ℝ}
    (hT : 0 ≤ T) {f : ℝ × P → ℝ} (hfm : Measurable f)
    (hfi : Integrable f ((volume.restrict (Icc 0 T)).prod ν))
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    Tendsto (fun s => eLpNorm (fun p =>
      timePrimitive (volume.restrict (Icc 0 T)) f (s,p)-
        timePrimitive (volume.restrict (Icc 0 T)) f (t,p)) 1 ν)
      (𝓝[Icc 0 T] t) (𝓝 0) := by
  let μ : Measure ℝ := volume.restrict (Icc 0 T)
  let G : ℝ → P → ℝ := fun s p => timePrimitive μ f (s,p)
  let M : P → ℝ := fun p => ∫ s, ‖f (s,p)‖ ∂μ
  have hM : Integrable M ν := hfi.integral_norm_prod_right
  have hGm s : Measurable (G s) :=
    (timePrimitive_measurable μ hfm).comp (measurable_const.prodMk measurable_id)
  have hGb (s : ℝ) : ∀ᵐ p ∂ν, ‖G s p‖ ≤ M p := by
    filter_upwards [hfi.prod_left_ae] with p hp
    apply norm_integral_le_of_norm_le hp.norm
    filter_upwards [] with r
    change ‖if r ≤ s then f (r,p) else 0‖ ≤ ‖f (r,p)‖
    split <;> simp
  have hGi (s : ℝ) : Integrable (G s) ν :=
    hM.mono' (hGm s).aestronglyMeasurable (hGb s)
  have hbound (s : ℝ) : ∀ᵐ p ∂ν, ‖‖G s p-G t p‖‖ ≤ 2*M p := by
    filter_upwards [hGb s,hGb t] with p hs ht
    rw [norm_norm]
    exact (norm_sub_le _ _).trans (by linarith)
  have hpoint : ∀ᵐ p ∂ν,
      Tendsto (fun s => ‖G s p-G t p‖) (𝓝[Icc 0 T] t) (𝓝 (0 : ℝ)) := by
    filter_upwards [hfi.prod_left_ae] with p hp
    have hpI : IntervalIntegrable (fun r => f (r,p)) volume 0 T :=
      (intervalIntegrable_iff_integrableOn_Icc_of_le hT).mpr hp
    have hc := intervalIntegral.continuousOn_primitive_interval' hpI
      (left_mem_uIcc : (0 : ℝ) ∈ uIcc 0 T)
    rw [uIcc_of_le hT] at hc
    have hcG : ContinuousOn (fun s => G s p) (Icc 0 T) := hc.congr (fun s hs =>
      timePrimitive_eq_interval hs f p)
    simpa using ((hcG t ht).sub (continuousWithinAt_const (b := G t p))).norm.tendsto
  have hlim : Tendsto (fun s => ∫ p, ‖G s p-G t p‖ ∂ν) (𝓝[Icc 0 T] t) (𝓝 0) := by
    have h := tendsto_integral_filter_of_dominated_convergence (fun p => 2*M p)
      (Eventually.of_forall (fun s => ((hGm s).sub (hGm t)).norm.aestronglyMeasurable))
      (Eventually.of_forall hbound) (hM.const_mul 2) hpoint
    simpa using h
  have he s : eLpNorm (fun p => G s p-G t p) 1 ν =
      ENNReal.ofReal (∫ p, ‖G s p-G t p‖ ∂ν) := by
    exact (eLpNorm_one_eq_lintegral_enorm ((hGi s).sub (hGi t)).aestronglyMeasurable).trans
      (ofReal_integral_norm_eq_lintegral_enorm ((hGi s).sub (hGi t))).symm
  have h := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hlim
  simpa only [Function.comp_def,ENNReal.ofReal_zero,← he] using h

end BoltzmannNonuniqueness.Published

end

end

section

/-! # Integrating a local term pasted to a time-translated global term -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness

def timePaste (T : ℝ) (a b : ℝ × Phase → ℝ) (z : ℝ × Phase) : ℝ :=
  if z.1 ≤ T then a z else b (z.1-T,z.2)

theorem kinetic_halfLine_split {T : ℝ} (hT : 0 ≤ T) :
    (volume.restrict (Ici (0:ℝ))).prod (volume : Measure Phase) =
      (volume.restrict (Icc (0:ℝ) T)).prod (volume : Measure Phase)+
      (volume.restrict (Ici T)).prod (volume : Measure Phase) := by
  have hd : Disjoint (Icc (0:ℝ) T) (Ioi T) :=
    disjoint_left.mpr (fun _ hx hy => (not_lt_of_ge hx.2) hy)
  have h := (volume : Measure ℝ).restrict_union hd measurableSet_Ioi
  rw [Icc_union_Ioi_eq_Ici hT,Measure.restrict_congr_set Ioi_ae_eq_Ici] at h
  rw [h,Measure.add_prod]

theorem timePaste_left_ae (T : ℝ) (a b : ℝ × Phase → ℝ) :
    timePaste T a b =ᵐ[(volume.restrict (Icc (0:ℝ) T)).prod volume] a := by
  have ht : ∀ᵐ z : ℝ × Phase ∂(volume.restrict (Icc (0:ℝ) T)).prod volume, z.1 ∈ Icc 0 T :=
    Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Icc)
  filter_upwards [ht] with z hz
  exact ite_eq_left hz.2

theorem timePaste_right_ae (T : ℝ) (a b : ℝ × Phase → ℝ) :
    timePaste T a b =ᵐ[(volume.restrict (Ici T)).prod volume] (fun z => b (z.1-T,z.2)) := by
  have ht : ∀ᵐ z : ℝ × Phase ∂(volume.restrict (Ici T)).prod volume, z.1 ∈ Ici T :=
    Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Ici)
  have hn : ∀ᵐ z : ℝ × Phase ∂(volume.restrict (Ici T)).prod volume, z.1 ≠ T :=
    Measure.quasiMeasurePreserving_fst.ae (ae_restrict_of_ae (Measure.ae_ne (volume : Measure ℝ) T))
  filter_upwards [ht,hn] with z hz hn
  exact ite_eq_right (not_le_of_gt (lt_of_le_of_ne hz hn.symm))

theorem timePaste_integral {T : ℝ} (hT : 0 ≤ T) {a b : ℝ × Phase → ℝ}
    (ha : Integrable a ((volume.restrict (Icc (0:ℝ) T)).prod volume))
    (hb : Integrable b ((volume.restrict (Ici (0:ℝ))).prod volume)) :
    Integrable (timePaste T a b) ((volume.restrict (Ici (0:ℝ))).prod volume) ∧
      (∫ z, timePaste T a b z ∂(volume.restrict (Ici (0:ℝ))).prod volume) =
        (∫ z, a z ∂(volume.restrict (Icc (0:ℝ) T)).prod volume)+
          ∫ z, b z ∂(volume.restrict (Ici (0:ℝ))).prod volume := by
  have hm : MeasurePreserving (timeTranslation (-T))
      ((volume.restrict (Ici T)).prod (volume : Measure Phase))
      ((volume.restrict (Ici (0:ℝ))).prod (volume : Measure Phase)) := by
    simpa only [add_neg_cancel] using timeTranslation_halfLine (-T) T
  have hbi : Integrable (fun z : ℝ × Phase => b (z.1-T,z.2))
      ((volume.restrict (Ici T)).prod volume) := by
    simpa only [Function.comp_def,timeTranslation_apply,sub_eq_add_neg] using hm.integrable_comp_of_integrable hb
  have hi₁ := ha.congr (timePaste_left_ae T a b).symm
  have hi₂ := hbi.congr (timePaste_right_ae T a b).symm
  constructor
  · rw [kinetic_halfLine_split hT]
    exact integrable_add_measure.mpr ⟨hi₁,hi₂⟩
  · nth_rw 1 [kinetic_halfLine_split hT]
    rw [integral_add_measure hi₁ hi₂,
      integral_congr_ae (timePaste_left_ae T a b),integral_congr_ae (timePaste_right_ae T a b)]
    congr 1
    simpa only [timeTranslation_apply,sub_eq_add_neg] using
      hm.integral_comp (timeTranslation (-T)).measurableEmbedding b

end BoltzmannNonuniqueness

end

end

section

/-! # Local integrability and almost-everywhere properties under time pasting -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness

theorem phaseIntervalBetween_measure (a b : ℝ) :
    (volume.restrict (Icc a b)).prod (volume : Measure Phase) =
      volume.restrict (Icc a b ×ˢ (univ : Set Phase)) := by
  rw [Measure.restrict_prod_eq_prod_univ,← Measure.volume_eq_prod]

theorem timePaste_before_measure_le (T R : ℝ) :
    (((volume.restrict (Icc (0:ℝ) R)).prod (volume : Measure Phase)).restrict
      {z : ℝ × Phase | z.1 ≤ T}) ≤
      (volume.restrict (Icc (0:ℝ) T)).prod volume := by
  rw [phaseIntervalBetween_measure,phaseIntervalBetween_measure,
    Measure.restrict_restrict (measurableSet_le measurable_fst measurable_const)]
  apply Measure.restrict_mono _ le_rfl
  intro z hz
  exact ⟨⟨hz.2.1.1,hz.1⟩,mem_univ _⟩

theorem timePaste_after_measure_le {T : ℝ} (hT : 0 ≤ T) (R : ℝ) :
    (((volume.restrict (Icc (0:ℝ) R)).prod (volume : Measure Phase)).restrict
      {z : ℝ × Phase | z.1 ≤ T}ᶜ) ≤
      (volume.restrict (Icc T (T+R))).prod volume := by
  rw [phaseIntervalBetween_measure,phaseIntervalBetween_measure,
    Measure.restrict_restrict (measurableSet_le measurable_fst measurable_const).compl]
  apply Measure.restrict_mono _ le_rfl
  intro z hz
  have ht : T < z.1 := lt_of_not_ge hz.1
  exact ⟨⟨ht.le,le_trans hz.2.1.2 (le_add_of_nonneg_left hT)⟩,mem_univ _⟩

theorem timeTranslation_from_interval (T R : ℝ) :
    MeasurePreserving (timeTranslation (-T))
      ((volume.restrict (Icc T (T+R))).prod (volume : Measure Phase))
      ((volume.restrict (Icc (0:ℝ) R)).prod (volume : Measure Phase)) := by
  have he : T+R+-T = R := by ring
  simpa only [add_neg_cancel,he] using
    timeTranslation_interval (-T) T (T+R)

theorem timePaste_integrable_bounded {T R : ℝ} (hT : 0 ≤ T)
    {a b : ℝ × Phase → ℝ}
    (ha : Integrable a ((volume.restrict (Icc (0:ℝ) T)).prod volume))
    (hb : Integrable b ((volume.restrict (Icc (0:ℝ) R)).prod volume)) :
    Integrable (timePaste T a b) ((volume.restrict (Icc (0:ℝ) R)).prod volume) := by
  let A : Set (ℝ × Phase) := {z | z.1 ≤ T}
  have hA : MeasurableSet A := measurableSet_le measurable_fst measurable_const
  have hpre := ha.mono_measure (timePaste_before_measure_le T R)
  have hpost := ((timeTranslation_from_interval T R).integrable_comp_of_integrable hb).mono_measure
    (timePaste_after_measure_le hT R)
  have hp := Integrable.piecewise hA hpre hpost
  have he : timePaste T a b = A.piecewise a (b ∘ timeTranslation (-T)) := by
    funext z
    by_cases ht : z.1 ≤ T <;>
      simp [timePaste,A,ht,Function.comp_def,sub_eq_add_neg]
  rw [he]
  exact hp

theorem timePaste_property_ae {T R : ℝ} (hT : 0 ≤ T)
    {P Q : ℝ × Phase → Prop}
    (hP : ∀ᵐ z ∂(volume.restrict (Icc (0:ℝ) T)).prod volume, P z)
    (hQ : ∀ᵐ z ∂(volume.restrict (Icc (0:ℝ) R)).prod volume, Q z) :
    ∀ᵐ z ∂(volume.restrict (Icc (0:ℝ) R)).prod volume,
      if z.1 ≤ T then P z else Q (z.1-T,z.2) := by
  let A : Set (ℝ × Phase) := {z | z.1 ≤ T}
  have hA : MeasurableSet A := measurableSet_le measurable_fst measurable_const
  apply ae_of_ae_restrict_of_ae_restrict_compl A
  · have hp := ae_mono (timePaste_before_measure_le T R) hP
    filter_upwards [hp,ae_restrict_mem hA] with z hz ht
    exact ite_eq_left ht ▸ hz
  · have hq := (timeTranslation_from_interval T R).quasiMeasurePreserving.ae hQ
    have hp := ae_mono (timePaste_after_measure_le hT R) hq
    filter_upwards [hp,ae_restrict_mem hA.compl] with z hz ht
    have ht' : ¬z.1 ≤ T := ht
    simpa only [ht',ite_false,Function.comp_def,timeTranslation_apply,sub_eq_add_neg] using hz

end BoltzmannNonuniqueness

end

end

section

/-! # Restricting local L¹ convergence to the physical time interval -/

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace BoltzmannNonuniqueness.Published

def timeSpaceVolume (T : ℝ) : Measure SpaceTime :=
  (volume.restrict (Icc 0 T)).prod volume

def TimeLocalL1Converges (T : ℝ) (f : ℕ → SpaceTime → ℝ) (g : SpaceTime → ℝ) : Prop :=
  LocallyIntegrable g ∧ ∀ K : Set SpaceTime, IsCompact K →
    Tendsto (fun n => eLpNorm (fun z => f n z-g z) 1 ((timeSpaceVolume T).restrict K)) atTop (𝓝 0)

theorem LocalL1Converges.time_restrict {T : ℝ} {f a : ℕ → SpaceTime → ℝ} {g : SpaceTime → ℝ}
    (h : LocalL1Converges f g) (he : ∀ n, a n =ᵐ[timeSpaceVolume T] f n) :
    TimeLocalL1Converges T a g := by
  refine ⟨h.1,fun K hK => ?_⟩
  have hμ : timeSpaceVolume T ≤ (volume : Measure SpaceTime) :=
    Measure.prod_mono Measure.restrict_le_self le_rfl
  have hn (n) : eLpNorm (fun z => a n z-g z) 1 ((timeSpaceVolume T).restrict K) =
      eLpNorm (fun z => f n z-g z) 1 ((timeSpaceVolume T).restrict K) := by
    apply eLpNorm_congr_ae
    filter_upwards [ae_restrict_of_ae (he n)] with z hz
    rw [hz]
  simp_rw [hn]
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (h.2 K hK)
    (fun _ => zero_le) (fun n => eLpNorm_mono_measure _ (Measure.restrict_mono_measure hμ K))

end BoltzmannNonuniqueness.Published

end

end

section

/-! # Cumulative phase-tested sources as indicator integrals -/

noncomputable section

open MeasureTheory Set

namespace BoltzmannNonuniqueness.WeakTime

theorem timeSource_cumulative (μ : Measure (ℝ × Phase)) {φ : Phase → ℝ}
    (hφ : Measurable φ) (hn : ∀ p, 0 ≤ φ p) (t : ℝ) :
    cumulative (timeSource μ φ) t =
      ∫ z, (Iic t).indicator (fun _ => (1 : ℝ)) z.1*φ z.2 ∂μ := by
  rw [cumulative,← integral_indicator_one measurableSet_Iic]
  exact timeSource_integral μ hφ hn (measurable_const.indicator measurableSet_Iic)

theorem cumulative_density_projection {F : ℝ × Phase → ℝ}
    (hF : Integrable F (volume : Measure (ℝ × Phase)))
    {φ : Phase → ℝ} (hφ : Measurable φ) {B : ℝ} (hB : ∀ p, |φ p| ≤ B) (t : ℝ) :
    (∫ z, ((Iic t).indicator (fun _ => (1 : ℝ)) z.1*φ z.2)*F z) =
      ∫ s in Iic t, phaseProjection F φ s := by
  rw [← integral_indicator measurableSet_Iic]
  symm
  convert phaseProjection_test_integral hF hφ hB
    (measurable_const.indicator measurableSet_Iic)
    (show ∀ s : ℝ, |(Iic t).indicator (fun _ => (1 : ℝ)) s| ≤ 1 from fun s => by
      by_cases hs : s ∈ Iic t <;> simp [hs]) using 1
  apply integral_congr_ae
  exact ae_of_all _ (fun s => by by_cases hs : s ∈ Iic t <;> simp [hs])

end BoltzmannNonuniqueness.WeakTime

end

end

end OAI
