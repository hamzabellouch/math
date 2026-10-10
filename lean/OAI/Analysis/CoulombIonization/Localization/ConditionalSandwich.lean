import Mathlib
import OAI.Analysis.CoulombIonization.Localization.UnorderedObservations

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter

namespace CoulombObservation

lemma condExp_observable_sandwich {Ω : Type*} {m₀ : MeasurableSpace Ω}
    {m : MeasurableSpace Ω} (hm : m ≤ m₀) (μ : @Measure Ω m₀) [IsFiniteMeasure μ]
    {f h d : Ω → ℝ} (hf : Integrable f μ) (hh : Integrable h μ) (hd : Integrable d μ)
    (hhm : StronglyMeasurable[m] h) (hdm : StronglyMeasurable[m] d)
    (hb : ∀ᵐ z ∂μ, |f z-h z| ≤ d z) :
    ∀ᵐ z ∂μ, |μ[f | m] z-h z| ≤ d z := by
  have hlow : (fun z => h z-d z) ≤ᵐ[μ] f := hb.mono (fun z hz => by
    have := (abs_le.mp hz).1
    linarith)
  have hupp : f ≤ᵐ[μ] (fun z => h z+d z) := hb.mono (fun z hz => by
    have := (abs_le.mp hz).2
    linarith)
  have hlo := condExp_mono (m := m) (hh.sub hd) hf hlow
  have hup := condExp_mono (m := m) hf (hh.add hd) hupp
  rw [condExp_of_stronglyMeasurable (m₀ := m₀) (μ := μ) hm (hhm.sub hdm) (hh.sub hd)] at hlo
  rw [condExp_of_stronglyMeasurable (m₀ := m₀) (μ := μ) hm (hhm.add hdm) (hh.add hd)] at hup
  filter_upwards [hlo,hup] with z hl hu
  simp only [Pi.sub_apply,Pi.add_apply] at hl hu
  exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma raw_condExp_observable_error {Ω : Type*} {m₀ : MeasurableSpace Ω}
    {m : MeasurableSpace Ω} (hm : m ≤ m₀) (μ : @Measure Ω m₀) [IsFiniteMeasure μ]
    {f h d : Ω → ℝ} (hf : Integrable f μ) (hh : Integrable h μ) (hd : Integrable d μ)
    (hhm : StronglyMeasurable[m] h) (hdm : StronglyMeasurable[m] d)
    (hb : ∀ᵐ z ∂μ, |f z-h z| ≤ d z) :
    ∀ᵐ z ∂μ, |f z-μ[f | m] z| ≤ 2*d z := by
  filter_upwards [hb,condExp_observable_sandwich hm μ hf hh hd hhm hdm hb] with z hz hc
  have he : f z-μ[f | m] z = (f z-h z)+(h z-μ[f | m] z) := by ring
  rw [he]
  calc
    _ ≤ |f z-h z|+|h z-μ[f | m] z| := abs_add_le _ _
    _ ≤ d z+d z := add_le_add hz (by rwa [abs_sub_comm])
    _ = _ := by ring

end CoulombObservation

open MeasureTheory Filter Set Metric
open scoped BigOperators NNReal

namespace CoulombAtom
open CoulombObservation

lemma integrable_configuration_test {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] {N : ℕ} {X : Ω → Configuration N}
    (hX : Measurable X) {g : Space → ℝ} (hg : Continuous g) (hc : HasCompactSupport g) :
    Integrable (fun z => ∑ i, g (X z i)) μ := by
  obtain ⟨v,hv⟩ := hg.norm.exists_forall_ge_of_hasCompactSupport hc.norm
  apply integrable_finsetSum
  intro i _
  apply (integrable_const ‖g v‖).mono'
    ((hg.measurable.comp ((measurable_pi_apply i).comp hX)).aestronglyMeasurable)
  exact ae_of_all _ (fun z => hv (X z i))

lemma observedLocalCount_integrable {N K : ℕ} (μ : Measure (Configuration N))
    [IsFiniteMeasure μ] (ell : Fin K → ℝ) (k : Fin K) (y : Space) (R : ℝ) :
    Integrable (observedLocalCount (N := N) ell k y R) (physicalObservationLaw μ K) := by
  have h := (observedLocalCount_information_measurable (N := N) ell k (Nat.zero_le _) y R).mono
    (observationInformation_le ell 0) (le_refl _)
  apply (integrable_const (N:ℝ)).mono' h.aestronglyMeasurable
  exact ae_of_all _ (fun z => by
    simpa only [Real.norm_eq_abs,abs_of_nonneg (observedLocalCount_nonneg ell k y R z)] using
      observedLocalCount_le ell k y R z)

def posteriorTestValue {N K : ℕ} (μ : Measure (Configuration N)) (ell : Fin K → ℝ)
    (j : ℕ) (g : Space → ℝ) :
    (Configuration N × (Fin K × (Fin N × Fin 3) → ℝ)) → ℝ :=
  (physicalObservationLaw μ K)[(fun z => ∑ i, g (z.1 i)) | observationInformation ell j]

lemma posteriorTestValue_tower {N K : ℕ} (μ : Measure (Configuration N))
    [IsFiniteMeasure μ] (ell : Fin K → ℝ) {j k : ℕ} (hjk : j ≤ k) (g : Space → ℝ) :
    (physicalObservationLaw μ K)[posteriorTestValue μ ell j g | observationInformation ell k] =ᵐ[
      physicalObservationLaw μ K] posteriorTestValue μ ell k g :=
  condExp_condExp_of_le (observationInformation_antitone ell hjk) (observationInformation_le ell j)

theorem posterior_observed_test_sandwich {N K : ℕ} (μ : Measure (Configuration N))
    [IsFiniteMeasure μ] (ell : Fin K → ℝ) (hell : ∀ k, 0 ≤ ell k)
    {j : ℕ} (k : Fin K) (hk : j ≤ k.val) {g : Space → ℝ} {L : ℝ≥0}
    (hg : LipschitzWith L g) (y : Space) (R : ℝ)
    (hs : Function.support g ⊆ closedBall y R) :
    ∀ᵐ z ∂physicalObservationLaw μ K,
      |posteriorTestValue μ ell j g z-(∑ i, g (physicalObservedConfiguration ell k z i))| ≤
        observedLocalCount ell k y (R+Real.sqrt 3*ell k) z*((L:ℝ)*(Real.sqrt 3*ell k)) := by
  have hc : HasCompactSupport g := HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall y R) hs
  have hf := integrable_configuration_test (physicalObservationLaw μ K)
    measurable_fst hg.continuous hc
  have hh := integrable_configuration_test (physicalObservationLaw μ K)
    (physicalObservedConfiguration_measurable ell k) hg.continuous hc
  have hd := (observedLocalCount_integrable μ ell k y (R+Real.sqrt 3*ell k)).mul_const
    ((L:ℝ)*(Real.sqrt 3*ell k))
  have hhm := (observedStatistic_information_measurable (N := N) ell k hk hg.continuous.measurable).stronglyMeasurable
  have hdm := ((observedLocalCount_information_measurable (N := N) ell k hk y (R+Real.sqrt 3*ell k)).mul_const
    ((L:ℝ)*(Real.sqrt 3*ell k))).stronglyMeasurable
  apply condExp_observable_sandwich (observationInformation_le ell j)
    (physicalObservationLaw μ K) hf hh hd hhm hdm
  filter_upwards [physicalObservationLaw_ae_displacement μ ell hell] with z hz
  exact matchedLocal_test_error z.1 (physicalObservedConfiguration ell k z)
    (mul_nonneg (Real.sqrt_nonneg _) (hell k)) (hz k) hg y hs

theorem raw_posterior_local_test_error {N K : ℕ} (μ : Measure (Configuration N))
    [IsFiniteMeasure μ] (ell : Fin K → ℝ) (hell : ∀ k, 0 ≤ ell k)
    {j : ℕ} (k : Fin K) (hk : j ≤ k.val) {g : Space → ℝ} {L : ℝ≥0}
    (hg : LipschitzWith L g) (y : Space) (R : ℝ)
    (hs : Function.support g ⊆ closedBall y R) :
    ∀ᵐ z ∂physicalObservationLaw μ K,
      |(∑ i, g (z.1 i))-posteriorTestValue μ ell j g z| ≤
        2*observedLocalCount ell k y (R+Real.sqrt 3*ell k) z*((L:ℝ)*(Real.sqrt 3*ell k)) := by
  filter_upwards [physicalObservationLaw_ae_displacement μ ell hell,
    posterior_observed_test_sandwich μ ell hell k hk hg y R hs] with z hz hp
  have hr := matchedLocal_test_error z.1 (physicalObservedConfiguration ell k z)
    (mul_nonneg (Real.sqrt_nonneg _) (hell k)) (hz k) hg y hs
  have he : (∑ i, g (z.1 i))-posteriorTestValue μ ell j g z =
    ((∑ i, g (z.1 i))-(∑ i, g (physicalObservedConfiguration ell k z i)))+
    ((∑ i, g (physicalObservedConfiguration ell k z i))-posteriorTestValue μ ell j g z) := by ring
  rw [he]
  refine (abs_add_le _ _).trans ?_
  rw [abs_sub_comm (∑ i, g (physicalObservedConfiguration ell k z i))]
  change _+_ ≤ 2*observedLocalCount ell k y (R+Real.sqrt 3*ell k) z*((L:ℝ)*(Real.sqrt 3*ell k))
  dsimp only [observedLocalCount] at hp ⊢
  linarith

end CoulombAtom

end

end OAI
