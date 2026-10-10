import OAI.MathematicalPhysics.Boltzmann.Branching.CharacteristicProductTest
import OAI.MathematicalPhysics.Boltzmann.Branching.ClippedCharacteristicGain
import OAI.MathematicalPhysics.Boltzmann.Branching.HotPositiveRegion
import OAI.MathematicalPhysics.Boltzmann.Branching.WindowLocalizedSource

namespace OAI

section

/-! # A common physical cylinder for all time tests of a fixed compact phase test -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.TransportCutoff

namespace BoltzmannNonuniqueness.EuclideanFlight

theorem exists_timePhase_cylinder (a A : ℝ) {φ : Velocity × Velocity → ℝ}
    (hc : HasCompactSupport φ) :
    ∃ R Rₑ : ℝ, 0 ≤ R ∧ ∀ (θ : ℝ → ℝ), tsupport θ ⊆ Ioo a A →
      tsupport (testPullback (timePhaseTest θ φ)) ⊆ kineticWindow a A Rₑ ∧
      (∀ z ∈ tsupport (testPullback (timePhaseTest θ φ)),
        hotChart z ∈ JetCopyDatum.AttainedCapSequence.coldCylinderSet a A R) := by
  let C := Icc a A ×ˢ tsupport φ
  have hC : IsCompact C := isCompact_Icc.prod hc.isCompact
  have hE := hC.image characteristicHomeomorph.continuous
  have hH := hE.image hotHomeomorph.continuous
  obtain ⟨Rₑ,hRₑ⟩ := hE.isBounded.exists_norm_le
  obtain ⟨R,hR,hRb⟩ := hH.isBounded.exists_pos_norm_le
  refine ⟨R,Rₑ,hR.le,?_⟩
  intro θ hs
  have hsub : tsupport (testPullback (timePhaseTest θ φ)) ⊆ characteristicEquiv.symm ⁻¹' C := by
    apply closure_minimal _ ((isClosed_Icc.prod (isClosed_tsupport φ)).preimage
      characteristicHomeomorph.symm.continuous)
    intro z hz
    have hz' : timePhaseTest θ φ (characteristicEquiv.symm z) ≠ 0 := hz
    have hp := timePhaseTest_support θ φ (subset_tsupport _ hz')
    exact ⟨⟨(hs hp.1).1.le,(hs hp.1).2.le⟩,hp.2⟩
  have himg (z) (hz : z ∈ tsupport (testPullback (timePhaseTest θ φ))) :
      z ∈ characteristicHomeomorph '' C := by
    exact ⟨characteristicEquiv.symm z,hsub hz,characteristicEquiv.apply_symm_apply z⟩
  constructor
  · intro z hz
    have ht := (hsub hz).1
    have hn : ‖z‖ ≤ Rₑ := hRₑ _ (himg z hz)
    exact ⟨⟨ht,(Metric.mem_closedBall.mpr (by
      simpa only [dist_zero_right] using (norm_snd_le z.1).trans ((norm_fst_le z).trans hn)))⟩,
      mem_univ _⟩
  · intro z hz
    have ht := (hsub hz).1
    have hn : ‖hotChart z‖ ≤ R := hRb _ ⟨z,himg z hz,rfl⟩
    exact ⟨⟨ht,(Metric.mem_closedBall.mpr (by
      simpa only [dist_zero_right] using
        (norm_snd_le (hotChart z).1).trans ((norm_fst_le (hotChart z)).trans hn)))⟩,
      mem_univ _⟩

end BoltzmannNonuniqueness.EuclideanFlight

end

end

section

/-! # A common characteristic cylinder for tests in one compact phase set -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.TransportCutoff

namespace BoltzmannNonuniqueness.EuclideanFlight

theorem exists_timePhase_cylinder_for_support (a A : ℝ) {β : Velocity × Velocity → ℝ}
    (hc : HasCompactSupport β) :
    ∃ R Rₑ : ℝ, 0 ≤ R ∧ ∀ (φ : Velocity × Velocity → ℝ), tsupport φ ⊆ tsupport β →
      ∀ (θ : ℝ → ℝ), tsupport θ ⊆ Ioo a A →
        tsupport (testPullback (timePhaseTest θ φ)) ⊆ kineticWindow a A Rₑ ∧
        (∀ z ∈ tsupport (testPullback (timePhaseTest θ φ)),
          hotChart z ∈ JetCopyDatum.AttainedCapSequence.coldCylinderSet a A R) := by
  let C := Icc a A ×ˢ tsupport β
  have hC : IsCompact C := isCompact_Icc.prod hc.isCompact
  have hE := hC.image characteristicHomeomorph.continuous
  have hH := hE.image hotHomeomorph.continuous
  obtain ⟨Rₑ,hRₑ⟩ := hE.isBounded.exists_norm_le
  obtain ⟨R,hR,hRb⟩ := hH.isBounded.exists_pos_norm_le
  refine ⟨R,Rₑ,hR.le,?_⟩
  intro φ hφ θ hs
  have hsub : tsupport (testPullback (timePhaseTest θ φ)) ⊆ characteristicEquiv.symm ⁻¹' C := by
    apply closure_minimal _ ((isClosed_Icc.prod (isClosed_tsupport β)).preimage
      characteristicHomeomorph.symm.continuous)
    intro z hz
    have hp := timePhaseTest_support θ φ (subset_tsupport _ hz)
    exact ⟨⟨(hs hp.1).1.le,(hs hp.1).2.le⟩,hφ hp.2⟩
  have himg (z) (hz : z ∈ tsupport (testPullback (timePhaseTest θ φ))) :
      z ∈ characteristicHomeomorph '' C :=
    ⟨characteristicEquiv.symm z,hsub hz,characteristicEquiv.apply_symm_apply z⟩
  constructor
  · intro z hz
    have ht := (hsub hz).1
    have hn : ‖z‖ ≤ Rₑ := hRₑ _ (himg z hz)
    exact ⟨⟨ht,(Metric.mem_closedBall.mpr (by
      simpa only [dist_zero_right] using (norm_snd_le z.1).trans ((norm_fst_le z).trans hn)))⟩,
      mem_univ _⟩
  · intro z hz
    have ht := (hsub hz).1
    have hn : ‖hotChart z‖ ≤ R := hRb _ ⟨z,himg z hz,rfl⟩
    exact ⟨⟨ht,(Metric.mem_closedBall.mpr (by
      simpa only [dist_zero_right] using
        (norm_snd_le (hotChart z).1).trans ((norm_fst_le (hotChart z)).trans hn)))⟩,
      mem_univ _⟩

end BoltzmannNonuniqueness.EuclideanFlight

end

end

section

/-! # Removing a spatial cylinder from compactly phase-tested characteristics -/

noncomputable section

open MeasureTheory Set
open BoltzmannNonuniqueness.TransportCutoff
open BoltzmannNonuniqueness.JetCopyDatum.AttainedCapSequence

namespace BoltzmannNonuniqueness.EuclideanFlight

theorem coldCylinderSet_mono_radius {a A R S : ℝ} (hRS : R ≤ S) :
    coldCylinderSet a A R ⊆ coldCylinderSet a A S := by
  intro z hz
  exact ⟨⟨hz.1.1,Metric.closedBall_subset_closedBall hRS hz.1.2⟩,hz.2⟩

theorem exists_phase_cylinder (a A : ℝ) {φ : Velocity × Velocity → ℝ}
    (hc : HasCompactSupport φ) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ t ∈ Icc a A, ∀ p ∈ tsupport φ,
      hotCharacteristicEquiv (t,p) ∈ coldCylinderSet a A R := by
  have hm : Continuous hotCharacteristicEquiv :=
    hotHomeomorph.continuous.comp characteristicHomeomorph.continuous
  obtain ⟨R,hR,hRb⟩ := ((isCompact_Icc.prod hc.isCompact).image hm).isBounded.exists_pos_norm_le
  refine ⟨R,hR.le,?_⟩
  intro t ht p hp
  have hb : ‖hotCharacteristicEquiv (t,p)‖ ≤ R := hRb _ ⟨(t,p),⟨ht,hp⟩,rfl⟩
  refine ⟨⟨ht,?_⟩,mem_univ _⟩
  rw [Metric.mem_closedBall,dist_zero_right]
  exact (norm_snd_le (hotCharacteristicEquiv (t,p)).1).trans
    ((norm_fst_le (hotCharacteristicEquiv (t,p))).trans hb)

theorem exists_timePhase_cylinder_cover (a A : ℝ) {φ : Velocity × Velocity → ℝ}
    (hc : HasCompactSupport φ) :
    ∃ R Rₑ : ℝ, 0 ≤ R ∧
      (∀ t ∈ Icc a A, ∀ p ∈ tsupport φ,
        hotCharacteristicEquiv (t,p) ∈ coldCylinderSet a A R) ∧
      ∀ (θ : ℝ → ℝ), tsupport θ ⊆ Ioo a A →
        tsupport (testPullback (timePhaseTest θ φ)) ⊆ kineticWindow a A Rₑ ∧
        (∀ z ∈ tsupport (testPullback (timePhaseTest θ φ)), hotChart z ∈ coldCylinderSet a A R) := by
  obtain ⟨R₀,Rₑ,hR₀,hloc⟩ := exists_timePhase_cylinder a A hc
  obtain ⟨R₁,hR₁,hcover⟩ := exists_phase_cylinder a A hc
  refine ⟨max R₀ R₁,Rₑ,hR₀.trans (le_max_left _ _),?_,?_⟩
  · intro t ht p hp
    exact coldCylinderSet_mono_radius (le_max_right R₀ R₁) (hcover t ht p hp)
  · intro θ hs
    exact ⟨(hloc θ hs).1,fun z hz =>
      coldCylinderSet_mono_radius (le_max_left R₀ R₁) ((hloc θ hs).2 z hz)⟩

theorem cylinder_phase_integral_eq {a A R t : ℝ}
    {φ : Velocity × Velocity → ℝ} {f : HotKineticPhase → ℝ}
    (hcover : ∀ p ∈ tsupport φ, hotCharacteristicEquiv (t,p) ∈ coldCylinderSet a A R) :
    (∫ p, φ p*cylinderPullback a A R f (t,p)) =
      ∫ p, φ p*f (hotCharacteristicEquiv (t,p)) := by
  apply integral_congr_ae
  exact ae_of_all _ (fun p => by
    by_cases hp : φ p = 0
    · simp only [hp,zero_mul]
    · change φ p*(coldCylinderSet a A R).indicator f (hotCharacteristicEquiv (t,p)) = _
      rw [indicator_of_mem (hcover p (subset_tsupport φ hp))])

end BoltzmannNonuniqueness.EuclideanFlight

end

end

section

/-! # The full physical gain is the almost-everywhere limit on characteristics -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace BoltzmannNonuniqueness.PeriodicApproximation
open CollisionCompactness

def physicalCharacteristicGain (f : (ℝ × Position) × Velocity → ℝ) : ℝ × Phase → ℝ :=
  TorusFlight.along (TorusFlight.regroup (gainDensity f))

theorem physicalCharacteristicGain_measurable {f : (ℝ × Position) × Velocity → ℝ}
    (hfm : Measurable f) : Measurable (physicalCharacteristicGain f) :=
  (gainDensity_measurable hfm).comp
    ((measurable_fst.prodMk TorusFlight.measurable_flight.fst).prodMk measurable_snd.snd)

theorem physicalCharacteristicGain_nonneg {f : (ℝ × Position) × Velocity → ℝ}
    (hf : ∀ p, 0 ≤ f p) (z : ℝ × Phase) : 0 ≤ physicalCharacteristicGain f z :=
  gainDensity_nonneg hf _

theorem GlobalCollisionLimit.characteristic_clipped_gain_tendsto
    {f : Density} {hfm : Measurable f} (G : GlobalCollisionLimit f hfm)
    (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f)) {T : ℝ} (hT : 0 ≤ T)
    (L : ℝ) :
    ∀ᵐ z ∂(volume.restrict (Icc 0 T)).prod ((volume : Measure Position).prod
      ((volume : Measure Velocity).restrict (Metric.closedBall 0 L))),
      Tendsto (fun n : ℕ => characteristicClippedPhysicalGain (n:ℝ) (n:ℝ)
        G.weakLimit.kineticProfile z) atTop (𝓝 (physicalCharacteristicGain G.weakLimit.kineticProfile z)) := by
  have hg := (G.normalized_integrability hf hi hT).2.2
  have hg' := hg.filter_mono (ae_mono
    (Measure.prod_mono le_rfl (Measure.restrict_le_self (μ := (volume : Measure Velocity))
      (s := Metric.closedBall 0 L))))
  have h := (TorusFlight.alongRegroup_measurePreserving (volume.restrict (Icc 0 T))
    ((volume : Measure Velocity).restrict (Metric.closedBall 0 L))).quasiMeasurePreserving.ae hg'
  filter_upwards [h] with z hz
  exact clippedPhysicalGain_tendsto G.weakLimit.kineticProfile_measurable
    (fun _ => G.weakLimit.nonnegative _) _ hz.1

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

end OAI
