import OAI.MathematicalPhysics.Boltzmann.Branching.HotPhysicalSource
import OAI.MathematicalPhysics.Boltzmann.Branching.PhaseDecompositionNorm
import OAI.MathematicalPhysics.Boltzmann.Branching.WeightedJetSolutions
import OAI.MathematicalPhysics.Boltzmann.Jets.ColdHotSourceDecomposition

namespace OAI

section

/-! # Exact physical source of the hot remainder after cancellation of damping -/

noncomputable section

open MeasureTheory

namespace BoltzmannNonuniqueness.HotRepresentative

variable {X I : Type*} [MeasurableSpace X]

theorem physical_hot_source_identity {q b R : ℝ} (L : ℝ)
    {c : I → X × Velocity → ℝ} {F : X × Velocity → ℝ}
    (hcm : ∀ i, Measurable (c i)) (hFm : Measurable F)
    (hc : ∀ i p, 0 ≤ c i p ∧ c i p ≤ R) (hF : ∀ p, 0 ≤ F p ∧ F p ≤ R)
    (hSum : ∀ s : Finset I, ∀ p, ∑ i ∈ s, c i p ≤ F p)
    (p : X × Velocity) (hp : p.2 ∈ good q) :
    VelocityWeight.H q p.2*(source q b L F p-(∑' i, coldSource q b L F (c i) p)-
      L*(F p-∑' i, c i p)) =
      KineticCollisionNullSets.gain b (density q F) p-
        (∑' i, KineticCollisionNullSets.gain b (density q (c i)) p)-
        KineticCollisionNullSets.frequency b (density q F) p*
          density q (fun z => F z-∑' i, c i z) p := by
  have hg : VelocityWeight.H q p.2*(∑' i, gain q b (c i) p) =
      ∑' i, KineticCollisionNullSets.gain b (density q (c i)) p := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro i
    exact physical_gain_eq (c i) hp
  rw [hot_source_identity L hcm hFm hc hF hSum]
  calc
    _ = VelocityWeight.H q p.2*gain q b F p-
        VelocityWeight.H q p.2*(∑' i, gain q b (c i) p)-
        frequency q b F p*(VelocityWeight.H q p.2*(F p-∑' i, c i p)) := by ring
    _ = _ := by rw [physical_gain_eq F hp,hg]; rfl

end BoltzmannNonuniqueness.HotRepresentative

end

end

section

/-! # Replacing only the hot remainder by an essential-norm representative -/

noncomputable section

open MeasureTheory MeasureTheory.Measure

namespace BoltzmannNonuniqueness.HotCanonical

def replacement (F C : ℝ × JetPrototype.Phase → ℝ) (u : ℝ × JetPrototype.Phase) : ℝ :=
  C u+PhaseEssSup.canonical (fun z => F z-C z) u

theorem measurable_replacement {F C : ℝ × JetPrototype.Phase → ℝ}
    (hFm : Measurable F) (hCm : Measurable C)
    (hnorm : Measurable (fun t => PhaseEssSup.size (fun p => F (t,p)-C (t,p)))) :
    Measurable (replacement F C) :=
  hCm.add (PhaseEssSup.measurable_canonical (hFm.sub hCm) hnorm)

theorem replacement_bounds {F C : ℝ × JetPrototype.Phase → ℝ}
    (hC : ∀ u, 0 ≤ C u ∧ C u ≤ F u) (u : ℝ × JetPrototype.Phase) :
    C u ≤ replacement F C u ∧ replacement F C u ≤ F u ∧
      replacement F C u-C u ≤ PhaseEssSup.size (fun p => F (u.1,p)-C (u.1,p)) := by
  have h := PhaseEssSup.canonical_bounds (f := fun z => F z-C z)
    (fun z => sub_nonneg.mpr (hC z).2) u
  unfold replacement
  constructor
  · linarith [h.1]
  constructor
  · linarith [h.2.2]
  · linarith [h.2.1]

theorem replacement_ae {F C : ℝ × JetPrototype.Phase → ℝ} {R : ℝ}
    (hFm : Measurable F) (hCm : Measurable C)
    (hF : ∀ u, F u ≤ R) (hC : ∀ u, 0 ≤ C u ∧ C u ≤ F u)
    (hnorm : Measurable (fun t => PhaseEssSup.size (fun p => F (t,p)-C (t,p)))) :
    replacement F C =ᵐ[(volume : Measure ℝ).prod FlightMeasure.phaseVolume] F := by
  have hB (u) : |F u-C u| ≤ R := by
    rw [abs_of_nonneg (sub_nonneg.mpr (hC u).2)]
    linarith [(hC u).1,hF u]
  filter_upwards [PhaseEssSup.canonical_ae (hFm.sub hCm) hB hnorm] with u hu
  change PhaseEssSup.canonical (fun z => F z-C z) u = F u-C u at hu
  unfold replacement
  rw [hu]
  ring

theorem state_congr {F G : ℝ × JetPrototype.Phase → ℝ}
    (hFG : F =ᵐ[(volume : Measure ℝ).prod FlightMeasure.phaseVolume] G) :
    GaussianLocal.state F =ᵐ[((volume : Measure ℝ).prod JetPrototype.spaceVolume).prod volume]
      GaussianLocal.state G :=
  (measurePreserving_prodAssoc (volume : Measure ℝ) JetPrototype.spaceVolume
    (volume : Measure Velocity)).quasiMeasurePreserving.ae_eq_comp hFG

end BoltzmannNonuniqueness.HotCanonical

namespace BoltzmannNonuniqueness.HotRepresentative

variable {X : Type*} [MeasurableSpace X]

theorem coldSource_congr_total (μ : Measure X) [SFinite μ]
    {F G : X × Velocity → ℝ} (hFG : F =ᵐ[μ.prod volume] G)
    (q b L : ℝ) (c : X × Velocity → ℝ) : coldSource q b L F c =ᵐ[μ.prod volume] coldSource q b L G c := by
  filter_upwards [frequency_congr μ hFG q b] with p hp
  unfold coldSource
  rw [hp]

end BoltzmannNonuniqueness.HotRepresentative

end

end

section

/-! # The mixed, quadratic-hot, and pure-cold parts of the physical hot source -/

noncomputable section

open MeasureTheory
open BoltzmannNonuniqueness.CollisionCompactness

namespace BoltzmannNonuniqueness.HotRepresentative

variable {X I : Type*} [MeasurableSpace X] [Countable I]

theorem physical_hot_collision_decomposition {q b R : ℝ} (hq : q < 2) (hb : 0 ≤ b) (L : ℝ)
    {c : I → X × Velocity → ℝ} {F : X × Velocity → ℝ}
    (hcm : ∀ i, Measurable (c i)) (hFm : Measurable F)
    (hc : ∀ i p, 0 ≤ c i p ∧ c i p ≤ R) (hF : ∀ p, 0 ≤ F p ∧ F p ≤ R)
    (hSum : ∀ s : Finset I, ∀ p, ∑ i ∈ s, c i p ≤ F p)
    (p : X × Velocity) (hp : p.2 ∈ good q) :
    let C : X × Velocity → ℝ := fun z => ∑' i, c i z
    let G : X × Velocity → ℝ := F-C
    VelocityWeight.H q p.2*(source q b L F p-(∑' i, coldSource q b L F (c i) p)-L*G p) =
      2*mixedGainDensity b (density q C) (density q G) p-
        density q G p*KineticCollisionNullSets.frequency b (density q C) p+
        collisionSource b (density q G) p+
        VelocityWeight.H q p.2*(source q b 0 C p-∑' i, coldSource q b 0 C (c i) p) := by
  intro C G
  have hCm : Measurable C := Measurable.tsum hcm
  have hGm : Measurable G := hFm.sub hCm
  have hCF z : C z ≤ F z := Real.tsum_le_of_sum_le (fun i => (hc i z).1) (fun s => hSum s z)
  have hCn z : 0 ≤ C z := tsum_nonneg (fun i => (hc i z).1)
  have hCb z : 0 ≤ C z ∧ C z ≤ R := ⟨hCn z,(hCF z).trans (hF z).2⟩
  have hGb z : 0 ≤ G z ∧ G z ≤ R :=
    ⟨sub_nonneg.mpr (hCF z),(sub_le_self _ (hCn z)).trans (hF z).2⟩
  have hplus : C+G = F := by
    funext z
    dsimp only [G,Pi.add_apply,Pi.sub_apply]
    ring
  have hg := physical_gain_add (b := b) hCm hGm hCb hGb p hp
  have hν := physical_frequency_add hq hb hCm hGm hCb hGb p
  rw [hplus] at hg hν
  calc
    _ = (KineticCollisionNullSets.gain b (density q F) p-
          KineticCollisionNullSets.gain b (density q C) p)-
        KineticCollisionNullSets.frequency b (density q F) p*density q G p+
        VelocityWeight.H q p.2*(source q b 0 C p-∑' i, coldSource q b 0 C (c i) p) := by
      dsimp only [G,Pi.sub_apply]
      rw [hot_cold_source_decomposition L hcm hFm hc hF hSum]
      rw [mul_add,mul_sub,mul_sub,physical_gain_eq F hp,physical_gain_eq C hp]
      dsimp only [density,G,Pi.sub_apply,frequency]
      ring
    _ = _ := by
      rw [hg,hν]
      unfold collisionSource
      ring

end BoltzmannNonuniqueness.HotRepresentative

end

end

end OAI
