import OAI.MathematicalPhysics.Boltzmann.Approximation.CapEntropyMoments
import OAI.MathematicalPhysics.Boltzmann.Approximation.CapMildLimit
import OAI.MathematicalPhysics.Boltzmann.Approximation.CapPairMoments
import OAI.MathematicalPhysics.Boltzmann.Approximation.CapWeightedNonlinearLimit
import OAI.MathematicalPhysics.Boltzmann.Approximation.CappedDensitySequence
import OAI.MathematicalPhysics.Boltzmann.Approximation.CappedTightness
import OAI.MathematicalPhysics.Boltzmann.Approximation.PositiveNonlinearLimit
import OAI.MathematicalPhysics.Boltzmann.Approximation.SubcapColdControl
import OAI.MathematicalPhysics.Boltzmann.Branching.CellLocalizedSource
import OAI.MathematicalPhysics.Boltzmann.Branching.CompactCapFamily
import OAI.MathematicalPhysics.Boltzmann.Branching.TightCapFamily
import OAI.MathematicalPhysics.Boltzmann.Compactness.WeakCapOuterBound
import OAI.MathematicalPhysics.Boltzmann.Jets.TorusCharacteristic

namespace OAI

section

/-! # Uniform integrability of collision terms below the cap -/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
open BoltzmannNonuniqueness.WeightedLocalControl

namespace BoltzmannNonuniqueness.JetCopyDatum.BelowCap

theorem cap_family_gainLoss_uniformIntegrable {s₀ η K α γ d₀ q T : ℝ}
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq : q < 2) (hT : 0 ≤ T) (hTmax : T ≤ 1/32)
    (F : ∀ N, Approximation s₀ η K α γ d₀ q T N) :
    UniformIntegrable (fun (N : ℕ) => CollisionCompactness.gainDensity (torusPhysical q (F N).solution.value)) 1
      ((AnnularEnvelope.timePositionVolume T).prod (volume : Measure Velocity)) ∧
    UniformIntegrable (fun (N : ℕ) => CollisionCompactness.lossDensity (torusPhysical q (F N).solution.value)) 1
      ((AnnularEnvelope.timePositionVolume T).prod (volume : Measure Velocity)) := by
  have hδ (n) : 0 < DatumBounds.scale s₀ η (n+1) := DatumBounds.scale_pos hs₀ _
  have hδmax (n) : DatumBounds.scale s₀ η (n+1) ≤ 1 := by
    have h := JetGeometry.scale_antitone hs₀.le hη.le (Nat.zero_le (n+1))
    rw [show DatumBounds.scale s₀ η 0 = s₀ by simp [DatumBounds.scale]] at h
    linarith
  have hhn (n) (p) : 0 ≤ (F n).coefficient*
      HotSeedProfile.normalized q (DatumBounds.scale s₀ η (n+1)) p := by
    obtain ⟨_,_,hb⟩ := HotSeedProfile.normalized_bounds (hδ n) (hδmax n) q
    exact mul_nonneg (F n).coefficient_mem.1 (hb p).1
  exact capped_family_gainLoss_uniformIntegrable hs₀ hsmax hη hηmax hK hα hαmax hγ hd₀ hd₀max
    hsmall hq hT hTmax (fun n => n+1) (fun n => damping q (n+1) (F n).amplitude)
    (fun n => 2*(F n).amplitude) (fun n => DatumBounds.scale s₀ η (n+1))
    (fun n p => (F n).coefficient*HotSeedProfile.normalized q (DatumBounds.scale s₀ η (n+1)) p)
    (fun _ => by positivity) (fun n => (bounds (by positivity) (F n).amplitude_pos).1)
    (fun n => mul_nonneg (by norm_num) (F n).amplitude_pos.le) hδ hδmax (fun _ => le_rfl)
    (fun n => (HotSeedProfile.normalized_measurable q _).const_mul _) hhn
    (fun n => (F n).initial_bound) (fun n => (F n).solution) (fun n => (F n).cap_bound)

theorem cap_family_cutoff_uniformIntegrable {s₀ η K α γ d₀ q T : ℝ}
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq : q < 2) (hT : 0 ≤ T) (hTmax : T ≤ 1/32)
    (F : ∀ N, Approximation s₀ η K α γ d₀ q T N) :
    UniformIntegrable (fun (N : ℕ) => KineticCollisionNullSets.gain (N+1) (torusPhysical q (F N).solution.value)) 1
      ((AnnularEnvelope.timePositionVolume T).prod (volume : Measure Velocity)) ∧
    UniformIntegrable (fun (N : ℕ) => CollisionCompactness.cutoffLossDensity (N+1) (torusPhysical q (F N).solution.value)) 1
      ((AnnularEnvelope.timePositionVolume T).prod (volume : Measure Velocity)) := by
  have hp := cap_family_pairs_uniformIntegrable hs₀ hsmax hη hηmax hK hα hαmax hγ hd₀ hd₀max
    hsmall hq hT hTmax F
  have hc := cap_family_gainLoss_uniformIntegrable hs₀ hsmax hη hηmax hK hα hαmax hγ hd₀ hd₀max
    hsmall hq hT hTmax F
  exact CollisionCompactness.cutoff_gainLoss_uniformIntegrable
    (fun (N : ℕ) => torusPhysical_measurable (F N).solution.measurable_value q)
    (fun (N : ℕ) => torusPhysical_nonneg (fun z => ((F N).solution.value_bounds z).1) q)
    (fun (N : ℕ) => memLp_one_iff_integrable.mp (hp.memLp N)) hc.1 hc.2 (fun (N : ℕ) => N+1)


end BoltzmannNonuniqueness.JetCopyDatum.BelowCap

end

end

section

/-! # Uniform integrability of one-particle densities below the cap -/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
open BoltzmannNonuniqueness.WeightedLocalControl

namespace BoltzmannNonuniqueness.JetCopyDatum.BelowCap

theorem cap_family_density_uniformIntegrable {s₀ η K α γ d₀ q T : ℝ}
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq : q < 2) (hT : 0 ≤ T) (hTmax : T ≤ 1/32)
    (F : ∀ N, Approximation s₀ η K α γ d₀ q T N) :
    UniformIntegrable (fun N => torusPhysical q (F N).solution.value) 1
      ((AnnularEnvelope.timePositionVolume T).prod (volume : Measure Velocity)) := by
  have hδ (n) : 0 < DatumBounds.scale s₀ η (n+1) := DatumBounds.scale_pos hs₀ _
  have hδmax (n) : DatumBounds.scale s₀ η (n+1) ≤ 1 := by
    have h := JetGeometry.scale_antitone hs₀.le hη.le (Nat.zero_le (n+1))
    rw [show DatumBounds.scale s₀ η 0 = s₀ by simp [DatumBounds.scale]] at h
    linarith
  have hhn (n) (p) : 0 ≤ (F n).coefficient*
      HotSeedProfile.normalized q (DatumBounds.scale s₀ η (n+1)) p := by
    obtain ⟨_,_,hb⟩ := HotSeedProfile.normalized_bounds (hδ n) (hδmax n) q
    exact mul_nonneg (F n).coefficient_mem.1 (hb p).1
  exact capped_family_density_uniformIntegrable hs₀ hsmax hη hηmax hK hα hαmax hγ hd₀ hd₀max
    hsmall hq hT hTmax (fun n => n+1) (fun n => damping q (n+1) (F n).amplitude)
    (fun n => 2*(F n).amplitude) (fun n => DatumBounds.scale s₀ η (n+1))
    (fun n p => (F n).coefficient*HotSeedProfile.normalized q (DatumBounds.scale s₀ η (n+1)) p)
    (fun _ => by positivity) (fun n => (bounds (by positivity) (F n).amplitude_pos).1)
    (fun n => mul_nonneg (by norm_num) (F n).amplitude_pos.le) hδ hδmax (fun _ => le_rfl)
    (fun n => (HotSeedProfile.normalized_measurable q _).const_mul _) hhn
    (fun n => (F n).initial_bound) (fun n => (F n).solution) (fun n => (F n).cap_bound)


end BoltzmannNonuniqueness.JetCopyDatum.BelowCap

end

end

section

/-! # Compactness bounds for positive cutoff approximations below the cap -/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace BoltzmannNonuniqueness.JetCopyDatum.BelowCap

structure CompactFamily (s₀ η K α γ d₀ q : ℝ) where
  time : ℝ
  time_pos : 0 < time
  time_le : time ≤ 1/32
  approximation : ∀ N, Approximation s₀ η K α γ d₀ q time N
  density_ui : UniformIntegrable (fun N => torusPhysical q (approximation N).solution.value) 1
    ((AnnularEnvelope.timePositionVolume time).prod (volume : Measure Velocity))
  pairs_ui : UniformIntegrable (fun N => CollisionCompactness.pairDensity
    (torusPhysical q (approximation N).solution.value)) 1
    ((AnnularEnvelope.timePositionVolume time).prod (volume : Measure (Velocity × Velocity)))
  gain_ui : UniformIntegrable (fun (N : ℕ) => KineticCollisionNullSets.gain (N+1)
    (torusPhysical q (approximation N).solution.value)) 1
    ((AnnularEnvelope.timePositionVolume time).prod (volume : Measure Velocity))
  loss_ui : UniformIntegrable (fun (N : ℕ) => CollisionCompactness.cutoffLossDensity (N+1)
    (torusPhysical q (approximation N).solution.value)) 1
    ((AnnularEnvelope.timePositionVolume time).prod (volume : Measure Velocity))
  initial_l1 : Tendsto (fun N => ∫ p,
    ‖periodicInitial s₀ η K α γ d₀ q N (approximation N).coefficient p-
      JetPeriodicDatum.datum s₀ η K α γ d₀ p‖) atTop (𝓝 0)

theorem CompactFamily.source_ui {s₀ η K α γ d₀ q : ℝ}
    (F : CompactFamily s₀ η K α γ d₀ q) :
    UniformIntegrable (fun (N : ℕ) => CollisionCompactness.collisionSource (N+1)
      (torusPhysical q (F.approximation N).solution.value)) 1
      ((AnnularEnvelope.timePositionVolume F.time).prod (volume : Measure Velocity)) :=
  CollisionCompactness.collisionSource_uniformIntegrable
    (fun N => torusPhysical_measurable (F.approximation N).solution.measurable_value q)
    (fun N => torusPhysical_nonneg (fun z => ((F.approximation N).solution.value_bounds z).1) q)
    F.pairs_ui (fun N => N+1) F.gain_ui F.loss_ui


end BoltzmannNonuniqueness.JetCopyDatum.BelowCap

end

end

section

/-! # Approximation sequences below the cap in the Euclidean fundamental cell -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace BoltzmannNonuniqueness.JetCopyDatum.BelowCap

theorem CompactFamily.density_ui_cell {s₀ η K α γ d₀ q : ℝ}
    (F : CompactFamily s₀ η K α γ d₀ q) :
    UniformIntegrable (fun n => EuclideanFlight.density q (F.approximation n).solution.value) 1
      (TorusKineticChart.cellVolume F.time) := by
  apply Compactness.uniformIntegrable_of_comp_measurePreserving
    (TorusKineticChart.measurePreserving F.time)
    (fun n => EuclideanFlight.density_measurable (F.approximation n).solution.measurable_value q)
  simpa only [TorusKineticChart.density_comp] using F.density_ui

theorem CompactFamily.source_ui_cell {s₀ η K α γ d₀ q : ℝ}
    (F : CompactFamily s₀ η K α γ d₀ q) :
    UniformIntegrable (fun n : ℕ => EuclideanFlight.source (n+1) q (F.approximation n).solution.value) 1
      (TorusKineticChart.cellVolume F.time) := by
  have hm (n : ℕ) : Measurable (EuclideanFlight.source (n+1) q (F.approximation n).solution.value) := by
    rw [EuclideanFlight.source_eq_collision]
    exact CollisionCompactness.collisionSource_measurable
      (EuclideanFlight.density_measurable (F.approximation n).solution.measurable_value q) (n+1)
  apply Compactness.uniformIntegrable_of_comp_measurePreserving
    (TorusKineticChart.measurePreserving F.time) hm
  simpa only [TorusKineticChart.source_comp] using F.source_ui


end BoltzmannNonuniqueness.JetCopyDatum.BelowCap

end

end

section

/-! # The torus initial-value identity for approximations below the cap -/

noncomputable section
open MeasureTheory Set

namespace BoltzmannNonuniqueness.JetCopyDatum.BelowCap
theorem Approximation.spacetime_mild (hcarleman : Published.GPV2009CarlemanInput)
    {s₀ η K α γ d₀ q T : ℝ} {N : ℕ} (F : Approximation s₀ η K α γ d₀ q T N)
    (hq₁ : 1 < q) (hq₂ : q < 2) (hT : 0 ≤ T) :
    TorusFlight.along (TorusFlight.regroup (torusPhysical q F.solution.value)) =ᵐ[
      (volume.restrict (Icc 0 T)).prod (volume : Measure Phase)]
    (fun z => periodicInitial s₀ η K α γ d₀ q N F.coefficient z.2 +
      Published.timePrimitive (volume.restrict (Icc 0 T))
        (TorusFlight.along (TorusFlight.regroup
          (CollisionCompactness.collisionSource (N+1) (torusPhysical q F.solution.value)))) z) := by
  have hm := (measurable_seed s₀ η K α γ d₀ q N).add
    ((HotSeedProfile.normalized_measurable q (DatumBounds.scale s₀ η (N+1))).const_mul F.coefficient)
  have h := TorusFlight.spacetime_mild hcarleman F.solution hq₁ hq₂
    (by positivity) (by have := F.amplitude_pos; positivity) hT le_rfl le_rfl hm
  filter_upwards [h] with z hz
  convert hz using 1
  congr 1
  exact mul_comm _ _


end BoltzmannNonuniqueness.JetCopyDatum.BelowCap

end

end

section

/-! # Every-time characteristic traces of approximations below the cap -/

noncomputable section
open MeasureTheory Set

namespace BoltzmannNonuniqueness.JetCopyDatum.BelowCap

theorem Approximation.characteristic_slice (hcarleman : Published.GPV2009CarlemanInput)
    {s₀ η K α γ d₀ q T : ℝ} {N : ℕ} (F : Approximation s₀ η K α γ d₀ q T N)
    (hq₁ : 1 < q) (hq₂ : q < 2) {t : ℝ} (ht : t ∈ Icc 0 T) :
    (fun p => torusPhysical q F.solution.value
      ((t,(TorusFlight.flight t p).1),(TorusFlight.flight t p).2)) =ᵐ[volume]
    TorusFlight.characteristicProfile (volume.restrict (Icc 0 T))
      (periodicInitial s₀ η K α γ d₀ q N F.coefficient)
      (TorusFlight.along (TorusFlight.regroup
        (CollisionCompactness.collisionSource (N+1) (torusPhysical q F.solution.value)))) t := by
  have hm := (measurable_seed s₀ η K α γ d₀ q N).add
    ((HotSeedProfile.normalized_measurable q (DatumBounds.scale s₀ η (N+1))).const_mul F.coefficient)
  have h := TorusFlight.characteristic hcarleman F.solution hq₁ hq₂
    (by positivity) (by have := F.amplitude_pos; positivity) ht.1 ht.2 le_rfl hm
  filter_upwards [h] with p hp
  change _ = periodicInitial s₀ η K α γ d₀ q N F.coefficient p+
    Published.timePrimitive (volume.restrict (Icc 0 T)) _ (t,p)
  rw [Published.timePrimitive_eq_interval ht]
  convert hp using 1
  congr 1
  exact mul_comm _ _


end BoltzmannNonuniqueness.JetCopyDatum.BelowCap

end

end

section

/-! # Pair-product compactness below the cap in the Euclidean fundamental cell -/

noncomputable section
open MeasureTheory

namespace BoltzmannNonuniqueness.JetCopyDatum.BelowCap

theorem CompactFamily.raw_pairs_ui_cell {s₀ η K α γ d₀ q : ℝ}
    (F : CompactFamily s₀ η K α γ d₀ q) :
    UniformIntegrable (fun n => CollisionCompactness.pairProduct
      (EuclideanFlight.density q (F.approximation n).solution.value)) 1
      (TorusKineticChart.pairCellVolume F.time) := by
  have hm (n) := torusPhysical_measurable (F.approximation n).solution.measurable_value q
  have hn (n) (z) := torusPhysical_nonneg
    (fun u => ((F.approximation n).solution.value_bounds u).1) q z
  have hp := CollisionCompactness.pairProduct_uniformIntegrable hm hn F.pairs_ui
  apply Compactness.uniformIntegrable_of_comp_measurePreserving
    (TorusKineticChart.pair_measurePreserving F.time)
    (fun n => CollisionCompactness.pairProduct_measurable
      (EuclideanFlight.density_measurable (F.approximation n).solution.measurable_value q))
  simpa only [TorusKineticChart.pair_comp] using hp


end BoltzmannNonuniqueness.JetCopyDatum.BelowCap

end

end

section

/-! # Uniform integrability of localized Euclidean transport sources below the cap -/

noncomputable section
open MeasureTheory Set
open scoped NNReal ENNReal
open BoltzmannNonuniqueness.Published BoltzmannNonuniqueness.TransportCutoff

namespace BoltzmannNonuniqueness.JetCopyDatum.BelowCap

theorem CompactFamily.localized_source_ui {s₀ η K α γ d₀ q : ℝ}
    (F : CompactFamily s₀ η K α γ d₀ q) {χ : Published.KineticPhase → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ {z | z.1.2 ∈ TorusChart.cube}) :
    UniformIntegrable (fun n : ℕ => TransportCutoff.localizedSource F.time χ
      (EuclideanFlight.density q (F.approximation n).solution.value)
      (EuclideanFlight.source (n+1) q (F.approximation n).solution.value)) 1 volume :=
  TorusKineticChart.localizedSource_uniformIntegrable hχ hc hs F.density_ui_cell F.source_ui_cell


end BoltzmannNonuniqueness.JetCopyDatum.BelowCap

end

end

section

/-! # Velocity averaging for approximations below the cap -/

noncomputable section
open MeasureTheory Set
open BoltzmannNonuniqueness.Published BoltzmannNonuniqueness.TransportCutoff

namespace BoltzmannNonuniqueness.JetCopyDatum.BelowCap

theorem CompactFamily.averaging_subsequence (hGLPS : Published.GLPS1988Proposition3)
    {s₀ η K α γ d₀ q : ℝ} (F : CompactFamily s₀ η K α γ d₀ q)
    {χ : Published.KineticPhase → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ {z | z.1.2 ∈ TorusChart.cube})
    (ψ : ℕ → Velocity → ℝ) (hψ : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (ψ j))
    (hψc : ∀ j, HasCompactSupport (ψ j)) :
    ∃ (φ : ℕ → ℕ) (g : ℕ → Published.SpaceTime → ℝ), StrictMono φ ∧
      ∀ j, Published.LocalL1Converges (fun n => Published.resolventAverage
        (localizedSource F.time χ (EuclideanFlight.density q (F.approximation (φ n)).solution.value)
          (EuclideanFlight.source ((φ n)+1) q (F.approximation (φ n)).solution.value)) (ψ j)) (g j) := by
  have hcompact : IsCompact (Prod.snd '' tsupport χ) := hc.image continuous_snd
  obtain ⟨R,hR,hball⟩ := hcompact.isBounded.subset_ball_lt 0 (0 : Velocity)
  have hv : tsupport χ ⊆ {z : KineticPhase | ‖z.2‖ ≤ R} := by
    intro z hz
    have hb := hball (mem_image_of_mem Prod.snd hz)
    exact (by simpa only [Metric.mem_ball,dist_zero_right] using hb : ‖z.2‖ < R).le
  let r : ℕ → KineticPhase → ℝ := fun n => localizedSource F.time χ
    (EuclideanFlight.density q (F.approximation n).solution.value)
    (EuclideanFlight.source (n+1) q (F.approximation n).solution.value)
  have hr : ∀ n, ∀ᵐ z ∂(volume : Measure KineticPhase), R < ‖z.2‖ → r n z = 0 := by
    intro n
    exact ae_of_all _ (fun z hz => localizedSource_velocity_support hv _ _ z hz)
  exact hGLPS.countable_tests (R := R) r hR hr (F.localized_source_ui hχ hc hs) ψ hψ hψc


end BoltzmannNonuniqueness.JetCopyDatum.BelowCap

end

end

section

/-! # Local strong convergence of velocity averages below the cap -/

noncomputable section
open MeasureTheory Set
open BoltzmannNonuniqueness.TransportCutoff

namespace BoltzmannNonuniqueness.JetCopyDatum.BelowCap

theorem Approximation.averages_resolvent (hcarleman : Published.GPV2009CarlemanInput)
    {s₀ η K α γ d₀ q T : ℝ} {N : ℕ} (F : Approximation s₀ η K α γ d₀ q T N)
    (hq₁ : 1 < q) (hq₂ : q < 2)
    {χ : Published.KineticPhase → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hzero : ∀ p : Velocity × Velocity, χ (TransportCutoff.characteristic p 0) = 0) (ψ : Velocity → ℝ) :
    (fun z : Published.SpaceTime => ∫ v, ψ v*(χ (z,v)*EuclideanFlight.density q F.solution.value (z,v)))
      =ᵐ[Published.timeSpaceVolume T]
      Published.resolventAverage (localizedSource T χ (EuclideanFlight.density q F.solution.value)
        (EuclideanFlight.source (N+1) q F.solution.value)) ψ := by
  have hi : Measurable (initial s₀ η K α γ d₀ q N
      (fun p => F.coefficient*HotSeedProfile.normalized q (DatumBounds.scale s₀ η (N+1)) p)) :=
    (measurable_seed s₀ η K α γ d₀ q N).add
      ((HotSeedProfile.normalized_measurable q (DatumBounds.scale s₀ η (N+1))).const_mul F.coefficient)
  have hA : 0 < F.amplitude := F.amplitude_pos
  exact EuclideanFlight.velocity_averages_resolvent hcarleman F.solution hq₁ hq₂
    (by positivity) (by positivity) le_rfl hi hχ hzero ψ

theorem CompactFamily.physical_averages_subsequence
    (hcarleman : Published.GPV2009CarlemanInput) (hGLPS : Published.GLPS1988Proposition3)
    {s₀ η K α γ d₀ q : ℝ} (F : CompactFamily s₀ η K α γ d₀ q)
    (hq₁ : 1 < q) (hq₂ : q < 2)
    {χ : Published.KineticPhase → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hc : HasCompactSupport χ) (hs : tsupport χ ⊆ {z | z.1.2 ∈ TorusChart.cube})
    (hzero : ∀ p : Velocity × Velocity, χ (TransportCutoff.characteristic p 0) = 0)
    (ψ : ℕ → Velocity → ℝ) (hψ : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (ψ j))
    (hψc : ∀ j, HasCompactSupport (ψ j)) :
    ∃ (φ : ℕ → ℕ) (g : ℕ → Published.SpaceTime → ℝ), StrictMono φ ∧
      ∀ j, Published.TimeLocalL1Converges F.time (fun n z => ∫ v, ψ j v*
        (χ (z,v)*EuclideanFlight.density q (F.approximation (φ n)).solution.value (z,v))) (g j) := by
  obtain ⟨φ,g,hφ,hg⟩ := F.averaging_subsequence hGLPS hχ hc hs ψ hψ hψc
  refine ⟨φ,g,hφ,fun j => (hg j).time_restrict (fun n => ?_)⟩
  exact (F.approximation (φ n)).averages_resolvent hcarleman hq₁ hq₂ hχ hzero (ψ j)


end BoltzmannNonuniqueness.JetCopyDatum.BelowCap

end

end

section

/-! # Tightness of approximation families below the cap -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal
open BoltzmannNonuniqueness.VelocityWeight BoltzmannNonuniqueness.WeightedLocalControl

namespace BoltzmannNonuniqueness.JetCopyDatum.BelowCap

theorem capped_family_unifTight {s₀ η K α γ d₀ q T : ℝ}
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq : q < 2) (hT : 0 ≤ T) (hTmax : T ≤ 1/32)
    (b L R δ : ℕ → ℝ) (h₀ : ℕ → JetPrototype.Phase → ℝ)
    (hb : ∀ n, 0 ≤ b n) (hL : ∀ n, 0 ≤ L n) (hR : ∀ n, 0 ≤ R n)
    (hδ : ∀ n, 0 < δ n) (hδmax : ∀ n, δ n ≤ 1)
    (hloss : ∀ n, R n*CutoffLipschitz.frequencyConstant q (b n) ≤ L n)
    (hh₀m : ∀ n, Measurable (h₀ n)) (hh₀ : ∀ n p, 0 ≤ h₀ n p)
    (hF₀ : ∀ n p, initial s₀ η K α γ d₀ q n (h₀ n) p ≤ R n)
    (F : ∀ n, PeriodicMildState q (b n) (L n) T (R n) (initial s₀ η K α γ d₀ q n (h₀ n)))
    (hcap : ∀ n, (F n).hotPeak (δ n) (color s₀ η K α γ d₀ q n) ≤ 1) :
    UnifTight (fun n => torusPhysical q (F n).value) 1
      ((AnnularEnvelope.timePositionVolume T).prod (volume : Measure Velocity)) ∧
    UnifTight (fun n => CollisionCompactness.pairDensity (torusPhysical q (F n).value)) 1
      ((AnnularEnvelope.timePositionVolume T).prod (volume : Measure (Velocity × Velocity))) ∧
    UnifTight (fun n => CollisionCompactness.gainDensity (torusPhysical q (F n).value)) 1
      ((AnnularEnvelope.timePositionVolume T).prod (volume : Measure Velocity)) ∧
    UnifTight (fun n => CollisionCompactness.lossDensity (torusPhysical q (F n).value)) 1
      ((AnnularEnvelope.timePositionVolume T).prod (volume : Measure Velocity)) := by
  apply CollisionCompactness.annular_unifTight hs₀ hη hηmax hT hq
    (momentBase_nonneg hs₀ hK hd₀ η α q) (JetEnvelopeGain.momentConstant_nonneg hK α γ)
    (fun n => torusPhysical_measurable (F n).measurable_value q)
    (fun n => torusPhysical_nonneg (fun u => ((F n).value_bounds u).1) q)
  · intro n
    exact capped_spacetime_moment hs₀ hsmax hη hηmax hK hα hαmax hγ hd₀ hd₀max hsmall
      hq (hb n) (hL n) hT (hR n) hTmax (hδ n) (hδmax n) (hloss n) n
      (hh₀m n) (hh₀ n) (hF₀ n) (F n) (hcap n)
  · intro J
    refine ⟨2+escapedConstant s₀ η K α d₀+finiteAmplitude s₀ η K α d₀ J,?_,?_⟩
    · exact add_nonneg (add_nonneg (by norm_num)
        (JetEscapedEnvelope.constant_nonneg hs₀ hK hd₀ η α _))
        (finiteAmplitude_nonneg hs₀ hK hd₀ η α J)
    · intro n
      exact capped_spacetime_outer_bound hs₀ hsmax hη hηmax hK hα hαmax hγ hd₀ hd₀max hsmall
        hq (hb n) (hL n) hT (hR n) hTmax (hδ n) (hδmax n) (hloss n) n J
        (hh₀m n) (hh₀ n) (hF₀ n) (F n) (hcap n)

theorem cap_family_unifTight {s₀ η K α γ d₀ q T : ℝ}
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hα : 0 < α) (hαmax : α ≤ 1) (hγ : 0 < γ)
    (hd₀ : 0 < d₀) (hd₀max : d₀ ≤ 1)
    (hsmall : JetComparisonCoefficient.coefficient K*d₀*s₀^9 ≤ 1)
    (hq : q < 2) (hT : 0 ≤ T) (hTmax : T ≤ 1/32)
    (F : ∀ N, Approximation s₀ η K α γ d₀ q T N) :
    UnifTight (fun N => torusPhysical q (F N).solution.value) 1
      ((AnnularEnvelope.timePositionVolume T).prod (volume : Measure Velocity)) ∧
    UnifTight (fun N => CollisionCompactness.pairDensity (torusPhysical q (F N).solution.value)) 1
      ((AnnularEnvelope.timePositionVolume T).prod (volume : Measure (Velocity × Velocity))) ∧
    UnifTight (fun N => CollisionCompactness.gainDensity (torusPhysical q (F N).solution.value)) 1
      ((AnnularEnvelope.timePositionVolume T).prod (volume : Measure Velocity)) ∧
    UnifTight (fun N => CollisionCompactness.lossDensity (torusPhysical q (F N).solution.value)) 1
      ((AnnularEnvelope.timePositionVolume T).prod (volume : Measure Velocity)) := by
  have hδ (n) : 0 < DatumBounds.scale s₀ η (n+1) := DatumBounds.scale_pos hs₀ _
  have hδmax (n) : DatumBounds.scale s₀ η (n+1) ≤ 1 := by
    have h := JetGeometry.scale_antitone hs₀.le hη.le (Nat.zero_le (n+1))
    rw [show DatumBounds.scale s₀ η 0 = s₀ by simp [DatumBounds.scale]] at h
    linarith
  have hhn (n) (p) : 0 ≤ (F n).coefficient*
      HotSeedProfile.normalized q (DatumBounds.scale s₀ η (n+1)) p := by
    obtain ⟨_,_,hb⟩ := HotSeedProfile.normalized_bounds (hδ n) (hδmax n) q
    exact mul_nonneg (F n).coefficient_mem.1 (hb p).1
  exact capped_family_unifTight hs₀ hsmax hη hηmax hK hα hαmax hγ hd₀ hd₀max
    hsmall hq hT hTmax (fun n => n+1) (fun n => damping q (n+1) (F n).amplitude)
    (fun n => 2*(F n).amplitude) (fun n => DatumBounds.scale s₀ η (n+1))
    (fun n p => (F n).coefficient*HotSeedProfile.normalized q (DatumBounds.scale s₀ η (n+1)) p)
    (fun _ => by positivity) (fun n => (bounds (by positivity) (F n).amplitude_pos).1)
    (fun n => mul_nonneg (by norm_num) (F n).amplitude_pos.le) hδ hδmax (fun _ => le_rfl)
    (fun n => (HotSeedProfile.normalized_measurable q _).const_mul _) hhn
    (fun n => (F n).initial_bound) (fun n => (F n).solution) (fun n => (F n).cap_bound)


end BoltzmannNonuniqueness.JetCopyDatum.BelowCap

end

end

section

/-! # Approximation families below the cap with uniform velocity tightness -/

noncomputable section
open MeasureTheory

namespace BoltzmannNonuniqueness.JetCopyDatum.BelowCap

structure TightFamily (s₀ η K α γ d₀ q : ℝ) extends CompactFamily s₀ η K α γ d₀ q where
  density_tight : UnifTight (fun N => torusPhysical q (approximation N).solution.value) 1
    ((AnnularEnvelope.timePositionVolume time).prod (volume : Measure Velocity))
  pairs_tight : UnifTight (fun N => CollisionCompactness.pairDensity
    (torusPhysical q (approximation N).solution.value)) 1
    ((AnnularEnvelope.timePositionVolume time).prod (volume : Measure (Velocity × Velocity)))
  gain_tight : UnifTight (fun N => CollisionCompactness.gainDensity
    (torusPhysical q (approximation N).solution.value)) 1
    ((AnnularEnvelope.timePositionVolume time).prod (volume : Measure Velocity))
  loss_tight : UnifTight (fun N => CollisionCompactness.lossDensity
    (torusPhysical q (approximation N).solution.value)) 1
    ((AnnularEnvelope.timePositionVolume time).prod (volume : Measure Velocity))


end BoltzmannNonuniqueness.JetCopyDatum.BelowCap

end

end

section

/-! # Weak density and pair-product limits of approximations below the cap -/

noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology

namespace BoltzmannNonuniqueness.JetCopyDatum.BelowCap

private theorem uniformIntegrable_comp {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {f : ℕ → X → ℝ} (hf : UniformIntegrable f 1 μ) (a : ℕ → ℕ) :
    UniformIntegrable (fun n => f (a n)) 1 μ := by
  obtain ⟨hu,C,hC⟩ := hf
  exact ⟨hu.comp a,C,fun n => hC (a n)⟩

theorem TightFamily.exists_weak_limits (hDP : Published.DunfordPettis1940Theorem321)
    {s₀ η K α γ d₀ q : ℝ} (F : TightFamily s₀ η K α γ d₀ q) :
    ∃ (φ : ℕ → ℕ) (g : (ℝ × Position) × Velocity → ℝ)
      (W : (ℝ × Position) × (Velocity × Velocity) → ℝ), StrictMono φ ∧
      Published.WeakL1Converges ((AnnularEnvelope.timePositionVolume F.time).prod volume)
        (fun n => torusPhysical q (F.approximation (φ n)).solution.value) g ∧
      Published.WeakL1Converges ((AnnularEnvelope.timePositionVolume F.time).prod volume)
        (fun n => CollisionCompactness.pairProduct
          (torusPhysical q (F.approximation (φ n)).solution.value)) W ∧
      (∀ᵐ z ∂(AnnularEnvelope.timePositionVolume F.time).prod volume, 0 ≤ g z) ∧
      (∀ᵐ z ∂(AnnularEnvelope.timePositionVolume F.time).prod volume, 0 ≤ W z) := by
  let f := fun N => torusPhysical q (F.approximation N).solution.value
  have hfm (N) : Measurable (f N) :=
    torusPhysical_measurable (F.approximation N).solution.measurable_value q
  have hfn (N) (z) : 0 ≤ f N z :=
    torusPhysical_nonneg (fun u => ((F.approximation N).solution.value_bounds u).1) q z
  have hpairUI := CollisionCompactness.pairProduct_uniformIntegrable hfm hfn F.pairs_ui
  have hpairTight := CollisionCompactness.pairProduct_unifTight hfm hfn F.pairs_tight
  obtain ⟨a,g,ha,hg⟩ := (hDP F.time F.time_pos.le).1 f hfm F.density_ui F.density_tight
  obtain ⟨b,W,hb,hW⟩ := (hDP F.time F.time_pos.le).2
    (fun n => CollisionCompactness.pairProduct (f (a n)))
    (fun n => CollisionCompactness.pairProduct_measurable (hfm (a n)))
    (uniformIntegrable_comp hpairUI a) (hpairTight.comp a)
  have hg' := hg.comp hb.tendsto_atTop
  refine ⟨a ∘ b,g,W,ha.comp hb,hg',hW,?_,?_⟩
  · exact hg'.nonneg (fun n => ae_of_all _ (hfn (a (b n))))
  · exact hW.nonneg (fun n => ae_of_all _ (CollisionCompactness.pairProduct_nonneg (hfn (a (b n)))))


end BoltzmannNonuniqueness.JetCopyDatum.BelowCap

end

end

section

/-! # Simultaneous velocity averaging with weak density and pair limits below the cap -/

noncomputable section
open MeasureTheory Set
open BoltzmannNonuniqueness.TransportCutoff

namespace BoltzmannNonuniqueness.JetCopyDatum.BelowCap

theorem CompactFamily.countable_physical_averages
    (hcarleman : Published.GPV2009CarlemanInput) (hGLPS : Published.GLPS1988Proposition3)
    {s₀ η K α γ d₀ q : ℝ} (F : CompactFamily s₀ η K α γ d₀ q)
    (hq₁ : 1 < q) (hq₂ : q < 2) (a : ℕ → ℕ)
    (χ : ℕ → Published.KineticPhase → ℝ)
    (hχ : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (χ j)) (hc : ∀ j, HasCompactSupport (χ j))
    (hs : ∀ j, tsupport (χ j) ⊆ {z | z.1.2 ∈ TorusChart.cube})
    (hzero : ∀ j (p : Velocity × Velocity), χ j (TransportCutoff.characteristic p 0) = 0)
    (ψ : ℕ → Velocity → ℝ) (hψ : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (ψ j))
    (hψc : ∀ j, HasCompactSupport (ψ j)) :
    ∃ (φ : ℕ → ℕ) (g : ℕ → Published.SpaceTime → ℝ), StrictMono φ ∧
      ∀ j, Published.TimeLocalL1Converges F.time (fun n z => ∫ v, ψ j v*
        (χ j (z,v)*EuclideanFlight.density q (F.approximation (a (φ n))).solution.value (z,v)))
        (g j) := by
  have hex (j) : ∃ R : ℝ, 0 < R ∧ tsupport (χ j) ⊆
      {z : Published.KineticPhase | ‖z.2‖ ≤ R} := by
    obtain ⟨R,hR,hball⟩ := ((hc j).image continuous_snd).isBounded.subset_ball_lt 0 (0 : Velocity)
    refine ⟨R,hR,fun z hz => ?_⟩
    have hb := hball (mem_image_of_mem Prod.snd hz)
    exact (by simpa only [Metric.mem_ball,dist_zero_right] using hb : ‖z.2‖ < R).le
  choose R hR hv using hex
  let r : ℕ → ℕ → Published.KineticPhase → ℝ := fun j n => localizedSource F.time (χ j)
    (EuclideanFlight.density q (F.approximation (a n)).solution.value)
    (EuclideanFlight.source (a n+1) q (F.approximation (a n)).solution.value)
  have hr (j n) : ∀ᵐ z ∂(volume : Measure Published.KineticPhase), R j < ‖z.2‖ → r j n z = 0 :=
    ae_of_all _ (fun z hz => localizedSource_velocity_support (hv j) _ _ z hz)
  have hui (j) : UniformIntegrable (r j) 1 volume :=
    Compactness.uniformIntegrable_comp (F.localized_source_ui (hχ j) (hc j) (hs j)) a
  obtain ⟨φ,g,hφ,hg⟩ := hGLPS.countable_sources_tests r R hR hr hui ψ hψ hψc
  refine ⟨φ,g,hφ,fun j => (hg j).time_restrict (fun n => ?_)⟩
  exact (F.approximation (a (φ n))).averages_resolvent hcarleman hq₁ hq₂ (hχ j) (hzero j) (ψ j)

theorem TightFamily.exists_weak_and_average_limits
    (hcarleman : Published.GPV2009CarlemanInput) (hGLPS : Published.GLPS1988Proposition3)
    (hDP : Published.DunfordPettis1940Theorem321)
    {s₀ η K α γ d₀ q : ℝ} (F : TightFamily s₀ η K α γ d₀ q)
    (hq₁ : 1 < q) (hq₂ : q < 2)
    (χ : ℕ → Published.KineticPhase → ℝ)
    (hχ : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (χ j)) (hc : ∀ j, HasCompactSupport (χ j))
    (hs : ∀ j, tsupport (χ j) ⊆ {z | z.1.2 ∈ TorusChart.cube})
    (hzero : ∀ j (p : Velocity × Velocity), χ j (TransportCutoff.characteristic p 0) = 0)
    (ψ : ℕ → Velocity → ℝ) (hψ : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (ψ j))
    (hψc : ∀ j, HasCompactSupport (ψ j)) :
    ∃ (φ : ℕ → ℕ) (g : (ℝ × Position) × Velocity → ℝ)
      (W : (ℝ × Position) × (Velocity × Velocity) → ℝ)
      (A : ℕ → Published.SpaceTime → ℝ), StrictMono φ ∧
      Published.WeakL1Converges ((AnnularEnvelope.timePositionVolume F.time).prod volume)
        (fun n => torusPhysical q (F.approximation (φ n)).solution.value) g ∧
      Published.WeakL1Converges ((AnnularEnvelope.timePositionVolume F.time).prod volume)
        (fun n => CollisionCompactness.pairProduct
          (torusPhysical q (F.approximation (φ n)).solution.value)) W ∧
      (∀ j, Published.TimeLocalL1Converges F.time (fun n z => ∫ v, ψ j v*
        (χ j (z,v)*EuclideanFlight.density q (F.approximation (φ n)).solution.value (z,v))) (A j)) ∧
      (∀ᵐ z ∂(AnnularEnvelope.timePositionVolume F.time).prod volume, 0 ≤ g z) ∧
      (∀ᵐ z ∂(AnnularEnvelope.timePositionVolume F.time).prod volume, 0 ≤ W z) := by
  obtain ⟨a,g,W,ha,hg,hW,hgn,hWn⟩ := F.exists_weak_limits hDP
  obtain ⟨b,A,hb,hA⟩ := F.toCompactFamily.countable_physical_averages hcarleman hGLPS
    hq₁ hq₂ a χ hχ hc hs hzero ψ hψ hψc
  exact ⟨a ∘ b,g,W,A,ha.comp hb,hg.comp hb.tendsto_atTop,hW.comp hb.tendsto_atTop,hA,hgn,hWn⟩


end BoltzmannNonuniqueness.JetCopyDatum.BelowCap

end

end

section

/-! # Factorized velocity-pair moments of weak limits below the cap -/

noncomputable section
open MeasureTheory Set
open BoltzmannNonuniqueness.TransportCutoff

namespace BoltzmannNonuniqueness.JetCopyDatum.BelowCap

def averageWeight (χ : Published.KineticPhase → ℝ) (ψ : Velocity → ℝ)
    (z : Published.KineticPhase) : ℝ := ψ z.2*χ z

theorem TightFamily.exists_factorized_pair_moments
    (hcarleman : Published.GPV2009CarlemanInput) (hGLPS : Published.GLPS1988Proposition3)
    (hDP : Published.DunfordPettis1940Theorem321)
    {s₀ η K α γ d₀ q : ℝ} (F : TightFamily s₀ η K α γ d₀ q)
    (hq₁ : 1 < q) (hq₂ : q < 2)
    (χ : ℕ → Published.KineticPhase → ℝ)
    (hχ : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (χ j)) (hc : ∀ j, HasCompactSupport (χ j))
    (hs : ∀ j, tsupport (χ j) ⊆ {z | z.1.2 ∈ TorusChart.cube})
    (hzero : ∀ j (p : Velocity × Velocity), χ j (TransportCutoff.characteristic p 0) = 0)
    (ψ : ℕ → Velocity → ℝ) (hψ : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (ψ j))
    (hψc : ∀ j, HasCompactSupport (ψ j)) :
    ∃ (φ : ℕ → ℕ) (g : (ℝ × Position) × Velocity → ℝ)
      (W : (ℝ × Position) × (Velocity × Velocity) → ℝ), StrictMono φ ∧
      Published.WeakL1Converges ((AnnularEnvelope.timePositionVolume F.time).prod volume)
        (fun n => torusPhysical q (F.approximation (φ n)).solution.value) g ∧
      Published.WeakL1Converges ((AnnularEnvelope.timePositionVolume F.time).prod volume)
        (fun n => CollisionCompactness.pairProduct
          (torusPhysical q (F.approximation (φ n)).solution.value)) W ∧
      (∀ i j (S : Set Published.SpaceTime), IsCompact S →
        (fun x => ∫ y : Velocity × Velocity,
          (averageWeight (χ i) (ψ i) (x,y.1)*averageWeight (χ j) (ψ j) (x,y.2))*
            TorusKineticChart.liftPair W (x,y)) =ᵐ[(TorusKineticChart.baseVolume F.time).restrict S]
          (fun x => (∫ v, averageWeight (χ i) (ψ i) (x,v)*TorusKineticChart.liftDensity g (x,v))*
            (∫ w, averageWeight (χ j) (ψ j) (x,w)*TorusKineticChart.liftDensity g (x,w)))) ∧
      (∀ᵐ z ∂(AnnularEnvelope.timePositionVolume F.time).prod volume, 0 ≤ g z) ∧
      (∀ᵐ z ∂(AnnularEnvelope.timePositionVolume F.time).prod volume, 0 ≤ W z) := by
  obtain ⟨φ,g,W,A,hφ,hg,hW,hA,hgn,hWn⟩ :=
    F.exists_weak_and_average_limits hcarleman hGLPS hDP hq₁ hq₂ χ hχ hc hs hzero ψ hψ hψc
  refine ⟨φ,g,W,hφ,hg,hW,?_,hgn,hWn⟩
  let f : ℕ → Published.KineticPhase → ℝ := fun n =>
    EuclideanFlight.density q (F.approximation (φ n)).solution.value
  have hfm (n) : Measurable (f n) :=
    EuclideanFlight.density_measurable (F.approximation (φ n)).solution.measurable_value q
  have hfi (n) : Integrable (f n) ((TorusKineticChart.baseVolume F.time).prod volume) :=
    memLp_one_iff_integrable.mp (F.toCompactFamily.density_ui_cell.memLp (φ n))
  have hpUI := Compactness.uniformIntegrable_comp F.toCompactFamily.raw_pairs_ui_cell φ
  have hgw := TorusKineticChart.weak_density_transfer
    (fun n => (F.approximation (φ n)).solution.measurable_value) hg
  have hWw := TorusKineticChart.weak_pair_transfer
    (fun n => (F.approximation (φ n)).solution.measurable_value) hW
  have hkw (j) : Continuous (averageWeight (χ j) (ψ j)) :=
    ((hψ j).continuous.comp continuous_snd).mul (hχ j).continuous
  have hkc (j) : HasCompactSupport (averageWeight (χ j) (ψ j)) := (hc j).mul_left
  have hAw (j) : Published.TimeLocalL1Converges F.time
      (fun n x => ∫ v, averageWeight (χ j) (ψ j) (x,v)*f n (x,v)) (A j) := by
    simpa only [averageWeight,mul_assoc] using hA j
  intro i j S hS
  exact Published.local_pair_moment_factorization (TorusKineticChart.baseVolume_le F.time)
    hfm hfi hpUI hgw hWw (hkw i) (hkw j) (hkc i) (hkc j) (hAw i) (hAw j) hS


end BoltzmannNonuniqueness.JetCopyDatum.BelowCap

end

end

section

/-! # Identification of the weak pair limit for approximations below the cap -/

noncomputable section
open MeasureTheory Set
open BoltzmannNonuniqueness.TransportCutoff

namespace BoltzmannNonuniqueness.JetCopyDatum.BelowCap

/-- The velocity-averaging step identifies the genuine nonlinear pair product. -/
theorem TightFamily.exists_nonlinear_weak_limit
    (hcarleman : Published.GPV2009CarlemanInput) (hGLPS : Published.GLPS1988Proposition3)
    (hDP : Published.DunfordPettis1940Theorem321)
    {s₀ η K α γ d₀ q : ℝ} (F : TightFamily s₀ η K α γ d₀ q)
    (hq₁ : 1 < q) (hq₂ : q < 2) :
    ∃ (φ : ℕ → ℕ) (g : (ℝ × Position) × Velocity → ℝ), StrictMono φ ∧
      Published.WeakL1Converges ((AnnularEnvelope.timePositionVolume F.time).prod volume)
        (fun n => torusPhysical q (F.approximation (φ n)).solution.value) g ∧
      Published.WeakL1Converges ((AnnularEnvelope.timePositionVolume F.time).prod volume)
        (fun n => CollisionCompactness.pairProduct
          (torusPhysical q (F.approximation (φ n)).solution.value))
        (CollisionCompactness.pairProduct g) ∧
      (∀ᵐ z ∂(AnnularEnvelope.timePositionVolume F.time).prod volume, 0 ≤ g z) := by
  obtain ⟨ψ,hψ,hψc,hdet⟩ := Compactness.exists_countable_smooth_determining_tests
  choose β hβ hβc _hβn hβtest using fun i => Compactness.exists_velocity_cutoff (hψc i)
  obtain ⟨χ,hχ,hχc,hχs,hcover⟩ := Compactness.exists_spacetime_cutoff_cover
    TorusKineticChart.interiorRegion_open TorusKineticChart.interiorRegion_nonempty
  let cuts : ℕ → Published.KineticPhase → ℝ := fun n =>
    Compactness.productCutoff (χ (Nat.unpair n).1) (β (Nat.unpair n).2)
  let tests : ℕ → Velocity → ℝ := fun n => ψ (Nat.unpair n).2
  have hcuts (n) : ContDiff ℝ (⊤ : ℕ∞) (cuts n) :=
    Compactness.productCutoff_smooth (hχ _) (hβ _)
  have hcutsc (n) : HasCompactSupport (cuts n) :=
    Compactness.productCutoff_compact (hχc _) (hβc _)
  have hcutss (n) : tsupport (cuts n) ⊆ {z | z.1.2 ∈ TorusChart.cube} :=
    Compactness.productCutoff_in_cell _ (hχs _)
  have hcuts0 (n) (p : Velocity × Velocity) : cuts n (TransportCutoff.characteristic p 0) = 0 :=
    Compactness.productCutoff_initial_zero _ (hχs _) p
  obtain ⟨φ,g,W,hφ,hg,hW,hmom,hgn,_hWn⟩ := F.exists_factorized_pair_moments
    hcarleman hGLPS hDP hq₁ hq₂ cuts hcuts hcutsc hcutss hcuts0 tests
    (fun n => hψ _) (fun n => hψc _)
  have hw (s i : ℕ) : averageWeight (cuts (Nat.pair s i)) (tests (Nat.pair s i)) =
      fun z => χ s z.1*ψ i z.2 := by
    dsimp only [cuts,tests]
    rw [Nat.unpair_pair]
    exact Compactness.productCutoff_preserves_test (χ s) (hβtest i)
  have hgw := TorusKineticChart.weak_density_transfer
    (fun n => (F.approximation (φ n)).solution.measurable_value) hg
  have hWw := TorusKineticChart.weak_pair_transfer
    (fun n => (F.approximation (φ n)).solution.measurable_value) hW
  have hscaled (s i j : ℕ) : ∀ᵐ x ∂TorusKineticChart.baseVolume F.time,
      (∫ y : Velocity × Velocity, ((χ s x*ψ i y.1)*(χ s x*ψ j y.2))*TorusKineticChart.liftPair W (x,y)) =
        (∫ v, (χ s x*ψ i v)*TorusKineticChart.liftDensity g (x,v))*
          (∫ w, (χ s x*ψ j w)*TorusKineticChart.liftDensity g (x,w)) := by
    apply Compactness.ae_of_all_compact_restrict
    intro S hS
    have ht := hmom (Nat.pair s i) (Nat.pair s j) S hS
    simp only [hw s i,hw s j] at ht
    filter_upwards [ht] with x hx
    exact hx
  have hpatch (s) : ∀ᵐ x ∂TorusKineticChart.baseVolume F.time, χ s x ≠ 0 →
      (fun y => TorusKineticChart.liftPair W (x,y)) =ᵐ[volume]
        (fun y : Velocity × Velocity => TorusKineticChart.liftDensity g (x,y.1)*
          TorusKineticChart.liftDensity g (x,y.2)) := by
    apply Compactness.pair_identity_on_patch hψ hψc hdet hWw.1 hgw.1 hWw.2.1 hgw.2.1 (χ s)
    exact fun i j => (hscaled s i j).mono (fun _ h _ => h)
  have hfib : ∀ᵐ x ∂TorusKineticChart.baseVolume F.time,
      (fun y => TorusKineticChart.liftPair W (x,y)) =ᵐ[volume]
        (fun y : Velocity × Velocity => TorusKineticChart.liftDensity g (x,y.1)*
          TorusKineticChart.liftDensity g (x,y.2)) := by
    filter_upwards [ae_all_iff.mpr hpatch,TorusKineticChart.interiorRegion_ae F.time] with x hx hxin
    obtain ⟨s,hs⟩ := hcover x hxin
    exact hx s hs
  have he : TorusKineticChart.liftPair W =ᵐ[TorusKineticChart.pairCellVolume F.time]
      CollisionCompactness.pairProduct (TorusKineticChart.liftDensity g) := by
    apply (Measure.ae_prod_iff_ae_ae ?_).mpr hfib
    exact measurableSet_eq_fun hWw.1 (CollisionCompactness.pairProduct_measurable hgw.1)
  have hback := (TorusKineticChart.pair_measurePreserving F.time).quasiMeasurePreserving.ae he
  have hEq : W =ᵐ[(AnnularEnvelope.timePositionVolume F.time).prod volume]
      CollisionCompactness.pairProduct g := by
    filter_upwards [hback] with z hz
    simpa only [TorusKineticChart.liftPair,TorusKineticChart.pairChart,
      CollisionCompactness.pairProduct,TorusKineticChart.liftDensity,
      TorusChart.projection_representative] using hz
  refine ⟨φ,g,hφ,hg,?_,hgn⟩
  refine ⟨CollisionCompactness.pairProduct_measurable hg.1,hW.2.1.congr hEq,?_⟩
  intro θ hθ hθB
  have ht := hW.2.2 θ hθ hθB
  have hi : (∫ z, θ z*W z ∂(AnnularEnvelope.timePositionVolume F.time).prod volume) =
      ∫ z, θ z*CollisionCompactness.pairProduct g z
        ∂(AnnularEnvelope.timePositionVolume F.time).prod volume :=
    integral_congr_ae (hEq.mono (fun z hz => congrArg (fun y => θ z*y) hz))
  rw [hi] at ht
  exact ht


end BoltzmannNonuniqueness.JetCopyDatum.BelowCap

end

end

section

/-! # Convergence to the weighted nonlinear pair product below the cap -/

noncomputable section
open MeasureTheory

namespace BoltzmannNonuniqueness.JetCopyDatum.BelowCap

theorem TightFamily.exists_weighted_nonlinear_weak_limit
    (hcarleman : Published.GPV2009CarlemanInput) (hGLPS : Published.GLPS1988Proposition3)
    (hDP : Published.DunfordPettis1940Theorem321)
    {s₀ η K α γ d₀ q : ℝ} (F : TightFamily s₀ η K α γ d₀ q)
    (hq₁ : 1 < q) (hq₂ : q < 2) :
    ∃ (φ : ℕ → ℕ) (g : (ℝ × Position) × Velocity → ℝ), StrictMono φ ∧
      Published.WeakL1Converges ((AnnularEnvelope.timePositionVolume F.time).prod volume)
        (fun n => torusPhysical q (F.approximation (φ n)).solution.value) g ∧
      Published.WeakL1Converges ((AnnularEnvelope.timePositionVolume F.time).prod volume)
        (fun n => CollisionCompactness.pairDensity
          (torusPhysical q (F.approximation (φ n)).solution.value))
        (CollisionCompactness.pairDensity g) ∧
      (∀ᵐ z ∂(AnnularEnvelope.timePositionVolume F.time).prod volume, 0 ≤ g z) := by
  obtain ⟨a,g,ha,hg,hraw,hgn⟩ := F.exists_nonlinear_weak_limit hcarleman hGLPS hDP hq₁ hq₂
  have hm (n) := CollisionCompactness.pairDensity_measurable
    (torusPhysical_measurable (F.approximation (a n)).solution.measurable_value q)
  obtain ⟨b,G,hb,hG⟩ := (hDP F.time F.time_pos.le).2
    (fun n => CollisionCompactness.pairDensity (torusPhysical q (F.approximation (a n)).solution.value))
    hm (Compactness.uniformIntegrable_comp F.pairs_ui a) (F.pairs_tight.comp a)
  let w : (ℝ × Position) × (Velocity × Velocity) → ℝ := fun z => 1+‖z.2.1‖+‖z.2.2‖
  have hw : Measurable w := by dsimp [w]; fun_prop
  have hw1 : ∀ z, 1 ≤ w z := by
    intro z
    dsimp [w]
    linarith [norm_nonneg z.2.1,norm_nonneg z.2.2]
  have hfun (u : (ℝ × Position) × Velocity → ℝ) :
      (fun z => w z*CollisionCompactness.pairProduct u z) = CollisionCompactness.pairDensity u := by
    funext z
    simp only [w,CollisionCompactness.pairProduct,CollisionCompactness.pairDensity,mul_assoc]
  have hraw' := hraw.comp hb.tendsto_atTop
  have hG' : Published.WeakL1Converges ((AnnularEnvelope.timePositionVolume F.time).prod volume)
      (fun n z => w z*CollisionCompactness.pairProduct
        (torusPhysical q (F.approximation (a (b n))).solution.value) z) G := by
    have hseq : (fun n z => w z*CollisionCompactness.pairProduct
        (torusPhysical q (F.approximation (a (b n))).solution.value) z) =
        (fun n => CollisionCompactness.pairDensity (torusPhysical q
          (F.approximation (a (b n))).solution.value)) := funext (fun n => hfun _)
    rw [hseq]
    exact hG
  have he := Published.identify_weighted_weak_limit hraw' hG' hw hw1
  have he' : G =ᵐ[(AnnularEnvelope.timePositionVolume F.time).prod volume]
      CollisionCompactness.pairDensity g := by
    rw [hfun] at he
    exact he
  exact ⟨a ∘ b,g,ha.comp hb,hg.comp hb.tendsto_atTop,
    hG.congr_limit (CollisionCompactness.pairDensity_measurable hg.1) he',hgn⟩


end BoltzmannNonuniqueness.JetCopyDatum.BelowCap

end

end

section

/-! # A nonnegative representative of the weighted nonlinear weak limit below the cap -/

noncomputable section
open MeasureTheory

namespace BoltzmannNonuniqueness.JetCopyDatum.BelowCap

theorem TightFamily.exists_positive_nonlinear_limit
    (hcarleman : Published.GPV2009CarlemanInput) (hGLPS : Published.GLPS1988Proposition3)
    (hDP : Published.DunfordPettis1940Theorem321)
    {s₀ η K α γ d₀ q : ℝ} (F : TightFamily s₀ η K α γ d₀ q)
    (hq₁ : 1 < q) (hq₂ : q < 2) :
    ∃ (φ : ℕ → ℕ) (g : (ℝ × Position) × Velocity → ℝ), StrictMono φ ∧
      Published.WeakL1Converges ((AnnularEnvelope.timePositionVolume F.time).prod volume)
        (fun n => torusPhysical q (F.approximation (φ n)).solution.value) g ∧
      Published.WeakL1Converges ((AnnularEnvelope.timePositionVolume F.time).prod volume)
        (fun n => CollisionCompactness.pairDensity
          (torusPhysical q (F.approximation (φ n)).solution.value))
        (CollisionCompactness.pairDensity g) ∧ (∀ z, 0 ≤ g z) := by
  obtain ⟨φ,g,hφ,hg,hpair,hgn⟩ := F.exists_weighted_nonlinear_weak_limit hcarleman hGLPS hDP hq₁ hq₂
  let g' : (ℝ × Position) × Velocity → ℝ := fun z => max (g z) 0
  have hm : Measurable g' := hg.1.max measurable_const
  have he : g =ᵐ[(AnnularEnvelope.timePositionVolume F.time).prod volume] g' := by
    filter_upwards [hgn] with z hz
    exact (max_eq_left hz).symm
  have hpe := CollisionCompactness.pairDensity_congr hg.1 hm he
  exact ⟨φ,g',hφ,hg.congr_limit hm he,
    hpair.congr_limit (CollisionCompactness.pairDensity_measurable hm) hpe,
    fun z => le_max_right _ _⟩


end BoltzmannNonuniqueness.JetCopyDatum.BelowCap

end

end

section

/-! # Convergence of collision sources for approximations below the cap -/

noncomputable section
open MeasureTheory Filter

namespace BoltzmannNonuniqueness.JetCopyDatum.BelowCap

theorem TightFamily.exists_cutoff_equation_limit_with_pair
    (hcarleman : Published.GPV2009CarlemanInput) (hGLPS : Published.GLPS1988Proposition3)
    (hDP : Published.DunfordPettis1940Theorem321)
    {s₀ η K α γ d₀ q : ℝ} (F : TightFamily s₀ η K α γ d₀ q)
    (hq₁ : 1 < q) (hq₂ : q < 2) :
    ∃ (φ : ℕ → ℕ) (g : (ℝ × Position) × Velocity → ℝ), StrictMono φ ∧
      Published.WeakL1Converges ((AnnularEnvelope.timePositionVolume F.time).prod volume)
        (fun n => torusPhysical q (F.approximation (φ n)).solution.value) g ∧
      Published.WeakL1Converges ((AnnularEnvelope.timePositionVolume F.time).prod volume)
        (fun n => CollisionCompactness.collisionSource (φ n+1)
          (torusPhysical q (F.approximation (φ n)).solution.value))
        (fun p => CollisionCompactness.gainDensity g p-CollisionCompactness.lossDensity g p) ∧
      Integrable (CollisionCompactness.pairDensity g)
        ((AnnularEnvelope.timePositionVolume F.time).prod volume) ∧ (∀ z, 0 ≤ g z) ∧
      Published.WeakL1Converges ((AnnularEnvelope.timePositionVolume F.time).prod volume)
        (fun n => CollisionCompactness.pairDensity
          (torusPhysical q (F.approximation (φ n)).solution.value))
        (CollisionCompactness.pairDensity g) := by
  obtain ⟨φ,g,hφ,hg,hpair,hgn⟩ := F.exists_positive_nonlinear_limit hcarleman hGLPS hDP hq₁ hq₂
  have hfm n := torusPhysical_measurable (F.approximation (φ n)).solution.measurable_value q
  have hfn n := torusPhysical_nonneg
    (fun z => ((F.approximation (φ n)).solution.value_bounds z).1) q
  have hf n := memLp_one_iff_integrable.mp (F.pairs_ui.memLp (φ n))
  have hb : Tendsto (fun n => (φ n : ℝ)+1) atTop atTop :=
    tendsto_atTop_mono (fun n => by linarith : ∀ n, (φ n : ℝ) ≤ (φ n : ℝ)+1)
      (tendsto_natCast_atTop_atTop.comp hφ.tendsto_atTop)
  have hterms := CollisionCompactness.weak_cutoff_gainLoss hfm hfn hg.1 hpair hf hb
  have hdiff := hterms.1.sub hterms.2
    (fun n => memLp_one_iff_integrable.mp (F.gain_ui.memLp (φ n)))
    (fun n => memLp_one_iff_integrable.mp (F.loss_ui.memLp (φ n)))
  have he n : (fun p => KineticCollisionNullSets.gain (φ n+1)
      (torusPhysical q (F.approximation (φ n)).solution.value) p-
      CollisionCompactness.cutoffLossDensity (φ n+1)
        (torusPhysical q (F.approximation (φ n)).solution.value) p) =ᵐ[
        (AnnularEnvelope.timePositionVolume F.time).prod volume]
      CollisionCompactness.collisionSource (φ n+1)
        (torusPhysical q (F.approximation (φ n)).solution.value) := by
    filter_upwards [CollisionCompactness.cutoff_loss_ae_eq_frequency (hfm n) (hfn n) (hf n)
      (φ n+1)] with p hp
    simp only [CollisionCompactness.collisionSource,hp]
  exact ⟨φ,g,hφ,hg,hdiff.congr_sequence he,hpair.2.1,hgn,hpair⟩

theorem TightFamily.exists_cutoff_equation_limit
    (hcarleman : Published.GPV2009CarlemanInput) (hGLPS : Published.GLPS1988Proposition3)
    (hDP : Published.DunfordPettis1940Theorem321)
    {s₀ η K α γ d₀ q : ℝ} (F : TightFamily s₀ η K α γ d₀ q)
    (hq₁ : 1 < q) (hq₂ : q < 2) :
    ∃ (φ : ℕ → ℕ) (g : (ℝ × Position) × Velocity → ℝ), StrictMono φ ∧
      Published.WeakL1Converges ((AnnularEnvelope.timePositionVolume F.time).prod volume)
        (fun n => torusPhysical q (F.approximation (φ n)).solution.value) g ∧
      Published.WeakL1Converges ((AnnularEnvelope.timePositionVolume F.time).prod volume)
        (fun n => CollisionCompactness.collisionSource (φ n+1)
          (torusPhysical q (F.approximation (φ n)).solution.value))
        (fun p => CollisionCompactness.gainDensity g p-CollisionCompactness.lossDensity g p) ∧
      Integrable (CollisionCompactness.pairDensity g)
        ((AnnularEnvelope.timePositionVolume F.time).prod volume) ∧ (∀ z, 0 ≤ g z) := by
  obtain ⟨φ,g,hφ,hg,hr,hpi,hgn,_hpair⟩ :=
    F.exists_cutoff_equation_limit_with_pair hcarleman hGLPS hDP hq₁ hq₂
  exact ⟨φ,g,hφ,hg,hr,hpi,hgn⟩


end BoltzmannNonuniqueness.JetCopyDatum.BelowCap

end

end

section

/-! # Weak convergence of initial data to the prescribed cold datum below the cap -/

noncomputable section
open MeasureTheory

namespace BoltzmannNonuniqueness.JetCopyDatum.BelowCap
theorem CompactFamily.initial_weak_limit {s₀ η K α γ d₀ q : ℝ}
    (F : CompactFamily s₀ η K α γ d₀ q)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hγ : 0 < γ) (hd₀ : 0 < d₀) (hq : 0 ≤ q) (hqmax : q < 2) :
    Published.WeakL1Converges volume
      (fun n => periodicInitial s₀ η K α γ d₀ q n (F.approximation n).coefficient)
      (JetPeriodicDatum.datum s₀ η K α γ d₀) := by
  have hi := JetPeriodicDatum.integrable_pullback
    (JetDatum.datum_integrable hs₀ hsmax hη hηmax hK hγ hd₀ α)
  exact Published.weakL1_of_integral_norm_sub
    (fun n => periodicInitial_integrable hs₀ hsmax hη hηmax hK hγ hd₀ hq hqmax α n _)
    (JetPeriodicDatum.measurable_pullback (Measurable.tsum
      (fun i => JetDatum.term_measurable s₀ η K α γ d₀ i))) hi F.initial_l1


end BoltzmannNonuniqueness.JetCopyDatum.BelowCap

end

end

section

/-! # A local mild solution from positive approximations below the cap -/

noncomputable section
open MeasureTheory Set

namespace BoltzmannNonuniqueness.JetCopyDatum.BelowCap

theorem TightFamily.exists_mild_limit_with_convergence
    (hcarleman : Published.GPV2009CarlemanInput) (hGLPS : Published.GLPS1988Proposition3)
    (hDP : Published.DunfordPettis1940Theorem321)
    {s₀ η K α γ d₀ q : ℝ} (F : TightFamily s₀ η K α γ d₀ q)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hγ : 0 < γ) (hd₀ : 0 < d₀) (hq₁ : 1 < q) (hq₂ : q < 2) :
    ∃ (φ : ℕ → ℕ) (g : (ℝ × Position) × Velocity → ℝ), StrictMono φ ∧
      Published.WeakL1Converges ((AnnularEnvelope.timePositionVolume F.time).prod volume)
        (fun n => torusPhysical q (F.approximation (φ n)).solution.value) g ∧
      MildCollisionSolution F.time (JetPeriodicDatum.datum s₀ η K α γ d₀) g ∧
      Published.WeakL1Converges ((AnnularEnvelope.timePositionVolume F.time).prod volume)
        (fun n => CollisionCompactness.pairDensity
          (torusPhysical q (F.approximation (φ n)).solution.value))
        (CollisionCompactness.pairDensity g) ∧
      Published.WeakL1Converges ((AnnularEnvelope.timePositionVolume F.time).prod volume)
        (fun n => CollisionCompactness.collisionSource (φ n+1)
          (torusPhysical q (F.approximation (φ n)).solution.value))
        (fun p => CollisionCompactness.gainDensity g p-CollisionCompactness.lossDensity g p) := by
  obtain ⟨φ,g,hφ,hg,hr,hpair,hgn,hpairweak⟩ := F.exists_cutoff_equation_limit_with_pair hcarleman hGLPS hDP hq₁ hq₂
  let μ : Measure ℝ := volume.restrict (Icc 0 F.time)
  let f : ℕ → (ℝ × Position) × Velocity → ℝ :=
    fun n => torusPhysical q (F.approximation (φ n)).solution.value
  let r : ℕ → (ℝ × Position) × Velocity → ℝ :=
    fun n => CollisionCompactness.collisionSource (φ n+1) (f n)
  let a : ℕ → Phase → ℝ :=
    fun n => periodicInitial s₀ η K α γ d₀ q (φ n) (F.approximation (φ n)).coefficient
  have hfm n : Measurable (f n) :=
    torusPhysical_measurable (F.approximation (φ n)).solution.measurable_value q
  have hrm n : Measurable (r n) := CollisionCompactness.collisionSource_measurable (hfm n) _
  have hrint n : Integrable (r n) ((AnnularEnvelope.timePositionVolume F.time).prod volume) :=
    memLp_one_iff_integrable.mp (F.toCompactFamily.source_ui.memLp (φ n))
  have hfr := TorusFlight.weak_regroup hfm hg
  have hrr := TorusFlight.weak_regroup hrm hr
  have hfa := TorusFlight.weak_along
    (fun n => (hfm n).comp MeasurableEquiv.prodAssoc.symm.measurable) hfr
  have hra := TorusFlight.weak_along
    (fun n => (hrm n).comp MeasurableEquiv.prodAssoc.symm.measurable) hrr
  have hrain n : Integrable (TorusFlight.along (TorusFlight.regroup (r n)))
      (μ.prod (volume : Measure Phase)) := by
    have hrreg : Integrable (TorusFlight.regroup (r n)) (μ.prod (volume : Measure Phase)) := by
      have hi := (measurePreserving_prodAssoc μ (volume : Measure Position)
        (volume : Measure Velocity)).symm.integrable_comp_of_integrable (hrint n)
      rw [Measure.volume_eq_prod]
      exact hi
    exact (TorusFlight.along_measurePreserving μ).integrable_comp_of_integrable hrreg
  have ham n : Measurable (a n) := periodicInitial_measurable s₀ η K α γ d₀ q _ _
  have hai n : Integrable (a n) := periodicInitial_integrable hs₀ hsmax hη hηmax hK hγ hd₀
    (by linarith : 0 ≤ q) hq₂ α _ _
  have ha := (F.toCompactFamily.initial_weak_limit hs₀ hsmax hη hηmax hK hγ hd₀
    (by linarith : 0 ≤ q) hq₂).comp hφ.tendsto_atTop
  have heq n : TorusFlight.along (TorusFlight.regroup (f n)) =ᵐ[μ.prod volume]
      (fun z => a n z.2+Published.timePrimitive μ
        (TorusFlight.along (TorusFlight.regroup (r n))) z) :=
    (F.approximation (φ n)).spacetime_mild hcarleman hq₁ hq₂ F.time_pos.le
  have hlim := TorusFlight.weak_duhamel_limit hfa hra
    (fun n => (hrm n).comp MeasurableEquiv.prodAssoc.symm.measurable |>.comp
      (TorusFlight.along_measurePreserving μ).measurable)
    hrain ha ham hai heq
  exact ⟨φ,g,hφ,hg,⟨hg.1,hgn,hg.2.1,hpair,hlim⟩,hpairweak,hr⟩

theorem TightFamily.exists_mild_limit
    (hcarleman : Published.GPV2009CarlemanInput) (hGLPS : Published.GLPS1988Proposition3)
    (hDP : Published.DunfordPettis1940Theorem321)
    {s₀ η K α γ d₀ q : ℝ} (F : TightFamily s₀ η K α γ d₀ q)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hγ : 0 < γ) (hd₀ : 0 < d₀) (hq₁ : 1 < q) (hq₂ : q < 2) :
    ∃ (φ : ℕ → ℕ) (g : (ℝ × Position) × Velocity → ℝ), StrictMono φ ∧
      Published.WeakL1Converges ((AnnularEnvelope.timePositionVolume F.time).prod volume)
        (fun n => torusPhysical q (F.approximation (φ n)).solution.value) g ∧
      MildCollisionSolution F.time (JetPeriodicDatum.datum s₀ η K α γ d₀) g := by
  obtain ⟨φ,g,hφ,hg,S,_hpair,_hr⟩ :=
    F.exists_mild_limit_with_convergence hcarleman hGLPS hDP
      hs₀ hsmax hη hηmax hK hγ hd₀ hq₁ hq₂
  exact ⟨φ,g,hφ,hg,S⟩


end BoltzmannNonuniqueness.JetCopyDatum.BelowCap

end

end

section

/-! # Every-time weak traces along the nonlinear mild-limit subsequence below the cap -/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology

namespace BoltzmannNonuniqueness.JetCopyDatum.BelowCap

theorem TightFamily.weak_each_time
    (hcarleman : Published.GPV2009CarlemanInput)
    {s₀ η K α γ d₀ q : ℝ} (F : TightFamily s₀ η K α γ d₀ q)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hγ : 0 < γ) (hd₀ : 0 < d₀) (hq₁ : 1 < q) (hq₂ : q < 2)
    {φ : ℕ → ℕ} {g : (ℝ × Position) × Velocity → ℝ} (hφ : StrictMono φ)
    (S : MildCollisionSolution F.time (JetPeriodicDatum.datum s₀ η K α γ d₀) g)
    (hr : Published.WeakL1Converges ((AnnularEnvelope.timePositionVolume F.time).prod volume)
      (fun n => CollisionCompactness.collisionSource (φ n+1)
        (torusPhysical q (F.approximation (φ n)).solution.value))
      (fun p => CollisionCompactness.gainDensity g p-CollisionCompactness.lossDensity g p))
    {t : ℝ} (ht : t ∈ Icc 0 F.time) :
    Published.WeakL1Converges volume
      (fun n p => torusPhysical q (F.approximation (φ n)).solution.value ((t,p.1),p.2))
      (MildCollisionSolution.positiveEvolution F.time (JetPeriodicDatum.datum s₀ η K α γ d₀) g t) := by
  let r : ℕ → (ℝ × Position) × Velocity → ℝ := fun n =>
    CollisionCompactness.collisionSource (φ n+1) (torusPhysical q (F.approximation (φ n)).solution.value)
  let a : ℕ → Density := fun n => periodicInitial s₀ η K α γ d₀ q (φ n)
    (F.approximation (φ n)).coefficient
  have hfm n := torusPhysical_measurable (F.approximation (φ n)).solution.measurable_value q
  have hrm n : Measurable (r n) := CollisionCompactness.collisionSource_measurable (hfm n) _
  have hri n : Integrable (r n) ((AnnularEnvelope.timePositionVolume F.time).prod volume) :=
    memLp_one_iff_integrable.mp (F.toCompactFamily.source_ui.memLp (φ n))
  have ha := (F.toCompactFamily.initial_weak_limit hs₀ hsmax hη hηmax hK hγ hd₀
    (by linarith : 0 ≤ q) hq₂).comp hφ.tendsto_atTop
  have hai n : Integrable (a n) := periodicInitial_integrable hs₀ hsmax hη hηmax hK hγ hd₀
    (by linarith : 0 ≤ q) hq₂ α _ _
  exact S.weak_kinetic_trace F.time_pos hfm hrm hri ha hai hr t ht
    (fun n => (F.approximation (φ n)).characteristic_slice hcarleman hq₁ hq₂ ht)

theorem TightFamily.exists_mild_limit_with_traces_and_convergence
    (hcarleman : Published.GPV2009CarlemanInput) (hGLPS : Published.GLPS1988Proposition3)
    (hDP : Published.DunfordPettis1940Theorem321)
    {s₀ η K α γ d₀ q : ℝ} (F : TightFamily s₀ η K α γ d₀ q)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hγ : 0 < γ) (hd₀ : 0 < d₀) (hq₁ : 1 < q) (hq₂ : q < 2) :
    ∃ (φ : ℕ → ℕ) (g : (ℝ × Position) × Velocity → ℝ), StrictMono φ ∧
      Published.WeakL1Converges ((AnnularEnvelope.timePositionVolume F.time).prod volume)
        (fun n => torusPhysical q (F.approximation (φ n)).solution.value) g ∧
      MildCollisionSolution F.time (JetPeriodicDatum.datum s₀ η K α γ d₀) g ∧
      Published.WeakL1Converges ((AnnularEnvelope.timePositionVolume F.time).prod volume)
        (fun n => CollisionCompactness.pairDensity
          (torusPhysical q (F.approximation (φ n)).solution.value))
        (CollisionCompactness.pairDensity g) ∧
      ∀ t ∈ Icc 0 F.time, Published.WeakL1Converges volume
        (fun n p => torusPhysical q (F.approximation (φ n)).solution.value ((t,p.1),p.2))
        (MildCollisionSolution.positiveEvolution F.time (JetPeriodicDatum.datum s₀ η K α γ d₀) g t) := by
  obtain ⟨φ,g,hφ,hg,S,hpair,hr⟩ := F.exists_mild_limit_with_convergence hcarleman hGLPS hDP
    hs₀ hsmax hη hηmax hK hγ hd₀ hq₁ hq₂
  exact ⟨φ,g,hφ,hg,S,hpair,fun _ ht => F.weak_each_time hcarleman
    hs₀ hsmax hη hηmax hK hγ hd₀ hq₁ hq₂ hφ S hr ht⟩

theorem TightFamily.exists_mild_limit_with_time_traces
    (hcarleman : Published.GPV2009CarlemanInput) (hGLPS : Published.GLPS1988Proposition3)
    (hDP : Published.DunfordPettis1940Theorem321)
    {s₀ η K α γ d₀ q : ℝ} (F : TightFamily s₀ η K α γ d₀ q)
    (hs₀ : 0 < s₀) (hsmax : s₀ ≤ 1/8) (hη : 0 < η) (hηmax : η ≤ Real.log 2)
    (hK : 0 ≤ K) (hγ : 0 < γ) (hd₀ : 0 < d₀) (hq₁ : 1 < q) (hq₂ : q < 2) :
    ∃ (φ : ℕ → ℕ) (g : (ℝ × Position) × Velocity → ℝ), StrictMono φ ∧
      MildCollisionSolution F.time (JetPeriodicDatum.datum s₀ η K α γ d₀) g ∧
      Published.WeakL1Converges ((AnnularEnvelope.timePositionVolume F.time).prod volume)
        (fun n => CollisionCompactness.pairDensity
          (torusPhysical q (F.approximation (φ n)).solution.value))
        (CollisionCompactness.pairDensity g) ∧
      ∀ t ∈ Icc 0 F.time, Published.WeakL1Converges volume
        (fun n p => torusPhysical q (F.approximation (φ n)).solution.value ((t,p.1),p.2))
        (MildCollisionSolution.positiveEvolution F.time (JetPeriodicDatum.datum s₀ η K α γ d₀) g t) := by
  obtain ⟨φ,g,hφ,_hg,S,hpair,hr⟩ := F.exists_mild_limit_with_convergence hcarleman hGLPS hDP
    hs₀ hsmax hη hηmax hK hγ hd₀ hq₁ hq₂
  exact ⟨φ,g,hφ,S,hpair,fun _ ht => F.weak_each_time hcarleman
    hs₀ hsmax hη hηmax hK hγ hd₀ hq₁ hq₂ hφ S hr ht⟩


end BoltzmannNonuniqueness.JetCopyDatum.BelowCap

end

end

end OAI
