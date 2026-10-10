import OAI.MathematicalPhysics.Boltzmann.Approximation.MassNormalizedCollisionLimits
import OAI.MathematicalPhysics.Boltzmann.Branching.BoundedCollisionBlocks
import OAI.MathematicalPhysics.Boltzmann.Branching.BoundedMildEntropyLimit
import OAI.MathematicalPhysics.Boltzmann.Compactness.EntropyRegularizationLimit
import OAI.MathematicalPhysics.Boltzmann.Compactness.KineticEntropyErrorLimit
import OAI.MathematicalPhysics.Boltzmann.Compactness.UniformIntegrableCoordinates
import OAI.MathematicalPhysics.Boltzmann.Jets.TorusVelocityWindowAE

namespace OAI

section

/-! # Regularized entropy inequality for the actual periodic finite approximations -/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness

namespace WeightedLocalControl.PeriodicMildState

def torusEvolution {q b L U R : ℝ} {f₀ : JetPrototype.Phase → ℝ}
    (F : PeriodicMildState q b L U R f₀) : Evolution :=
  fun t p => JetCopyDatum.torusPhysical q F.value ((t,p.1),p.2)

theorem regularized_entropy_inequality (hcarleman : Published.GPV2009CarlemanInput)
    {q b L T U R δ p : ℝ} {f₀ : JetPrototype.Phase → ℝ}
    (F : PeriodicMildState q b L U R f₀)
    (hq₁ : 1 < q) (hq₂ : q < 2) (hb : 0 ≤ b) (hR : 0 ≤ R) (hT : 0 < T) (hTU : T ≤ U)
    (hloss : R*CutoffLipschitz.frequencyConstant q b ≤ L)
    (hf₀ : Measurable f₀) (hf₀b : ∀ z, 0 ≤ f₀ z ∧ f₀ z ≤ R)
    (hδ : 0 < δ) (hδone : δ ≤ 1) (hp : 1 < p)
    (hpi : Integrable (fun v : Velocity => H q v^p)) :
    (∫ z, regularizedRelativeEntropyDensity δ (F.torusEvolution T) z)-
      (∫ z, regularizedRelativeEntropyDensity δ (TorusFlight.initialDensity q f₀) z) ≤
      (δ*entropyErrorCoefficient q R b)*∫ z : (ℝ × Position) × Velocity,
        logarithmicMajorant q (R+tiltConstant) p δ z.2
        ∂(AnnularEnvelope.timePositionVolume T).prod volume := by
  let E : Evolution := F.torusEvolution
  let a : Density := TorusFlight.initialDensity q f₀
  let r := TorusFlight.along (cutoffPhysicalSource b E)
  have hEm : Measurable (fun z : ℝ × Phase => E z.1 z.2) :=
    (JetCopyDatum.torusPhysical_measurable F.measurable_value q).comp MeasurableEquiv.prodAssoc.symm.measurable
  have hEn : ∀ t z, 0 ≤ E t z := fun t z =>
    JetCopyDatum.torusPhysical_nonneg (fun u => (F.value_bounds u).1) q _
  have hEb : ∀ t z, E t z ≤ R*H q z.2 := by
    intro t z
    have h := mul_le_mul_of_nonneg_left (F.value_bounds
      (t,(JetPeriodicDatum.spatialMap (TorusChart.representative z.1),z.2))).2 (H_nonneg q z.2)
    exact h.trans_eq (mul_comm _ _)
  have ham : Measurable a := TorusFlight.initialDensity_measurable hf₀ q
  have han : ∀ z, 0 ≤ a z := fun z => mul_nonneg (H_nonneg q z.2) (hf₀b _).1
  have hab : ∀ z, a z ≤ R*H q z.2 := by
    intro z
    exact (mul_le_mul_of_nonneg_left (hf₀b _).2 (H_nonneg q z.2)).trans_eq (mul_comm _ _)
  have hcT : (fun z => E T (TorusFlight.flight T z)) =ᵐ[volume] entropyPath a r T :=
    TorusFlight.characteristic hcarleman F hq₁ hq₂ hb hR hT.le hTU hloss hf₀
  have hc : (fun z : ℝ × Phase => E z.1 (TorusFlight.flight z.1 z.2)) =ᵐ[
      (volume.restrict (Icc 0 T)).prod volume] (fun z => entropyPath a r z.1 z.2) := by
    have h := TorusFlight.spacetime_mild hcarleman F hq₁ hq₂ hb hR hT.le hTU hloss hf₀
    have ht : ∀ᵐ z : ℝ × Phase ∂(volume.restrict (Icc 0 T)).prod volume, z.1 ∈ Icc 0 T :=
      Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Icc)
    filter_upwards [h,ht] with z hz hzt
    rw [Published.timePrimitive_eq_interval hzt] at hz
    exact hz
  have hbal := bounded_mild_entropy_balance hcarleman hT hq₁ hq₂ hR hδ hδone hb
    hEm hEn hEb ham han hab hc hcT
  have hprod := physical_regularized_entropy_production_bound (T := T) hcarleman hq₁ hq₂ hR hδ hδone hb
    hp hpi hEm hEn hEb
  exact hbal.trans_le hprod


/-- Every finite periodic mild approximation has nonincreasing relative entropy. -/
theorem entropy_nonincrease (hcarleman : Published.GPV2009CarlemanInput)
    {q b L T U R : ℝ} {f₀ : JetPrototype.Phase → ℝ}
    (F : PeriodicMildState q b L U R f₀)
    (hq₁ : 1 < q) (hq₂ : q < 2) (hb : 0 ≤ b) (hR : 0 ≤ R) (hT : 0 < T) (hTU : T ≤ U)
    (hloss : R*CutoffLipschitz.frequencyConstant q b ≤ L)
    (hf₀ : Measurable f₀) (hf₀b : ∀ z, 0 ≤ f₀ z ∧ f₀ z ≤ R) :
    relativeEntropy (F.torusEvolution T) ≤ relativeEntropy (TorusFlight.initialDensity q f₀) := by
  obtain ⟨p,hp,hpi⟩ := exists_integrable_rpow_H hq₁ hq₂
  have hEm : Measurable (fun z : ℝ × Phase => F.torusEvolution z.1 z.2) :=
    (JetCopyDatum.torusPhysical_measurable F.measurable_value q).comp MeasurableEquiv.prodAssoc.symm.measurable
  have hEn : ∀ z, 0 ≤ F.torusEvolution T z := fun z =>
    JetCopyDatum.torusPhysical_nonneg (fun u => (F.value_bounds u).1) q _
  have hEb : ∀ z, F.torusEvolution T z ≤ R*H q z.2 := by
    intro z
    exact (mul_le_mul_of_nonneg_left (F.value_bounds
      (T,(JetPeriodicDatum.spatialMap (TorusChart.representative z.1),z.2))).2
      (H_nonneg q z.2)).trans_eq (mul_comm _ _)
  have ham : Measurable (TorusFlight.initialDensity q f₀) := TorusFlight.initialDensity_measurable hf₀ q
  have han : ∀ z, 0 ≤ TorusFlight.initialDensity q f₀ z :=
    fun z => mul_nonneg (H_nonneg q z.2) (hf₀b _).1
  have hab : ∀ z, TorusFlight.initialDensity q f₀ z ≤ R*H q z.2 := by
    intro z
    exact (mul_le_mul_of_nonneg_left (hf₀b _).2 (H_nonneg q z.2)).trans_eq (mul_comm _ _)
  have hFt := regularizedRelativeEntropyDensity_tendsto hq₂ hR hp hpi
    (hEm.comp (measurable_const.prodMk measurable_id)) hEn hEb
  have hAt := regularizedRelativeEntropyDensity_tendsto hq₂ hR hp hpi ham han hab
  have herror := (kinetic_entropy_error_tendsto (AnnularEnvelope.timePositionVolume T)
    (B := R+tiltConstant) (entropyErrorCoefficient q R b) hq₂ hpi).mono_left
    (show 𝓝[>] (0:ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
  have hle := le_of_tendsto_of_tendsto (hFt.sub hAt) herror (show
      ∀ᶠ δ : ℝ in 𝓝[>] 0, (∫ z, regularizedRelativeEntropyDensity δ (F.torusEvolution T) z)-
        (∫ z, regularizedRelativeEntropyDensity δ (TorusFlight.initialDensity q f₀) z) ≤
        (δ*entropyErrorCoefficient q R b)*∫ z : (ℝ × Position) × Velocity,
          logarithmicMajorant q (R+tiltConstant) p δ z.2
          ∂(AnnularEnvelope.timePositionVolume T).prod volume from by
    filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with δ hδ
    exact F.regularized_entropy_inequality hcarleman hq₁ hq₂ hb hR hT hTU hloss hf₀ hf₀b
      hδ.1 hδ.2.le hp hpi)
  have he (f : Density) : (∫ z, scalarRelativeEntropy (maxwellian z.2) (f z)) = relativeEntropy f := by
    unfold relativeEntropy
    apply integral_congr_ae
    filter_upwards [] with z
    exact scalarRelativeEntropy_eq (maxwellian_pos z.2) (f z)
  rw [he,he] at hle
  change relativeEntropy (F.torusEvolution T)-relativeEntropy (TorusFlight.initialDensity q f₀) ≤ 0 at hle
  linarith only [hle]

end WeightedLocalControl.PeriodicMildState
end BoltzmannNonuniqueness

end

end

section

/-! # The actual finite periodic approximations satisfy entropy with dissipation -/

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open BoltzmannNonuniqueness.VelocityWeight

namespace BoltzmannNonuniqueness.WeightedLocalControl.PeriodicMildState

theorem entropy_dissipation_inequality (hcarleman : Published.GPV2009CarlemanInput)
    {q b L T U R : ℝ} {f₀ : JetPrototype.Phase → ℝ}
    (F : PeriodicMildState q b L U R f₀)
    (hq₁ : 1 < q) (hq₂ : q < 2) (hb : 0 ≤ b) (hR : 0 ≤ R) (hT : 0 < T) (hTU : T ≤ U)
    (hloss : R*CutoffLipschitz.frequencyConstant q b ≤ L)
    (hf₀ : Measurable f₀) (hf₀b : ∀ z, 0 ≤ f₀ z ∧ f₀ z ≤ R) :
    ENNReal.ofReal (relativeEntropy (F.torusEvolution T))+
      CollisionCompactness.cutoffExtendedDissipation (AnnularEnvelope.timePositionVolume T) b
        (kineticDensity F.torusEvolution) ≤
      ENNReal.ofReal (relativeEntropy (TorusFlight.initialDensity q f₀)) := by
  let E : Evolution := F.torusEvolution
  let a : Density := TorusFlight.initialDensity q f₀
  let r := TorusFlight.along (cutoffPhysicalSource b E)
  have hEm : Measurable (fun z : ℝ × Phase => E z.1 z.2) :=
    (JetCopyDatum.torusPhysical_measurable F.measurable_value q).comp MeasurableEquiv.prodAssoc.symm.measurable
  have hEn : ∀ t z, 0 ≤ E t z := fun t z =>
    JetCopyDatum.torusPhysical_nonneg (fun u => (F.value_bounds u).1) q _
  have hEb : ∀ t z, E t z ≤ R*H q z.2 := by
    intro t z
    have h := mul_le_mul_of_nonneg_left (F.value_bounds
      (t,(JetPeriodicDatum.spatialMap (TorusChart.representative z.1),z.2))).2 (H_nonneg q z.2)
    exact h.trans_eq (mul_comm _ _)
  have ham : Measurable a := TorusFlight.initialDensity_measurable hf₀ q
  have han : ∀ z, 0 ≤ a z := fun z => mul_nonneg (H_nonneg q z.2) (hf₀b _).1
  have hab : ∀ z, a z ≤ R*H q z.2 := by
    intro z
    exact (mul_le_mul_of_nonneg_left (hf₀b _).2 (H_nonneg q z.2)).trans_eq (mul_comm _ _)
  have hcT : (fun z => E T (TorusFlight.flight T z)) =ᵐ[volume] entropyPath a r T :=
    TorusFlight.characteristic hcarleman F hq₁ hq₂ hb hR hT.le hTU hloss hf₀
  have hc : (fun z : ℝ × Phase => E z.1 (TorusFlight.flight z.1 z.2)) =ᵐ[
      (volume.restrict (Icc 0 T)).prod volume] (fun z => entropyPath a r z.1 z.2) := by
    have h := TorusFlight.spacetime_mild hcarleman F hq₁ hq₂ hb hR hT.le hTU hloss hf₀
    have ht : ∀ᵐ z : ℝ × Phase ∂(volume.restrict (Icc 0 T)).prod volume, z.1 ∈ Icc 0 T :=
      Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Icc)
    filter_upwards [h,ht] with z hz hzt
    rw [Published.timePrimitive_eq_interval hzt] at hz
    exact hz
  exact bounded_mild_entropy_dissipation_limit hcarleman hq₁ hq₂ hb hR hT
    hEm hEn hEb ham han hab hc hcT

end BoltzmannNonuniqueness.WeightedLocalControl.PeriodicMildState

end

end

section

/-! # Uniform integrability of actual finite rates on elastic windows -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace BoltzmannNonuniqueness.PeriodicApproximation
open Compactness CollisionCompactness
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]

theorem scatterTriple_window_measurePreserving (R : ℝ) :
    MeasurePreserving (scatterTriple (X := X))
      (((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea).restrict (collisionWindow R))
      (((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea).restrict (collisionWindow R)) := by
  have he : scatterTriple (X := X) ⁻¹' collisionWindow R = collisionWindow R := by
    ext z
    change (‖scatterLeft z.1.2.1 z.1.2.2 z.2‖^2+
      ‖scatterRight z.1.2.1 z.1.2.2 z.2‖^2 ≤ R^2) ↔ _
    rw [scatter_energy _ _ _ (mem_sphere_zero_iff_norm.mp z.2.property)]
    rfl
  have h := (scatterTriple_measurePreserving μ).restrict_preimage (collisionWindow_measurable R)
  rwa [he] at h

theorem massRegularizedPreRate_window_uniformIntegrable
    {f : ℕ → X × Velocity → ℝ} {N : ℕ → ℝ} {C : ℝ}
    (hfm : ∀ n, Measurable (f n)) (hf : ∀ n p, 0 ≤ f n p)
    (hi : ∀ n, Integrable (entropyGauge (f n)) (μ.prod volume))
    (hb : ∀ n, (∫ p, entropyGauge (f n) p ∂μ.prod volume) ≤ C)
    (hN : ∀ n, 0 < N n) {R : ℝ} (hR : 0 ≤ R) :
    UniformIntegrable (fun n => massRegularizedPreRate (N n) (f n)) 1
      (((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea).restrict (collisionWindow R)) := by
  have hu := uniformIntegrable_restrict
    (massNormalizedPreRate_local_uniformIntegrable R hfm hf hi hb) (collisionWindow R)
  rw [Measure.restrict_restrict_of_subset (collisionWindow_subset_angularPairBox hR)] at hu
  have hm n := (massRegularizedPreRate_measurable (N n) (hfm n)).aestronglyMeasurable
    (μ := (((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea).restrict (collisionWindow R)))
  have he n : ∀ᵐ z ∂(((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea).restrict
      (collisionWindow R)), ‖massRegularizedPreRate (N n) (f n) z‖ₑ ≤ ‖massNormalizedPreRate (f n) z‖ₑ := by
    filter_upwards [] with z
    apply enorm_le_iff_norm_le.mpr
    rw [Real.norm_of_nonneg (massRegularizedPreRate_bounds (hN n) (hf n) z).1,Real.norm_eq_abs]
    exact (massRegularizedPreRate_bounds (hN n) (hf n) z).2.trans (le_abs_self _)
  obtain ⟨hu,B,hB⟩ := hu
  exact ⟨hu.ae_mono hm he,B,fun n => (eLpNorm_mono_enorm_ae (hm n) (he n)).trans (hB n)⟩

theorem massRegularizedPostRate_window_uniformIntegrable
    {f : ℕ → X × Velocity → ℝ} {N : ℕ → ℝ} {C : ℝ}
    (hfm : ∀ n, Measurable (f n)) (hf : ∀ n p, 0 ≤ f n p)
    (hi : ∀ n, Integrable (entropyGauge (f n)) (μ.prod volume))
    (hb : ∀ n, (∫ p, entropyGauge (f n) p ∂μ.prod volume) ≤ C)
    (hN : ∀ n, 0 < N n) {R : ℝ} (hR : 0 ≤ R) :
    UniformIntegrable (fun n => massRegularizedPostRate (N n) (f n)) 1
      (((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea).restrict (collisionWindow R)) := by
  let ν := ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea).restrict (collisionWindow R)
  have he : MeasurePreserving (scatterTripleEquiv (X := X)) ν ν :=
    scatterTriple_window_measurePreserving R
  have hp : UniformIntegrable (fun n => massRegularizedPreRate (N n) (f n)) 1 ν :=
    massRegularizedPreRate_window_uniformIntegrable hfm hf hi hb hN hR
  have h := Published.uniformIntegrable_comp_equiv (μ := ν) (ν := ν)
    scatterTripleEquiv he (fun n => massRegularizedPreRate (N n) (f n)) hp
  exact h

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

end OAI
