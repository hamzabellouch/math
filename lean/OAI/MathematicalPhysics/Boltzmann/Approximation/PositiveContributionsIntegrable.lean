import OAI.MathematicalPhysics.Boltzmann.Approximation.PositiveSourceFormula
import OAI.MathematicalPhysics.Boltzmann.Approximation.SurvivalVolterraIntegrable
import OAI.MathematicalPhysics.Boltzmann.Branching.ClippedCharacteristicGain
import OAI.MathematicalPhysics.Boltzmann.Collision.KernelInvariantPowers
import OAI.MathematicalPhysics.Boltzmann.Compactness.PeriodicStrongAverages
import OAI.MathematicalPhysics.Boltzmann.Compactness.WeakConservedMarginal

namespace OAI

section

/-! # A cutoff equal to one preserves every collision ending in its core -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

namespace BoltzmannNonuniqueness

variable {X : Type*} [MeasurableSpace X]

theorem withDensity_restrict_le_of_core (μ : Measure X) {f g : X → ℝ≥0∞}
    {A : Set X} (hA : MeasurableSet A) (hfg : ∀ x ∈ A, f x ≤ g x) :
    (μ.withDensity f).restrict A ≤ μ.withDensity g := by
  rw [restrict_withDensity hA,← withDensity_indicator hA]
  apply withDensity_mono
  exact Filter.Eventually.of_forall (fun x => by
    by_cases hx : x ∈ A
    · simpa only [indicator_of_mem hx] using hfg x hx
    · simp only [indicator_of_notMem hx]
      exact bot_le)

theorem positiveSourceKernel_restrict_le (K : Kernel X X) [IsSFiniteKernel K]
    {b r : X → ℝ} (hb : Measurable b) (hr : Measurable r) {A : Set X}
    (hA : MeasurableSet A) (hcore : ∀ x ∈ A, b x = 1) :
    (positiveSourceKernel K (fun _ => 1) r).restrict hA ≤ positiveSourceKernel K b r := by
  intro x
  rw [Kernel.restrict_apply,positiveSourceKernel,positiveSourceKernel,add_apply,add_apply,
    Measure.restrict_add]
  apply add_le_add
  · rw [Kernel.withDensity_apply (f := fun (_ : X) (_ : X) => ENNReal.ofReal (1:ℝ)) K (by fun_prop),
      Kernel.withDensity_apply (f := fun (_ : X) y => ENNReal.ofReal (b y)) K (by fun_prop)]
    apply withDensity_restrict_le_of_core _ hA
    intro y hy
    simp only [hcore y hy]
    exact le_rfl
  · rw [Kernel.withDensity_apply (f := fun (_ : X) y => ENNReal.ofReal ((1:ℝ)*r y)) Kernel.id (by fun_prop),
      Kernel.withDensity_apply (f := fun (_ : X) y => ENNReal.ofReal (b y*r y)) Kernel.id (by fun_prop)]
    apply withDensity_restrict_le_of_core _ hA
    intro y hy
    simp only [hcore y hy,one_mul]
    exact le_rfl

end BoltzmannNonuniqueness

end

end

section

/-! # The actual positive gain integrals converge with their physical survival factors -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace BoltzmannNonuniqueness.PeriodicApproximation

def finitePositiveSource (T N K R : ℝ) (f : (ℝ × Position) × Velocity → ℝ) : ℝ × Phase → ℝ :=
  Published.survivalVolterra (volume.restrict (Icc 0 T))
    (Published.twoTimeSurvival (volume.restrict (Icc 0 T)) (physicalCharacteristicFrequency f))
    (characteristicClippedFiniteGain N K R f)

def physicalPositiveSource (T K R : ℝ) (f : (ℝ × Position) × Velocity → ℝ) : ℝ × Phase → ℝ :=
  Published.survivalVolterra (volume.restrict (Icc 0 T))
    (Published.twoTimeSurvival (volume.restrict (Icc 0 T)) (physicalCharacteristicFrequency f))
    (characteristicClippedPhysicalGain K R f)

theorem GlobalCollisionLimit.positive_source_limit {f : Density} {hfm : Measurable f}
    (G : GlobalCollisionLimit f hfm) (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    {T R L : ℝ} (hT : 0 ≤ T) (hR : 0 ≤ R) (hL : 0 ≤ L) (K : ℝ≥0) :
    Published.WeakL1Converges
      ((volume.restrict (Icc 0 T)).prod ((volume : Measure Position).prod
        ((volume : Measure Velocity).restrict (Metric.closedBall 0 L))))
      (fun n => finitePositiveSource T ((G.weakLimit.indices n:ℝ)+1) K R
        (approximatingSolution f hfm (G.weakLimit.indices n)).kineticProfile)
      (physicalPositiveSource T K R G.weakLimit.kineticProfile) := by
  let : IsFiniteMeasure ((volume : Measure Velocity).restrict (Metric.closedBall 0 L)) :=
    isFiniteMeasure_restrict.mpr (isCompact_closedBall (0:Velocity) L).measure_lt_top.ne
  obtain ⟨hw,hu⟩ := G.characteristic_clipped_gain_limit hf hi hT hR K L
  apply hw.survivalVolterra hu
    (fun n => characteristicClippedFiniteGain_measurable ((G.weakLimit.indices n:ℝ)+1) (K:ℝ) R
      (approximatingSolution f hfm (G.weakLimit.indices n)).kineticProfile_measurable)
    (fun n => Published.twoTimeSurvival_measurable (physicalCharacteristicFrequency_measurable
      (approximatingSolution f hfm (G.weakLimit.indices n)).kineticProfile_measurable))
    (Published.twoTimeSurvival_measurable (physicalCharacteristicFrequency_measurable
      G.weakLimit.kineticProfile_measurable)) 1
  · intro n z
    have h := Published.twoTimeSurvival_bounds (volume.restrict (Icc 0 T))
      (physicalCharacteristicFrequency (approximatingSolution f hfm (G.weakLimit.indices n)).kineticProfile) z
    exact (abs_of_pos h.1).trans_le h.2
  · intro z
    have h := Published.twoTimeSurvival_bounds (volume.restrict (Icc 0 T))
      (physicalCharacteristicFrequency G.weakLimit.kineticProfile) z
    exact (abs_of_pos h.1).trans_le h.2
  · exact G.two_time_survival_strong hf hi hT hL

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

section

/-! # Integrable positive contributions on the local phase windows -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal
namespace BoltzmannNonuniqueness.PeriodicApproximation

theorem survivingInitial_integrable {μ : Measure ℝ} {ν : Measure Phase}
    [IsFiniteMeasure μ] [SFinite ν] (T : ℝ)
    {f : Density} (hfi : Integrable f ν) {u : (ℝ × Position) × Velocity → ℝ}
    (hum : Measurable u) (hun : ∀ p, 0 ≤ u p) :
    Integrable (survivingInitial T f u) (μ.prod ν) := by
  apply (hfi.comp_snd μ).bdd_mul
    (Published.timeSurvival_measurable (physicalCharacteristicFrequency_measurable hum)).aestronglyMeasurable
  apply ae_of_all
  intro z
  have h := Published.timeSurvival_bounds (μ := volume.restrict (Icc 0 T))
    (physicalCharacteristicFrequency_nonneg hun) z
  exact (abs_of_pos h.1).trans_le h.2

theorem GlobalCollisionLimit.finitePositiveSource_integrable {f : Density} {hfm : Measurable f}
    (G : GlobalCollisionLimit f hfm) (hf : ∀ p, 0 ≤ f p) (hi : Integrable (entropyMoment f))
    {T R : ℝ} (hT : 0 ≤ T) (hR : 0 ≤ R) (K : ℝ≥0) (L : ℝ) (n : ℕ) :
    Integrable (finitePositiveSource T ((G.weakLimit.indices n:ℝ)+1) K R
      (approximatingSolution f hfm (G.weakLimit.indices n)).kineticProfile)
      ((volume.restrict (Icc 0 T)).prod ((volume : Measure Position).prod
        ((volume : Measure Velocity).restrict (Metric.closedBall 0 L)))) := by
  have hci := memLp_one_iff_integrable.mp
    ((G.characteristic_clipped_gain_limit hf hi hT hR K L).2.memLp n)
  apply Published.survivalVolterra_integrable hci
    (Published.twoTimeSurvival_measurable (physicalCharacteristicFrequency_measurable
      (approximatingSolution f hfm (G.weakLimit.indices n)).kineticProfile_measurable)) 1
  intro z
  have h := Published.twoTimeSurvival_bounds (volume.restrict (Icc 0 T))
    (physicalCharacteristicFrequency (approximatingSolution f hfm (G.weakLimit.indices n)).kineticProfile) z
  exact (abs_of_pos h.1).trans_le h.2

end BoltzmannNonuniqueness.PeriodicApproximation

end

end

end OAI
