import OAI.MathematicalPhysics.Boltzmann.Branching.ClippedProductionLimit
import OAI.MathematicalPhysics.Boltzmann.Branching.DissipationMassExhaustion

namespace OAI

/-! # The full physical dissipation survives the finite periodic approximations -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness.PeriodicApproximation
open Compactness CollisionCompactness
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]

theorem full_dissipation_le_liminf
    {f : ℕ → X × Velocity → ℝ} {g : X × Velocity → ℝ} {N : ℕ → ℝ} {C : ℝ}
    (hfm : ∀ n, Measurable (f n)) (hgm : Measurable g)
    (hf : ∀ n p, 0 ≤ f n p) (hg : ∀ p, 0 ≤ g p)
    (hi : ∀ n, Integrable (entropyGauge (f n)) (μ.prod volume))
    (hb : ∀ n, (∫ p, entropyGauge (f n) p ∂μ.prod volume) ≤ C)
    (hN : ∀ n, 0 < N n)
    (hm : Tendsto (fun n => eLpNorm (fun x => fiberMass volume (f n) x-fiberMass volume g x)
      1 μ) atTop (𝓝 0))
    (hp : Published.WeakL1Converges ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea)
      (fun n => massRegularizedPreRate (N n) (f n)) (massNormalizedPreRate g))
    (hq : Published.WeakL1Converges ((μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea)
      (fun n => massRegularizedPostRate (N n) (f n)) (massNormalizedPostRate g))
    : rateDissipation μ g ≤ liminf (fun n => extendedDissipation μ (N n) (f n)) atTop := by
  have h := production_le_of_clipped_windows hgm hg
    (fun K R hR => clipped_production_liminf hfm hgm hf hg hi hb hN hm hp hq K hR)
  have hl := ENNReal.le_liminf_mul (u := fun _ : ℕ => (4:ℝ≥0∞)⁻¹)
    (v := fun n => ∫⁻ z, extendedProduction (N n) (f n) z
      ∂(μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) (f := atTop)
  exact (mul_le_mul' (le_refl (4:ℝ≥0∞)⁻¹) h).trans (by
    simpa only [liminf_const,Pi.mul_def,extendedDissipation] using hl)

end BoltzmannNonuniqueness.PeriodicApproximation

end

end OAI
