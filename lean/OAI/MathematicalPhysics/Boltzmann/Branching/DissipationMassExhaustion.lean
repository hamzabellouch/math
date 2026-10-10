import OAI.MathematicalPhysics.Boltzmann.Branching.ClippedProductionLimit
import OAI.MathematicalPhysics.Boltzmann.Collision.CollisionConservation

namespace OAI

/-! # Removing the mass cap and the collision window from entropy production -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
namespace BoltzmannNonuniqueness.PeriodicApproximation
open Compactness CollisionCompactness
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

omit [MeasurableSpace X] in
theorem eventually_mem_collisionWindow (z : (X × (Velocity × Velocity)) × Sphere) :
    ∀ᶠ n : ℕ in atTop, z ∈ collisionWindow (n:ℝ) := by
  filter_upwards [tendsto_natCast_atTop_atTop.eventually
    (eventually_ge_atTop (‖z.1.2.1‖+‖z.1.2.2‖))] with n hn
  change ‖z.1.2.1‖^2+‖z.1.2.2‖^2 ≤ (n:ℝ)^2
  nlinarith [norm_nonneg z.1.2.1,norm_nonneg z.1.2.2,
    mul_nonneg (norm_nonneg z.1.2.1) (norm_nonneg z.1.2.2)]

theorem production_le_of_clipped_windows {g : X × Velocity → ℝ}
    (hgm : Measurable g) (hg : ∀ p, 0 ≤ g p) {L : ℝ≥0∞}
    (h : ∀ (K : ℝ≥0) (R : ℝ), 0 ≤ R →
      (∫⁻ z in collisionWindow R, extendedEntropyProduction
        (collisionMassClip K g z*massNormalizedPostRate g z)
        (collisionMassClip K g z*massNormalizedPreRate g z)
        ∂(μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) ≤ L) :
    (∫⁻ z, extendedEntropyProduction (postRate g z) (preRate g z)
      ∂(μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea) ≤ L := by
  let ν := (μ.prod (volume : Measure (Velocity × Velocity))).prod sphereArea
  let P := fun z : (X × (Velocity × Velocity)) × Sphere =>
    extendedEntropyProduction (postRate g z) (preRate g z)
  have hPm : Measurable P := measurable_extendedEntropyProduction
    ((preRate_measurable hgm).comp scatterTriple_measurable) (preRate_measurable hgm)
  have hw (R : ℝ) (hR : 0 ≤ R) : (∫⁻ z in collisionWindow R, P z ∂ν) ≤ L := by
    let p (k : ℕ) (z : (X × (Velocity × Velocity)) × Sphere) :=
      extendedEntropyProduction
        (collisionMassClip (k:ℝ) g z*massNormalizedPostRate g z)
        (collisionMassClip (k:ℝ) g z*massNormalizedPreRate g z)
    have hpm k : Measurable (p k) := measurable_extendedEntropyProduction
      ((collisionMassClip_measurable k hgm).mul (massNormalizedPostRate_measurable hgm))
      ((collisionMassClip_measurable k hgm).mul (massNormalizedPreRate_measurable hgm))
    have ht z : Tendsto (fun k => p k z) atTop (𝓝 (P z)) := by
      apply tendsto_const_nhds.congr'
      filter_upwards [collisionMassClip_eventually_full hg z] with k hk
      simp only [p,hk.1,hk.2,P]
    calc
      _ = ∫⁻ z in collisionWindow R, liminf (fun k => p k z) atTop ∂ν :=
        lintegral_congr (fun z => (ht z).liminf_eq.symm)
      _ ≤ liminf (fun k => ∫⁻ z in collisionWindow R, p k z ∂ν) atTop :=
        lintegral_liminf_le (fun k => hpm k)
      _ ≤ L := liminf_le_of_frequently_le
        (Eventually.of_forall (fun (k : ℕ) => h (k:ℝ≥0) R hR)).frequently
  have ht z : Tendsto (fun n : ℕ => (collisionWindow (n:ℝ)).indicator P z) atTop (𝓝 (P z)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_mem_collisionWindow z] with n hn
    exact (indicator_of_mem hn P).symm
  calc
    _ = ∫⁻ z, liminf (fun n : ℕ => (collisionWindow (n:ℝ)).indicator P z) atTop ∂ν :=
      lintegral_congr (fun z => (ht z).liminf_eq.symm)
    _ ≤ liminf (fun n : ℕ => ∫⁻ z, (collisionWindow (n:ℝ)).indicator P z ∂ν) atTop :=
      lintegral_liminf_le (fun n => hPm.indicator (collisionWindow_measurable n))
    _ ≤ L := liminf_le_of_frequently_le ((Eventually.of_forall (fun (n : ℕ) => by
      rw [lintegral_indicator (collisionWindow_measurable n)]
      exact hw n (Nat.cast_nonneg n))).frequently)

end BoltzmannNonuniqueness.PeriodicApproximation

end

end OAI
