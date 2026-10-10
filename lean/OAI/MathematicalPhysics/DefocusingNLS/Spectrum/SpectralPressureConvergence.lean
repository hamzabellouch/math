import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralPressureOperator

namespace OAI

/-! Weak-star pressure convergence may be paired with strongly varying L² states. -/

open MeasureTheory Filter Topology Set
namespace DefocusingNLS
local notation "H(" R ")" => Lp ℂ 2 (radialPressureMeasure R)

theorem spectral_pressure_energy_convergence (R : ℝ) (p : ℕ → ℝ → ℝ) (p₀ : ℝ → ℝ)
    (hp : ∀ n, AEStronglyMeasurable (p n) (radialPressureMeasure R))
    (hpb : ∀ n, ∀ᵐ r ∂radialPressureMeasure R, ‖p n r‖ ≤ 1)
    (hweak : ∀ φ : ℝ → ℝ, Integrable φ (radialPressureMeasure R) →
      Tendsto (fun n => ∫ r, p n r*φ r ∂radialPressureMeasure R) atTop
        (𝓝 (∫ r, p₀ r*φ r ∂radialPressureMeasure R)))
    (u : ℕ → H(R)) (v : H(R)) (hu : Tendsto u atTop (𝓝 v)) :
    Tendsto (fun n => ∫ r, p n r*‖u n r‖^2 ∂radialPressureMeasure R) atTop
      (𝓝 (∫ r, p₀ r*‖v r‖^2 ∂radialPressureMeasure R)) := by
  let P := fun n => spectralPressureOperator R (p n) (hp n) (hpb n)
  have hv : Integrable (fun r => ‖v r‖^2) (radialPressureMeasure R) :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable v)).mp (Lp.memLp v)
  have hfixed : Tendsto (fun n => inner ℝ (P n v) v) atTop
      (𝓝 (∫ r, p₀ r*‖v r‖^2 ∂radialPressureMeasure R)) := by
    simpa only [P,spectralPressureOperator_quadratic] using hweak (fun r => ‖v r‖^2) hv
  have h := spectral_quadratic_tendsto P 1 zero_le_one
    (fun n => spectralPressureOperator_norm R (p n) (hp n) (hpb n)) u v hu _ hfixed
  simpa only [P,spectralPressureOperator_quadratic] using h

theorem spectral_pressure_core_constraint (R l b : ℝ) (hb : 0 < b)
    (p : ℕ → ℝ → ℝ)
    (hp : ∀ n, AEStronglyMeasurable (p n) (radialPressureMeasure R))
    (hpb : ∀ n, ∀ᵐ r ∂radialPressureMeasure R, ‖p n r‖ ≤ 1)
    (hweak : ∀ φ : ℝ → ℝ, Integrable φ (radialPressureMeasure R) →
      Tendsto (fun n => ∫ r, p n r*φ r ∂radialPressureMeasure R) atTop
        (𝓝 (∫ r, (Iic l).indicator (fun _ : ℝ => b) r*φ r ∂radialPressureMeasure R)))
    (u : ℕ → H(R)) (v : H(R)) (hu : Tendsto u atTop (𝓝 v))
    (a : ℕ → ℝ) (ha : Tendsto a atTop (𝓝 0)) (K : ℝ)
    (henergy : ∀ n, 0 ≤ (∫ r, p n r*‖u n r‖^2 ∂radialPressureMeasure R) ∧
      (∫ r, p n r*‖u n r‖^2 ∂radialPressureMeasure R) ≤ K*a n) :
    (fun r => v r) =ᵐ[(radialPressureMeasure R).restrict (Iic l)] 0 := by
  have hlimit := spectral_pressure_energy_convergence R p
    ((Iic l).indicator (fun _ : ℝ => b)) hp hpb hweak u v hu
  have hz : Tendsto (fun n => ∫ r, p n r*‖u n r‖^2 ∂radialPressureMeasure R)
      atTop (𝓝 0) := by
    apply squeeze_zero (fun n => (henergy n).1) (fun n => (henergy n).2)
    simpa only [mul_zero] using tendsto_const_nhds.mul ha
  apply spectral_step_pressure_constraint R l b hb _
    ((memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable v)).mp (Lp.memLp v))
  exact tendsto_nhds_unique hlimit hz

end DefocusingNLS

end OAI
