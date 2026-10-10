import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRadialCoreSpace
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralPenaltyInverse
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralPressureConvergence

namespace OAI

/-! The actual radial penalty inverse enforces the limiting closed core constraint. -/

open Set MeasureTheory Filter Topology
namespace DefocusingNLS

theorem spectralPressureOperator_nonnegative (R : ℝ) (q : ℝ → ℝ)
    (hq : AEStronglyMeasurable q (radialPressureMeasure R))
    (hqb : ∀ᵐ r ∂radialPressureMeasure R, ‖q r‖ ≤ 1)
    (hqp : ∀ᵐ r ∂radialPressureMeasure R, 0 ≤ q r) (u : SpectralRadialL2 R) :
    0 ≤ inner ℝ (spectralPressureOperator R q hq hqb u) u := by
  rw [spectralPressureOperator_quadratic]
  apply integral_nonneg_of_ae
  filter_upwards [hqp] with r hr
  exact mul_nonneg hr (sq_nonneg _)

noncomputable def spectralRadialPenaltyInverse (R : ℝ) (q : ℝ → ℝ)
    (hq : AEStronglyMeasurable q (radialPressureMeasure R))
    (hqb : ∀ᵐ r ∂radialPressureMeasure R, ‖q r‖ ≤ 1)
    (hqp : ∀ᵐ r ∂radialPressureMeasure R, 0 ≤ q r) (a : ℝ) (ha : 0 < a) :
    StrongDual ℝ (SpectralRadialPairEnergy R) →L[ℝ] SpectralRadialPairEnergy R :=
  spectralPenaltyInverse (E := SpectralRadialPairEnergy R) (H := SpectralRadialL2 R)
    (spectralRadialFirstValue R) (spectralPressureOperator R q hq hqb)
    a ha (spectralPressureOperator_nonnegative R q hq hqb hqp)

theorem spectralRadialPenalty_core_limit (R l b : ℝ) (hb : 0 < b)
    (q : ℕ → ℝ → ℝ)
    (hq : ∀ n, AEStronglyMeasurable (q n) (radialPressureMeasure R))
    (hqb : ∀ n, ∀ᵐ r ∂radialPressureMeasure R, ‖q n r‖ ≤ 1)
    (hqp : ∀ n, ∀ᵐ r ∂radialPressureMeasure R, 0 ≤ q n r)
    (a : ℕ → ℝ) (ha : ∀ n, 0 < a n) (ha0 : Tendsto a atTop (𝓝 0))
    (F : ℕ → StrongDual ℝ (SpectralRadialPairEnergy R))
    (M : ℝ) (hF : ∀ n, ‖F n‖ ≤ M)
    (hweak : ∀ φ : ℝ → ℝ, Integrable φ (radialPressureMeasure R) →
      Tendsto (fun n => ∫ r, q n r*φ r ∂radialPressureMeasure R) atTop
        (𝓝 (∫ r, (Iic l).indicator (fun _ : ℝ => b) r*φ r ∂radialPressureMeasure R)))
    (v : SpectralRadialPairEnergy R)
    (hv : Tendsto (fun n => spectralRadialFirstValue R
      (spectralRadialPenaltyInverse R (q n) (hq n) (hqb n) (hqp n) (a n) (ha n) (F n)))
      atTop (𝓝 (spectralRadialFirstValue R v))) :
    v ∈ spectralRadialCoreSubspace R l := by
  rw [spectralRadialCoreSubspace_mem]
  let u := fun n => spectralRadialFirstValue R
    (spectralRadialPenaltyInverse R (q n) (hq n) (hqb n) (hqp n) (a n) (ha n) (F n))
  apply spectral_pressure_core_constraint R l b hb q hq hqb hweak u
    (spectralRadialFirstValue R v) hv a ha0 (M^2)
  intro n
  have hnonneg := spectralPressureOperator_nonnegative R (q n) (hq n) (hqb n) (hqp n) (u n)
  rw [spectralPressureOperator_quadratic] at hnonneg
  refine ⟨hnonneg,?_⟩
  have he := spectralPenaltyInverse_energy (E := SpectralRadialPairEnergy R) (H := SpectralRadialL2 R)
    (spectralRadialFirstValue R)
    (spectralPressureOperator R (q n) (hq n) (hqb n)) (a n) (ha n)
    (spectralPressureOperator_nonnegative R (q n) (hq n) (hqb n) (hqp n)) (F n)
  change inner ℝ (spectralPressureOperator R (q n) (hq n) (hqb n) (u n)) (u n) ≤
    a n*‖F n‖^2 at he
  rw [spectralPressureOperator_quadratic] at he
  calc
    _ ≤ a n*‖F n‖^2 := he
    _ ≤ M^2*a n := by
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg (F n)) (hF n) 2) (ha n).le

end DefocusingNLS

end OAI
