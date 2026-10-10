import OAI.Geometry.RCD.Coordinates.NormalizedPairing
import OAI.Geometry.RCD.Sobolev.DirichletPoincare

namespace OAI

/-! # Dimensionless Poisson value error from the actual Dirichlet energy -/

open Set MeasureTheory Filter
open scoped ENNReal Topology

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

/-- A physical energy error of order `E * r² * volume` yields a
squared mean value error at most `C * E` after division by `r²`.
This is the L2 value estimate for the genuine Poisson replacement. -/
theorem normalized_dirichlet_error (Ω : Set X) (hfin : μ Ω ≠ ∞)
    (hvol : 0 < μ.real Ω) {r C E : ℝ} (hr : 0 < r) (hC : 0 ≤ C)
    (w : SobolevSpace μ hQ) (hw : w ∈ SobolevSpace.dirichlet μ hQ Ω)
    (hpoin : ∀ v : SobolevSpace.dirichlet μ hQ Ω,
      ‖SobolevSpace.toLp μ hQ v.val‖ ^ 2 ≤ C * r ^ 2 * energyForm μ hQ v.val v.val)
    (he : ∫ x, (SobolevSpace.minimalSlope μ hQ w x) ^ 2 ∂μ ≤ E * r ^ 2 * μ.real Ω) :
    ‖normalizeLocalL2 μ Ω hfin (SobolevSpace.restrictLp μ hQ Ω ((r ^ 2)⁻¹ • w))‖ ^ 2 ≤ C * E := by
  have henergy : energyForm μ hQ w w ≤ E * r ^ 2 * μ.real Ω := by
    rw [energyForm_self, ← SobolevSpace.minimalSlope_norm_sq, ← lp_integral_square_eq_norm_square]
    exact he
  have hp := (hpoin ⟨w, hw⟩).trans
    (mul_le_mul_of_nonneg_left henergy (mul_nonneg hC (sq_nonneg r)))
  have hl : (∫ x in Ω, (SobolevSpace.toLp μ hQ w x) ^ 2 ∂μ) ≤
      C * r ^ 2 * (E * r ^ 2 * μ.real Ω) := by
    calc
      _ ≤ ∫ x, (SobolevSpace.toLp μ hQ w x) ^ 2 ∂μ :=
        setIntegral_le_integral (Lp.memLp _).integrable_sq
          (Filter.Eventually.of_forall fun _ => sq_nonneg _)
      _ = ‖SobolevSpace.toLp μ hQ w‖ ^ 2 := lp_integral_square_eq_norm_square μ _
      _ ≤ _ := hp
  rw [map_smul, normalizeLocalL2_smul, norm_smul, mul_pow,
    Real.norm_eq_abs, abs_inv, abs_of_nonneg (sq_nonneg r)]
  rw [normalized_sobolev_mean_sq]
  calc
    _ ≤ ((r ^ 2)⁻¹) ^ 2 * ((μ.real Ω)⁻¹ * (C * r ^ 2 * (E * r ^ 2 * μ.real Ω))) := by
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hl (by positivity)) (sq_nonneg _)
    _ = C * E := by field_simp [hr.ne', hvol.ne']

/-- The preceding estimate tends to zero with the normalized source mass. -/
theorem normalized_dirichlet_error_tendsto_zero
    (Ω : ℕ → Set X) (hfin : ∀ i, μ (Ω i) ≠ ∞) (hvol : ∀ i, 0 < μ.real (Ω i))
    (r E : ℕ → ℝ) {C : ℝ} (hC : 0 ≤ C) (hr : ∀ i, 0 < r i)
    (w : ℕ → SobolevSpace μ hQ) (hw : ∀ i, w i ∈ SobolevSpace.dirichlet μ hQ (Ω i))
    (hpoin : ∀ i, ∀ v : SobolevSpace.dirichlet μ hQ (Ω i),
      ‖SobolevSpace.toLp μ hQ v.val‖ ^ 2 ≤ C * r i ^ 2 * energyForm μ hQ v.val v.val)
    (he : ∀ i, ∫ x, (SobolevSpace.minimalSlope μ hQ (w i) x) ^ 2 ∂μ ≤
      E i * r i ^ 2 * μ.real (Ω i))
    (hE : Tendsto E atTop (𝓝 0)) :
    Tendsto (fun i => ‖normalizeLocalL2 μ (Ω i) (hfin i)
      (SobolevSpace.restrictLp μ hQ (Ω i) ((r i ^ 2)⁻¹ • w i))‖) atTop (𝓝 0) := by
  apply squeeze_zero (fun _ => norm_nonneg _)
    (fun i => Real.le_sqrt_of_sq_le
      (normalized_dirichlet_error μ hQ (Ω i) (hfin i) (hvol i) (hr i) hC
        (w i) (hw i) (hpoin i) (he i)))
  simpa using ((tendsto_const_nhds (x := C)).mul hE).sqrt

end RegularPointCoordinates

end

end OAI
