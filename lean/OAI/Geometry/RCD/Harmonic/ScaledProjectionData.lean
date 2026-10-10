import OAI.Geometry.RCD.Coordinates.ScaledCoordinates
import OAI.Geometry.RCD.Harmonic.AffineChange
import OAI.Geometry.RCD.Harmonic.RescaledRadialFunction

namespace OAI

/-! # Rescaling the actual affine projection and its Euler equation -/

open Set MeasureTheory
open scoped ENNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

/-- Coordinate rescaling uses the same Sobolev representatives. -/
def radiusScaledColumns {n : ℕ} (r : ℝ) (u : Fin n → SobolevSpace μ hQ) :
    Fin n → SobolevSpace μ hQ := fun j => r⁻¹ • u j

omit [BorelSpace X] [ProperSpace X] in
theorem radiusScaledColumns_column {n : ℕ} (r : ℝ)
    (u : Fin n → SobolevSpace μ hQ) (b : Euclidean n) :
    sobolevColumnMap μ hQ (radiusScaledColumns μ hQ r u) b =
      r⁻¹ • sobolevColumnMap μ hQ u b := by
  simp only [sobolevColumnMap_apply, radiusScaledColumns, Finset.smul_sum, smul_comm (r⁻¹)]

omit [BorelSpace X] [ProperSpace X] in
/-- The physical inverse radius preserves the affine subspace and the
actual orthogonal projection. -/
theorem radiusScaledColumns_affineResidual {n : ℕ} {r : ℝ} (hr : r ≠ 0)
    (u : Fin n → SobolevSpace μ hQ) (Ω : Set X) (hfin : μ Ω ≠ ∞) :
    affineResidual μ hQ (radiusScaledColumns μ hQ r u) Ω hfin =
      affineResidual μ hQ u Ω hfin := by
  let B := scaledCoordinateEquiv (ContinuousLinearEquiv.refl ℝ (Euclidean n)) r⁻¹ (inv_ne_zero hr)
  apply affineResidual_eq_of_change μ hQ u (radiusScaledColumns μ hQ r u) Ω hfin B 0
  intro v
  rw [radiusScaledColumns_column]
  change SobolevSpace.restrictLp μ hQ Ω (r⁻¹ • sobolevColumnMap μ hQ u v) =
    SobolevSpace.restrictLp μ hQ Ω (sobolevColumnMap μ hQ u (r⁻¹ • v)) + 0 • restrictedOne μ Ω hfin
  rw [map_smul, map_smul, map_smul, zero_smul, add_zero]

omit [BorelSpace X] [ProperSpace X] in
/-- The same residual, divided by the squared physical radius, is the
actual projection residual of the rescaled target and coordinates. -/
theorem radius_scaled_projection {n : ℕ} {r : ℝ} (hr : r ≠ 0)
    (u : Fin n → SobolevSpace μ hQ) (Ω : Set X) (hfin : μ Ω ≠ ∞)
    (v w : SobolevSpace μ hQ)
    (hw : SobolevSpace.restrictLp μ hQ Ω w =
      affineResidual μ hQ u Ω hfin (SobolevSpace.restrictLp μ hQ Ω v)) :
    SobolevSpace.restrictLp μ hQ Ω ((r ^ 2)⁻¹ • w) =
      affineResidual μ hQ (radiusScaledColumns μ hQ r u) Ω hfin
        (SobolevSpace.restrictLp μ hQ Ω ((r ^ 2)⁻¹ • v)) := by
  rw [radiusScaledColumns_affineResidual μ hQ hr, map_smul, map_smul, hw, map_smul]

/-- Radial rescaling and residual amplitude rescaling preserve the exact
Euler equation; the coordinate coefficient is divided by one radius. -/
theorem radius_scaled_projection_euler {n : ℕ} {r B B' : ℝ} (hr : 0 < r)
    (Ω : Set X) (u : Fin n → SobolevSpace μ hQ)
    (f w η e : SobolevSpace μ hQ) (ell : Euclidean n) (k : ℝ)
    (hf : ∀ᵐ x ∂μ.restrict Ω, localGamma μ hQ f f x ≤ B)
    (hf' : ∀ᵐ x ∂μ.restrict Ω,
      localGamma μ hQ ((r ^ 2)⁻¹ • f) ((r ^ 2)⁻¹ • f) x ≤ B')
    (hid : localRadialDerivative μ hQ Ω f hf w = SobolevSpace.restrictLp μ hQ Ω
      (w + sobolevColumnMap μ hQ u ell + k • η + e)) :
    r ^ 2 • localRadialDerivative μ hQ Ω ((r ^ 2)⁻¹ • f) hf' ((r ^ 2)⁻¹ • w) =
      SobolevSpace.restrictLp μ hQ Ω
        ((r ^ 2)⁻¹ • w + sobolevColumnMap μ hQ (radiusScaledColumns μ hQ r u) (r⁻¹ • ell) +
          ((r ^ 2)⁻¹ * k) • η + (r ^ 2)⁻¹ • e) := by
  have hcoef : sobolevColumnMap μ hQ (radiusScaledColumns μ hQ r u) (r⁻¹ • ell) =
      (r ^ 2)⁻¹ • sobolevColumnMap μ hQ u ell := by
    rw [radiusScaledColumns_column, map_smul, smul_smul]
    congr 1
    field_simp
  rw [rescaled_radial_derivative μ hQ Ω f _ hr hf hf', map_smul, hid, ← map_smul, hcoef]
  congr 1
  module

end RegularPointCoordinates

end

end OAI
