import OAI.GroupTheory.PolycyclicRecognition.Geometry.ProfileChainHeightBounds
import OAI.GroupTheory.PolycyclicRecognition.Geometry.ConeHeightMultiplier
import OAI.GroupTheory.PolycyclicRecognition.Analysis.BasedImagePaths

namespace OAI

/-! # The anchor-frame Haar multiplier from the two actual profile offsets -/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory

/-- At the common pivot, the linear parts cancel across the two sheets.
The actual anchor-to-base height has the sign needed for quotient volume. -/
theorem anchor_height_error_of_affine_profiles
    {G W V Z : Type*} [Group G] [NormedAddCommGroup W] [NormedSpace ℝ W]
    [AddCommGroup V] [Module ℝ V]
    (π : G →* Multiplicative W) (F : G → G) (x base anchor : G)
    (r : ℝ) (φ : Z → G) (q : Z → V) (A : V →ₗ[ℝ] W)
    (b₁ b₂ : W) (z₀ : Z) {ε₁ ε₂ : ℝ}
    (hbase : ‖rescaledMapProfile (fun g => (π (F g)).toAdd) x base r φ z₀ -
      (A (q z₀) + b₁)‖ ≤ ε₁)
    (hanchor : ‖rescaledMapProfile (fun g => (π (F g)).toAdd) x anchor r φ z₀ -
      (A (q z₀) + b₂)‖ ≤ ε₂) :
    ‖(π ((F (x * anchor * φ z₀))⁻¹ * F (x * base * φ z₀))).toAdd +
      Real.exp r • (b₂ - b₁)‖ ≤ Real.exp r * (ε₁ + ε₂) := by
  have hh := relative_height_of_affine_profiles (fun g => (π (F g)).toAdd)
    x base anchor r φ q A b₁ b₂ z₀ z₀ hbase hanchor
  have he (u v : W) : -v + u + Real.exp r • (b₂ - b₁) =
      u - v - Real.exp r • (b₁ - b₂) := by
    simp only [smul_sub]
    abel
  rw [map_mul, map_inv, toAdd_mul, toAdd_inv, he]
  simpa only [sub_self, map_zero, zero_add] using hh

/-- The profile estimate supplies the Haar bound uniformly over any finite
or infinite family of anchors. The quotient set may vary with the scale. -/
theorem anchor_haar_bound_of_affine_profiles
    {G Q W V Z : Type*} [Group G] [MeasurableSpace Q]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [AddCommGroup V] [Module ℝ V]
    (π : G →* Multiplicative W) (F : G → G) (x base anchor : G)
    (r : ℝ) (φ : Z → G) (q : Z → V) (A : V →ₗ[ℝ] W)
    (b₁ b₂ : W) (z₀ : Z) {ε₁ ε₂ : ℝ}
    (hbase : ‖rescaledMapProfile (fun g => (π (F g)).toAdd) x base r φ z₀ -
      (A (q z₀) + b₁)‖ ≤ ε₁)
    (hanchor : ‖rescaledMapProfile (fun g => (π (F g)).toAdd) x anchor r φ z₀ -
      (A (q z₀) + b₂)‖ ≤ ε₂)
    (ell : W →L[ℝ] ℝ) (μ : Measure Q) (α : Q ≃ Q) (S : Set Q)
    (hvol : μ (α '' S) = ENNReal.ofReal (Real.exp (ell
      (π ((F (x * anchor * φ z₀))⁻¹ * F (x * base * φ z₀))).toAdd)) * μ S) :
    μ (α '' S) ≤ ENNReal.ofReal (Real.exp
      (-ell (b₂ - b₁) * Real.exp r + (‖ell‖ * (ε₁ + ε₂)) * Real.exp r)) * μ S := by
  have hh := haar_image_le_of_height_error ell μ α S
    (π ((F (x * anchor * φ z₀))⁻¹ * F (x * base * φ z₀))).toAdd
    (b₂ - b₁) (Real.exp r) (Real.exp r * (ε₁ + ε₂)) hvol
    (anchor_height_error_of_affine_profiles π F x base anchor r φ q A b₁ b₂ z₀ hbase hanchor)
  have he : ‖ell‖ * (Real.exp r * (ε₁ + ε₂)) = (‖ell‖ * (ε₁ + ε₂)) * Real.exp r := by ring
  simpa only [he] using hh

end PolycyclicRecognition

end

end OAI
