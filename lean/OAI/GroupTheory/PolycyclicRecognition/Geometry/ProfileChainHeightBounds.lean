import OAI.GroupTheory.PolycyclicRecognition.Analysis.CenteredProfilePaths

namespace OAI

/-! # Relative image heights from a common affine profile along the chain -/

noncomputable section
namespace PolycyclicRecognition

variable {G W Z V : Type*} [Group G]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [AddCommGroup V] [Module ℝ V]

/-- Different affine offsets are retained when comparing the two sheets. -/
theorem relative_height_of_affine_profiles
    (J : G → W) (x k l : G) (r : ℝ) (φ : Z → G)
    (q : Z → V) (A : V →ₗ[ℝ] W) (b b₀ : W) (z z₀ : Z)
    {ε ε₀ : ℝ}
    (hz : ‖rescaledMapProfile J x k r φ z - (A (q z) + b)‖ ≤ ε)
    (hz₀ : ‖rescaledMapProfile J x l r φ z₀ - (A (q z₀) + b₀)‖ ≤ ε₀) :
    ‖J (x * k * φ z) - J (x * l * φ z₀) -
      Real.exp r • (A (q z - q z₀) + (b - b₀))‖ ≤ Real.exp r * (ε + ε₀) := by
  have hh := norm_centered_sub_smul_le
    (height_bound_of_rescaled_profile J x k r φ z (A (q z) + b) hz)
    (height_bound_of_rescaled_profile J x l r φ z₀ (A (q z₀) + b₀) hz₀)
  have he : (A (q z) + b) - (A (q z₀) + b₀) = A (q z - q z₀) + (b - b₀) := by
    rw [map_sub]
    abel
  simpa only [he, mul_add] using hh

/-- Two different sheets can be centered at the same original image.
Their common affine offset cancels from the relative height estimate. -/
theorem relative_height_of_common_affine_profiles
    (J : G → W) (x k l : G) (r : ℝ) (φ : Z → G)
    (q : Z → V) (A : V →ₗ[ℝ] W) (b : W) (z z₀ : Z)
    {ε ε₀ : ℝ}
    (hz : ‖rescaledMapProfile J x k r φ z - (A (q z) + b)‖ ≤ ε)
    (hz₀ : ‖rescaledMapProfile J x l r φ z₀ - (A (q z₀) + b)‖ ≤ ε₀) :
    ‖J (x * k * φ z) - J (x * l * φ z₀) -
      Real.exp r • A (q z - q z₀)‖ ≤ Real.exp r * (ε + ε₀) := by
  have hh := norm_centered_sub_smul_le
    (height_bound_of_rescaled_profile J x k r φ z (A (q z) + b) hz)
    (height_bound_of_rescaled_profile J x l r φ z₀ (A (q z₀) + b) hz₀)
  simpa only [map_sub, add_sub_add_right_eq_sub, mul_add] using hh

/-- One common affine approximation to every prefix gives a uniform
centered height bound over every permitted Cartan leg coordinate. -/
theorem chain_height_bound_of_common_affine_profile
    {I : Type*} (J : G → W) (x : G) (suffix : I → G) (i₀ : I)
    (r : ℝ) (φ : Z → G) (q : Z → V) (A : V →ₗ[ℝ] W) (b : W)
    (Q : Set Z) (z₀ : Z) (hz₀ : z₀ ∈ Q) {ε : ℝ}
    (hgood : ∀ i z, z ∈ Q →
      ‖rescaledMapProfile J x (suffix i) r φ z - (A (q z) + b)‖ ≤ ε) :
    ∀ i z, z ∈ Q →
      ‖J (x * suffix i * φ z) - J (x * suffix i₀ * φ z₀) -
        Real.exp r • A (q z - q z₀)‖ ≤ 2 * Real.exp r * ε := by
  intro i z hz
  have hh := relative_height_of_common_affine_profiles J x (suffix i) (suffix i₀)
    r φ q A b z z₀ (hgood i z hz) (hgood i₀ z₀ hz₀)
  have he : Real.exp r * (ε + ε) = 2 * Real.exp r * ε := by ring
  simpa only [he] using hh

end PolycyclicRecognition

end

end OAI
