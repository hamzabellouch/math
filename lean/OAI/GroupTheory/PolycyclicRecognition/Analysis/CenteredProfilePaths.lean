import OAI.GroupTheory.PolycyclicRecognition.Analysis.CoarsePathConcatenation
import OAI.GroupTheory.PolycyclicRecognition.Geometry.GoodProfileFlow

namespace OAI

/-! # Centering profile-controlled paths at their actual initial image -/

namespace PolycyclicRecognition

open Set

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- Centering costs only the profile error at the initial point. -/
theorem norm_centered_sub_smul_le {u a c w w₀ : W} {r B B₀ : ℝ}
    (hu : ‖u - c - r • w‖ ≤ B) (ha : ‖a - c - r • w₀‖ ≤ B₀) :
    ‖u - a - r • (w - w₀)‖ ≤ B + B₀ := by
  have he : u - a - r • (w - w₀) = (u - c - r • w) - (a - c - r • w₀) := by
    rw [smul_sub]
    abel
  rw [he]
  exact (norm_sub_le _ _).trans (add_le_add hu ha)

/-- An entire path over a prescribed profile image lies over its translated
image when centered at its actual start, with the same explicit error. -/
theorem centered_path_height_bound
    {X : Type*} [TopologicalSpace X] {a b : X} (γ : Path a b) (J : X → W)
    (center w₀ : W) (E : Set W) (r B B₀ : ℝ)
    (hstart : ‖J a - center - r • w₀‖ ≤ B₀)
    (hpath : ∀ t, ∃ w ∈ E, ‖J (γ t) - center - r • w‖ ≤ B) :
    ∀ t, ∃ w ∈ (fun z => z - w₀) '' E, ‖J (γ t) - J a - r • w‖ ≤ B + B₀ := by
  intro t
  obtain ⟨w, hw, hh⟩ := hpath t
  exact ⟨w - w₀, ⟨w, hw, rfl⟩, norm_centered_sub_smul_le hh hstart⟩

/-- Two points of the same good normalized profile give an unnormalized
relative height bound at the true exponential scale. -/
theorem relative_height_of_rescaled_profile
    {G Z : Type*} [Group G] (J : G → W) (x n : G) (s : ℝ) (φ : Z → G)
    (z z₀ : Z) (w w₀ : W) {ε ε₀ : ℝ}
    (hz : ‖rescaledMapProfile J x n s φ z - w‖ ≤ ε)
    (hz₀ : ‖rescaledMapProfile J x n s φ z₀ - w₀‖ ≤ ε₀) :
    ‖J (x * n * φ z) - J (x * n * φ z₀) - Real.exp s • (w - w₀)‖ ≤
      Real.exp s * (ε + ε₀) := by
  have hh := norm_centered_sub_smul_le
    (height_bound_of_rescaled_profile J x n s φ z w hz)
    (height_bound_of_rescaled_profile J x n s φ z₀ w₀ hz₀)
  simpa only [mul_add] using hh

end PolycyclicRecognition

end OAI
