import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.NormalCoordinateTests
import OAI.Analysis.RieszRectifiability.Kernel.EuclideanCoordinateMoments

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory

theorem normalizedNormalHeight_second_moment_bound {q d : ℕ}
    (μ : Measure (Ambient d)) (a : Ambient d) (N : Ambient q →ₗᵢ[ℝ] Ambient d) (δ : ℝ)
    (hw : ∀ i, MemLp (fun x => normalCoordinate a N i x / δ) 2 μ)
    (C : ℝ) (hC : ∀ i, (∫ x, (normalCoordinate a N i x / δ) ^ 2 ∂μ) ≤ C) :
    Integrable (fun x => ‖normalizedNormalHeight a N δ x‖ ^ 2) μ ∧
      (∫ x, ‖normalizedNormalHeight a N δ x‖ ^ 2 ∂μ) ≤ (q : ℝ) * C := by
  have heq : ∀ x i, normalizedNormalHeight a N δ x i = normalCoordinate a N i x / δ := by
    intro x i
    exact congrArg (fun v : Ambient q => v i) (normalCoordinate_normalized_vector a N δ x).symm
  have hi : ∀ i, Integrable (fun x => (normalizedNormalHeight a N δ x i) ^ 2) μ := by
    intro i
    simpa only [heq] using! (hw i).integrable_sq
  refine ⟨integrable_euclidean_norm_sq_of_coordinates μ (normalizedNormalHeight a N δ) hi, ?_⟩
  rw [integral_euclidean_norm_sq_eq_sum μ (normalizedNormalHeight a N δ) hi]
  calc
    _ ≤ ∑ _i : Fin q, C := by
      apply Finset.sum_le_sum
      intro i _hi
      simpa only [heq] using! hC i
    _ = _ := by simp

end

end RieszRectifiability

end OAI
