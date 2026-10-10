import OAI.Probability.SignedSweeps.MatrixTwirl
import OAI.Probability.SignedSweeps.HullLift

namespace OAI

noncomputable section
namespace SignedSweeps
open scoped Classical
open Set

lemma matrixHilbert_mem_hull {I : Type*} [Fintype I] [DecidableEq I]
    {S : Set (Matrix I I ℂ)} {A : Matrix I I ℂ}
    (hA : A ∈ closedConvexHull ℝ S) :
    matrixHilbertEquiv A ∈ closedConvexHull ℝ (matrixHilbertEquiv '' S) := by
  let L : Matrix I I ℂ →ₗ[ℝ] MatrixHilbert I := matrixHilbertEquiv.toLinearMap.restrictScalars ℝ
  apply closedConvexHull_min (t := L ⁻¹' closedConvexHull ℝ (matrixHilbertEquiv '' S)) _
    (convex_closedConvexHull.linear_preimage L)
    (isClosed_closedConvexHull.preimage L.continuous_of_finiteDimensional) hA
  intro X hX
  exact subset_closedConvexHull ⟨X,hX,rfl⟩

lemma matrix_orbitHull_lift {I J G : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] [Group G]
    (ρ : G →* Matrix.unitaryGroup I ℂ)
    (L : MatrixHilbert I →ₗ[ℝ] Matrix J J ℂ) (A : Matrix I I ℂ)
    {B : Matrix J J ℂ}
    (hB : B ∈ closedConvexHull ℝ (Set.range (fun g =>
      L (matrixConjugationAction ρ g (matrixHilbertEquiv A))))) :
    ∃ M : Matrix I I ℂ,
      matrixHilbertEquiv M ∈ closedOrbitHull (matrixConjugationAction ρ) (matrixHilbertEquiv A) ∧
      L (matrixHilbertEquiv M) = B := by
  let K := (matrixHilbertEquiv.toLinearMap.restrictScalars ℝ).comp L
  have hB' := matrixHilbert_mem_hull hB
  rw [← Set.range_comp'] at hB'
  change matrixHilbertEquiv B ∈ closedConvexHull ℝ (Set.range (fun g =>
    K (matrixConjugationAction ρ g (matrixHilbertEquiv A)))) at hB'
  obtain ⟨z,hz,he⟩ := orbitHull_lift
    (F := MatrixHilbert J) (H := MatrixHilbert I)
    (matrixConjugationAction ρ) K (matrixHilbertEquiv A) hB'
  refine ⟨matrixHilbertEquiv.symm z, ?_, ?_⟩
  · rw [LinearEquiv.apply_symm_apply]
    exact hz
  · rw [LinearEquiv.apply_symm_apply]
    exact matrixHilbertEquiv.injective he

end SignedSweeps
end

end OAI
