import OAI.Analysis.Nuclearity.MinimalTensorAlgebraic
import OAI.Analysis.WeakInfiniteness.CrossUniverseTensorBound

namespace OAI

/-! The elementary norm comparison for a completed spatial tensor sum.
Separating it keeps concrete GNS/subalgebra instances out of the finite-sum
completion calculation. -/

noncomputable section
open scoped TensorProduct

namespace WeakPureInfiniteness

lemma completion_finset_sum {I V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℂ V]
    (s : Finset I) (T : I → V →L[ℂ] V) :
    (∑ i ∈ s, T i).completion = ∑ i ∈ s, (T i).completion := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, completion_zero]
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, completion_add, ih]

lemma norm_completed_tensor_sum_le_minimal {A B H K I : Type*}
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (s : Finset I) (a : I → A) (b : I → B)
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (ρ : B →⋆ₙₐ[ℂ] (K →L[ℂ] K)) :
    ‖∑ i ∈ s, (TensorProduct.mapL (π (a i)) (ρ (b i))).completion‖ ≤
      ‖(∑ i ∈ s, minimalElementary (a i) (b i) : MinimalTensor A B)‖ := by
  rw [← completion_finset_sum, norm_completion]
  have h := norm_tensorSum_le_spatial_any s a b π ρ
  change _ ≤ ‖(minimalTensorSubalgebra A B).subtype
    (∑ i ∈ s, minimalElementary (a i) (b i) : MinimalTensor A B)‖
  simp only [map_sum]
  change ‖∑ i ∈ s, TensorProduct.mapL (π (a i)) (ρ (b i))‖ ≤
    ‖∑ i ∈ s, spatialElementary (a i) (b i)‖
  exact h

end WeakPureInfiniteness

end

end OAI
