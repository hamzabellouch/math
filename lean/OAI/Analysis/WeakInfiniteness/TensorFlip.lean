import Mathlib

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal ComplexOrder
open UniformSpace
open CStarAlgebra
open scoped NNReal
open scoped TensorProduct ComplexConjugate
open scoped ENNReal InnerProductSpace
open scoped InnerProductSpace
open scoped TensorProduct InnerProductSpace

namespace WeakPureInfiniteness

section TensorFlip

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]

lemma norm_tensorSum_flip {ι : Type*} (s : Finset ι)
    (T : ι → H →L[ℂ] H) (S : ι → K →L[ℂ] K) :
    ‖∑ i ∈ s, TensorProduct.mapL (T i) (S i)‖ =
      ‖∑ i ∈ s, TensorProduct.mapL (S i) (T i)‖ := by
  let e := TensorProduct.commIsometry ℂ H K
  have he (x : H ⊗[ℂ] K) :
      e ((∑ i ∈ s, TensorProduct.mapL (T i) (S i)) x) =
        (∑ i ∈ s, TensorProduct.mapL (S i) (T i)) (e x) := by
    induction x using TensorProduct.inductionOn with
    | tmul x y => simp [e, TensorProduct.commIsometry_apply]
    | add x y hx hy => simp only [map_add,hx,hy]
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (ContinuousLinearMap.opNorm_nonneg _)
    intro x
    rw [← e.norm_map ((∑ i ∈ s, TensorProduct.mapL (T i) (S i)) x), he]
    simpa using (∑ i ∈ s, TensorProduct.mapL (S i) (T i)).le_opNorm (e x)
  · apply ContinuousLinearMap.opNorm_le_bound _ (ContinuousLinearMap.opNorm_nonneg _)
    intro y
    obtain ⟨x,rfl⟩ := e.surjective y
    rw [← he, e.norm_map, e.norm_map]
    exact (∑ i ∈ s, TensorProduct.mapL (T i) (S i)).le_opNorm x

end TensorFlip

end WeakPureInfiniteness
end

end OAI
