import OAI.Analysis.Pureness.Completion.CompletedSpatialTensorMap
import OAI.Analysis.Pureness.Operators.DenseKernelClosedIdeal

namespace OAI
noncomputable section
namespace CuntzPureness
open scoped TensorProduct
variable {A B C : Type*} [CStarAlgebra A] [CStarAlgebra B] [CStarAlgebra C]
variable (q : A →⋆ₐ[ℂ] C)

def algebraicIdealTensorMap : q.toLinearMap.ker ⊗[ℂ] B →ₗ[ℂ] A ⊗[ℂ] B :=
  q.toLinearMap.ker.subtype.rTensor B

lemma algebraicIdealTensorMap_tmul (a : q.toLinearMap.ker) (b : B) :
    algebraicIdealTensorMap (B := B) q (a ⊗ₜ[ℂ] b) = (a : A) ⊗ₜ[ℂ] b := rfl

theorem algebraicStarTensorMap_ker (hq : Function.Surjective q) :
    (algebraicStarTensorMap q (StarAlgHom.id ℂ B)).toLinearMap.ker =
      (algebraicIdealTensorMap (B := B) q).range := by
  exact (rTensor_exact B q.toLinearMap.exact_subtype_ker_map hq).linearMap_ker_eq

lemma algebraicStarTensorMap_eq_zero_iff (hq : Function.Surjective q) (z : A ⊗[ℂ] B) :
    algebraicStarTensorMap q (StarAlgHom.id ℂ B) z = 0 ↔
      ∃ w : q.toLinearMap.ker ⊗[ℂ] B, algebraicIdealTensorMap q w = z := by
  change z ∈ (algebraicStarTensorMap q (StarAlgHom.id ℂ B)).toLinearMap.ker ↔ _
  rw [algebraicStarTensorMap_ker q hq]
  rfl

variable {H K : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable (α : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (β : B →⋆ₐ[ℂ] (K →L[ℂ] K))

def spatialTensorKernelIdeal : ClosedStarIdeal (representedSpatialTensor α β) :=
  denseKernelClosedIdeal (spatialCompletionMap α β)
    (algebraicStarTensorMap q (StarAlgHom.id ℂ B)) (representedSpatialTensor_dense α β)

lemma spatialTensorKernelIdeal_coe (hq : Function.Surjective q) :
    ((spatialTensorKernelIdeal q α β).ideal : Set (representedSpatialTensor α β)) =
      closure (Set.range (fun w : q.toLinearMap.ker ⊗[ℂ] B =>
        spatialCompletionMap α β (algebraicIdealTensorMap q w))) := by
  rw [spatialTensorKernelIdeal, denseKernelClosedIdeal_coe]
  congr 1
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨w, rfl⟩ := (algebraicStarTensorMap_eq_zero_iff q hq z).mp hz
    exact ⟨w, rfl⟩
  · rintro ⟨w, rfl⟩
    exact ⟨algebraicIdealTensorMap q w,
      (algebraicStarTensorMap_eq_zero_iff q hq _).mpr ⟨w, rfl⟩, rfl⟩

lemma spatialTensorKernelIdeal_tmul (a : A) (ha : q a = 0) (b : B) :
    spatialCompletionMap α β (a ⊗ₜ[ℂ] b) ∈ (spatialTensorKernelIdeal q α β).ideal := by
  apply (denseKernelClosedIdeal_mem _ _ _ _).mpr
  change spatialCompletionMap α β (a ⊗ₜ[ℂ] b) ∈
    (denseKernelImage (spatialCompletionMap α β)
      (algebraicStarTensorMap q (StarAlgHom.id ℂ B))).topologicalClosure
  apply Submodule.le_topologicalClosure
  exact ⟨a ⊗ₜ[ℂ] b, by
    change q a ⊗ₜ[ℂ] b = 0
    rw [ha, TensorProduct.zero_tmul], rfl⟩
end CuntzPureness

end

end OAI
