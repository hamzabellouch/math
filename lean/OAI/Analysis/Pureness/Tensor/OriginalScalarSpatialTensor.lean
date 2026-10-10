import OAI.Analysis.Pureness.Operators.SimpleStateGNS
import OAI.Analysis.Pureness.States.ScalarUltraproductGNS
import OAI.Analysis.Pureness.Tensor.SpatialCommutingTensor
import OAI.Analysis.Pureness.Tensor.SpatialTensorNorm

namespace OAI
noncomputable section
namespace CuntzPureness
open CuntzComparison
open scoped TensorProduct InnerProductSpace
variable (A : Type*) [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] [Nontrivial A]
variable (U : Ultrafilter ℕ)

abbrev OriginalScalarSpatialHilbert := SpatialHilbert (SimpleStateHilbert A) (ScalarMatrixUltraHilbert U)

def originalScalarSpatialHom : A ⊗[ℂ] ScalarTracialMatrixUltraproduct U →⋆ₐ[ℂ]
    (OriginalScalarSpatialHilbert A U →L[ℂ] OriginalScalarSpatialHilbert A U) :=
  spatialStarTensorHom (simpleStateGNS A) (scalarMatrixUltraGNS U)

lemma originalScalarSpatialHom_injective (hsimple : TopologicallySimple A) :
    Function.Injective (originalScalarSpatialHom A U) :=
  spatialStarTensorHom_injective _ _ hsimple (scalarMatrixUltraGNS_injective U)

lemma originalScalarSpatialHom_tmul (a : A) (b : ScalarTracialMatrixUltraproduct U) :
    originalScalarSpatialHom A U (a ⊗ₜ[ℂ] b) =
      spatialTensorOp (simpleStateGNS A a) (scalarMatrixUltraGNS U b) :=
  spatialStarTensorHom_tmul _ _ a b

lemma originalScalarSpatialHom_tmul_norm (hsimple : TopologicallySimple A)
    (a : A) (b : ScalarTracialMatrixUltraproduct U) :
    ‖originalScalarSpatialHom A U (a ⊗ₜ[ℂ] b)‖ = ‖a‖ * ‖b‖ := by
  exact (congrArg norm (originalScalarSpatialHom_tmul A U a b)).trans
    ((spatialTensorOp_norm (simpleStateGNS A a) (scalarMatrixUltraGNS U b)).trans
      (congrArg₂ (· * ·) (simpleStateGNS_norm A hsimple a)
        (scalarMatrixUltraGNS_norm U b)))

lemma originalScalarSpatialHom_sum_norm_le (hsimple : TopologicallySimple A)
    {ι : Type*} (s : Finset ι) (a : ι → A) (b : ι → ScalarTracialMatrixUltraproduct U) :
    ‖originalScalarSpatialHom A U (∑ i ∈ s, a i ⊗ₜ[ℂ] b i)‖ ≤
      ∑ i ∈ s, ‖a i‖ * ‖b i‖ := by
  rw [map_sum]
  calc
    _ ≤ ∑ i ∈ s, ‖originalScalarSpatialHom A U (a i ⊗ₜ[ℂ] b i)‖ :=
      norm_sum_le s (fun i => originalScalarSpatialHom A U (a i ⊗ₜ[ℂ] b i))
    _ = _ := Finset.sum_congr rfl (fun i _ =>
      originalScalarSpatialHom_tmul_norm A U hsimple (a i) (b i))

abbrev OriginalScalarSpatialCompletion :=
  representedSpatialTensor (simpleStateGNS A) (scalarMatrixUltraGNS U)

def originalScalarSpatialCompletionMap : A ⊗[ℂ] ScalarTracialMatrixUltraproduct U →⋆ₐ[ℂ]
    OriginalScalarSpatialCompletion A U :=
  commutingTensorClosureMap _ _ _

lemma originalScalarSpatialCompletionMap_injective (hsimple : TopologicallySimple A) :
    Function.Injective (originalScalarSpatialCompletionMap A U) := by
  intro x y h
  exact originalScalarSpatialHom_injective A U hsimple (congrArg Subtype.val h)

lemma originalScalarSpatialCompletionMap_dense :
    DenseRange (originalScalarSpatialCompletionMap A U) :=
  commutingTensorClosureMap_denseRange _ _ _

lemma originalScalarSpatialCompletionMap_norm (z : A ⊗[ℂ] ScalarTracialMatrixUltraproduct U) :
    ‖originalScalarSpatialCompletionMap A U z‖ = ‖originalScalarSpatialHom A U z‖ := rfl
end CuntzPureness

end

end OAI
