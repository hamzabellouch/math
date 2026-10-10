import OAI.Analysis.Pureness.Tensor.OriginalFreeGroupSpatialTensor
import OAI.Analysis.Pureness.Projections.UltralimitAWNormality

namespace OAI
noncomputable section
namespace CuntzPureness
open CuntzTrace OrderedSemigroup
open scoped TensorProduct
universe u
variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] [Nontrivial A]
variable (hsimple : TopologicallySimple A) (hA : IsNuclear.{u, 0} A)
variable (y : finiteCuntzSubmonoid (A := A)) (hy : y ≠ 0) (f : StateSpace y)

def originalFreeGroupSpatialQuasitrace : ComplexQuasitrace (OriginalFreeGroupSpatialCompletion A) :=
  (matrixStateAWQuasitrace hsimple y hy f freeGroupScalarUltrafilter).comap
    (originalFreeGroupSpatialAWEmbedding hsimple y hy f hA).toNonUnitalStarAlgHom

lemma originalFreeGroupSpatialQuasitrace_left (a : A) :
    originalFreeGroupSpatialQuasitrace hsimple hA y hy f
      (originalFreeGroupSpatialCompletionMap A (a ⊗ₜ[ℂ] 1)) =
        (normalizedRegularizedStateTwoQuasitrace hsimple y hy f).base a := by
  change matrixStateAWQuasitrace hsimple y hy f freeGroupScalarUltrafilter
    (originalFreeGroupSpatialAWEmbedding hsimple y hy f hA
      (originalFreeGroupSpatialCompletionMap A (a ⊗ₜ[ℂ] 1))) = _
  rw [originalFreeGroupSpatialAWEmbedding_tensor, originalFreeGroupTensorHom_left]
  exact matrixStateDiagonalAWEmbedding_value hsimple y hy f freeGroupScalarUltrafilter a

lemma originalFreeGroupSpatialQuasitrace_right (b : ReducedFreeGroup) :
    originalFreeGroupSpatialQuasitrace hsimple hA y hy f
      (originalFreeGroupSpatialCompletionMap A (1 ⊗ₜ[ℂ] b)) =
        (reducedGroupTracialState (FreeGroup ℕ)).functional b := by
  change matrixStateAWQuasitrace hsimple y hy f freeGroupScalarUltrafilter
    (originalFreeGroupSpatialAWEmbedding hsimple y hy f hA
      (originalFreeGroupSpatialCompletionMap A (1 ⊗ₜ[ℂ] b))) = _
  rw [originalFreeGroupSpatialAWEmbedding_tensor, originalFreeGroupTensorHom_right]
  exact reducedFreeGroupAWEmbedding_value hsimple y hy f b

lemma originalFreeGroupSpatialQuasitrace_faithful (x : OriginalFreeGroupSpatialCompletion A) :
    originalFreeGroupSpatialQuasitrace hsimple hA y hy f (star x*x)=0 ↔ x=0 :=
  ComplexQuasitrace.comap_faithful _ _
    (originalFreeGroupSpatialAWEmbedding_isometry hsimple y hy f hA).injective
    (ultralimitAWQuasitrace_faithful _ _ _ _ _) x

lemma originalFreeGroupSpatialQuasitrace_unit :
    originalFreeGroupSpatialQuasitrace hsimple hA y hy f 1 = 1 :=
  (congrArg (matrixStateAWQuasitrace hsimple y hy f freeGroupScalarUltrafilter)
    (originalFreeGroupSpatialAWEmbedding hsimple y hy f hA).map_one).trans
    (ultralimitAWQuasitrace_unit _ _ _ _ _)

include hsimple hA y hy f in

theorem originalFreeGroupSpatialCompletion_finite (x : OriginalFreeGroupSpatialCompletion A)
    (hx : star x*x=1) : x*star x=1 := by
  let ι := originalFreeGroupSpatialAWEmbedding hsimple y hy f hA
  have hi : Function.Injective ι := (originalFreeGroupSpatialAWEmbedding_isometry hsimple y hy f hA).injective
  apply hi
  have he : star (ι x)*ι x=1 := by
    have hm : ι (star x*x) = star (ι x)*ι x :=
      (map_mul ι (star x) x).trans (congrArg (fun t => t*ι x) (map_star ι x))
    exact hm.symm.trans ((congrArg ι hx).trans ι.map_one)
  have hf := ultralimitAWCompletion_finite
    (normalizedMatrixStatePositiveQuasitrace hsimple y hy f) freeGroupScalarUltrafilter
    (normalizedMatrixStatePositiveQuasitrace_unit hsimple y hy f)
    (normalizedMatrixStatePositiveQuasitrace_metricSize_add hsimple y hy f)
    (normalizedMatrixStatePositiveQuasitrace_sqrt_add hsimple y hy f) (ι x) he
  exact (map_mul ι x (star x)).trans
    ((congrArg (fun t => ι x*t) (map_star ι x)).trans (hf.trans ι.map_one.symm))

include hA in

theorem original_freeGroup_finite_normal_AW_embedding :
    ∃ ι : OriginalFreeGroupSpatialCompletion A →⋆ₐ[ℂ]
        NormalizedMatrixStateUltraAW hsimple y hy f freeGroupScalarUltrafilter,
      Isometry ι ∧
      (∀ x : NormalizedMatrixStateUltraAW hsimple y hy f freeGroupScalarUltrafilter,
        star x*x=1 → x*star x=1) ∧
      (∀ S : Set (NormalizedMatrixStateUltraAW hsimple y hy f freeGroupScalarUltrafilter),
        ∃ p, IsStarProjection p ∧ ∀ z, (∀ a ∈ S, a*z=0) ↔ p*z=z) ∧
      ∃ Q : ComplexQuasitrace (NormalizedMatrixStateUltraAW hsimple y hy f freeGroupScalarUltrafilter),
        Q 1=1 ∧ (∀ x, Q (star x*x)=0 ↔ x=0) ∧
        (∀ S : Set (NormalizedMatrixStateUltraAW hsimple y hy f freeGroupScalarUltrafilter), S.Nonempty →
          (∀ p ∈ S, IsStarProjection p) → DirectedOn (· ≤ ·) S →
          ∃ p, IsStarProjection p ∧ (∀ q ∈ S, q ≤ p) ∧
            (∀ q, IsStarProjection q → (∀ a ∈ S, a ≤ q) → p ≤ q) ∧
            (Q p).re = sSup ((fun q => (Q q).re) '' S)) ∧
        (∀ a : A, Q (ι (originalFreeGroupSpatialCompletionMap A (a ⊗ₜ[ℂ] 1))) =
          (normalizedRegularizedStateTwoQuasitrace hsimple y hy f).base a) ∧
        (∀ b : ReducedFreeGroup, Q (ι (originalFreeGroupSpatialCompletionMap A (1 ⊗ₜ[ℂ] b))) =
            (reducedGroupTracialState (FreeGroup ℕ)).functional b) := by
  refine ⟨originalFreeGroupSpatialAWEmbedding hsimple y hy f hA,
    originalFreeGroupSpatialAWEmbedding_isometry hsimple y hy f hA,
    ?_, ?_, matrixStateAWQuasitrace hsimple y hy f freeGroupScalarUltrafilter, ?_, ?_, ?_, ?_, ?_⟩
  · exact ultralimitAWCompletion_finite _ _ _ _ (normalizedMatrixStatePositiveQuasitrace_sqrt_add hsimple y hy f)
  · exact ultralimitAWCompletion_annihilator _ _ _ _ (normalizedMatrixStatePositiveQuasitrace_sqrt_add hsimple y hy f)
  · exact ultralimitAWQuasitrace_unit _ _ _ _ _
  · exact ultralimitAWQuasitrace_faithful _ _ _ _ _
  · exact ultralimitAWQuasitrace_normal _ _ _ _ _
  · exact originalFreeGroupSpatialQuasitrace_left hsimple hA y hy f
  · exact originalFreeGroupSpatialQuasitrace_right hsimple hA y hy f
end CuntzPureness

end

end OAI
