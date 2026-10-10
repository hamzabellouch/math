import OAI.Analysis.Pureness.States.OriginalScalarNuclearTensor
import OAI.Analysis.Pureness.Quasitrace.ComplexQuasitracePullback

namespace OAI
noncomputable section
namespace CuntzPureness
open CuntzTrace OrderedSemigroup
open scoped TensorProduct
universe u
variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] [Nontrivial A]
variable (hsimple : TopologicallySimple A) (hA : IsNuclear.{u, 0} A)
variable (y : finiteCuntzSubmonoid (A := A)) (hy : y ≠ 0) (f : StateSpace y)
variable (U : Ultrafilter ℕ)

abbrev matrixStateAWQuasitrace : ComplexQuasitrace (NormalizedMatrixStateUltraAW hsimple y hy f U) :=
  ultralimitAWQuasitrace (normalizedMatrixStatePositiveQuasitrace hsimple y hy f) U
    (normalizedMatrixStatePositiveQuasitrace_unit hsimple y hy f)
    (normalizedMatrixStatePositiveQuasitrace_metricSize_add hsimple y hy f)
    (normalizedMatrixStatePositiveQuasitrace_sqrt_add hsimple y hy f)

def originalScalarSpatialQuasitrace : ComplexQuasitrace (OriginalScalarSpatialCompletion A U) :=
  (matrixStateAWQuasitrace hsimple y hy f U).comap
    (originalScalarSpatialAWEmbedding hsimple hA y hy f U).toNonUnitalStarAlgHom

lemma originalScalarSpatialQuasitrace_left (a : A) :
    originalScalarSpatialQuasitrace hsimple hA y hy f U
      (originalScalarSpatialCompletionMap A U (a ⊗ₜ[ℂ] 1)) =
        (normalizedRegularizedStateTwoQuasitrace hsimple y hy f).base a := by
  exact (congrArg (matrixStateAWQuasitrace hsimple y hy f U)
    (originalScalarSpatialAWEmbedding_left hsimple hA y hy f U a)).trans
    (matrixStateDiagonalAWEmbedding_value hsimple y hy f U a)

lemma originalScalarSpatialQuasitrace_right (b : ScalarTracialMatrixUltraproduct U) :
    originalScalarSpatialQuasitrace hsimple hA y hy f U
      (originalScalarSpatialCompletionMap A U (1 ⊗ₜ[ℂ] b)) =
        (scalarMatrixUltraTracialState U).functional b := by
  exact (congrArg (matrixStateAWQuasitrace hsimple y hy f U)
    (originalScalarSpatialAWEmbedding_right hsimple hA y hy f U b)).trans
    (scalarTracialMatrixAWEmbedding_value hsimple y hy f U b)

lemma originalScalarSpatialQuasitrace_faithful (x : OriginalScalarSpatialCompletion A U) :
    originalScalarSpatialQuasitrace hsimple hA y hy f U (star x*x)=0 ↔ x=0 :=
  ComplexQuasitrace.comap_faithful _ _
    (originalScalarSpatialAWEmbedding_isometry hsimple hA y hy f U).injective
    (ultralimitAWQuasitrace_faithful _ _ _ _ _) x

lemma originalScalarSpatialQuasitrace_unit :
    originalScalarSpatialQuasitrace hsimple hA y hy f U 1 = 1 := by
  exact (congrArg (matrixStateAWQuasitrace hsimple y hy f U)
    (originalScalarSpatialAWEmbedding hsimple hA y hy f U).map_one).trans
    (ultralimitAWQuasitrace_unit _ _ _ _ _)

include hsimple hA y hy f in

theorem originalScalarSpatialCompletion_finite (x : OriginalScalarSpatialCompletion A U)
    (hx : star x*x=1) : x*star x=1 := by
  let ι := originalScalarSpatialAWEmbedding hsimple hA y hy f U
  have hi : Function.Injective ι :=
    (originalScalarSpatialAWEmbedding_isometry hsimple hA y hy f U).injective
  apply hi
  have he : star (ι x)*ι x=1 := by
    have hm : ι (star x*x) = star (ι x)*ι x :=
      (map_mul ι (star x) x).trans (congrArg (fun t => t*ι x) (map_star ι x))
    exact hm.symm.trans ((congrArg ι hx).trans ι.map_one)
  have hf := ultralimitAWCompletion_finite
    (normalizedMatrixStatePositiveQuasitrace hsimple y hy f) U
    (normalizedMatrixStatePositiveQuasitrace_unit hsimple y hy f)
    (normalizedMatrixStatePositiveQuasitrace_metricSize_add hsimple y hy f)
    (normalizedMatrixStatePositiveQuasitrace_sqrt_add hsimple y hy f) (ι x) he
  exact (map_mul ι x (star x)).trans
    ((congrArg (fun t => ι x*t) (map_star ι x)).trans (hf.trans ι.map_one.symm))
end CuntzPureness

end

end OAI
