import OAI.Algebra.Finitistic.Localization.EvaluationModule
import OAI.Algebra.Finitistic.Tensor.IdempotentTensorMaps

namespace OAI
noncomputable section
namespace LittleFinitistic.QuadraticEncoding.Representation
open IdempotentTensor BalancedTensor
universe u v
variable {k : Type u} [Field k] {d t : ℕ} {P : Relations k d t}
variable {Y : Type v} [AddCommGroup Y] [Module k Y]
variable (X : Representation P Y)

abbrev vertexId (i : Fin 3) : B P := ThreeVertexAlgebra.vertex (composition P) i

/-- Identify the actual fixed-point vertex part of M(Y) with Y. -/
def vertexFixedEquiv (i : Fin 3) : leftSpace (k := k) (vertexId (P := P) i) X.Evaluation ≃ₗ[k] Y where
  __ := (X.projection i).comp (leftSpace (k := k) (vertexId (P := P) i) X.Evaluation).subtype
  invFun y := ⟨X.inclusion i y, by
    change vertexId (P := P) i • X.inclusion i y = X.inclusion i y
    rw [X.vertex_smul, X.projection_inclusion]⟩
  left_inv m := by
    apply Subtype.ext
    exact (X.vertex_smul i m.val).symm.trans m.property
  right_inv y := X.projection_inclusion i y

/-- The manuscript's E_i tensor_B M(Y) ≃ Y, for the actual right ideal E_i=e_iB. -/
def vertexTensorEquiv (i : Fin 3) :
    Tensor k (B P) (rightIdeal (vertexId (P := P) i)) X.Evaluation ≃ₗ[k] Y :=
  (tensorEquiv (k := k) (vertexId (P := P) i) X.Evaluation
    ((ThreeVertexAlgebra.directedSystem (composition P)).idem i)).trans (X.vertexFixedEquiv i)

@[simp] theorem vertexTensorEquiv_mk (i : Fin 3)
    (m : rightIdeal (vertexId (P := P) i)) (y : X.Evaluation) :
    X.vertexTensorEquiv i (BalancedTensor.mk k (B P) (rightIdeal (vertexId (P := P) i)) X.Evaluation m y) =
      X.projection i (m.val • y) := rfl

@[simp] theorem vertexTensorEquiv_symm (i : Fin 3) (y : Y) :
    (X.vertexTensorEquiv i).symm y =
      BalancedTensor.mk k (B P) (rightIdeal (vertexId (P := P) i)) X.Evaluation
        ⟨vertexId (P := P) i,(ThreeVertexAlgebra.directedSystem (composition P)).idem i⟩
        (X.inclusion i y) := rfl

/-- Under the natural tensor identifications, an arrow map evaluates to its module action. -/
theorem tensor_leftMultiply (i j : Fin 3) (b : B P)
    (ht : vertexId (P := P) j*b=b) (hs : b*vertexId (P := P) i=b) (y : Y) :
    X.vertexTensorEquiv j
      (mapLeft (k := k) X.Evaluation (leftMultiply (e := vertexId (P := P) i) b ht)
        ((X.vertexTensorEquiv i).symm y)) = X.projection j (b • X.inclusion i y) := by
  rw [vertexTensorEquiv_symm, mapLeft_mk, vertexTensorEquiv_mk]
  simp only [leftMultiply_apply, hs]

lemma arrow01_target (h : Fin (d+1)) : vertexId (P := P) 1 * arrow01 P h = arrow01 P h := by
  change ThreeVertexAlgebra.mul (composition P) _ _ = _
  simp [vertexId,ThreeVertexAlgebra.vertex,ThreeVertexAlgebra.mul,arrow01]
lemma arrow01_source (h : Fin (d+1)) : arrow01 P h * vertexId (P := P) 0 = arrow01 P h := by
  change ThreeVertexAlgebra.mul (composition P) _ _ = _
  simp [vertexId,ThreeVertexAlgebra.vertex,ThreeVertexAlgebra.mul,arrow01]
lemma arrow12_target (h : Fin (d+1)) : vertexId (P := P) 2 * arrow12 P h = arrow12 P h := by
  change ThreeVertexAlgebra.mul (composition P) _ _ = _
  simp [vertexId,ThreeVertexAlgebra.vertex,ThreeVertexAlgebra.mul,arrow12]
lemma arrow12_source (h : Fin (d+1)) : arrow12 P h * vertexId (P := P) 1 = arrow12 P h := by
  change ThreeVertexAlgebra.mul (composition P) _ _ = _
  simp [vertexId,ThreeVertexAlgebra.vertex,ThreeVertexAlgebra.mul,arrow12]

theorem tensor_arrow01 (h : Fin (d+1)) (y : Y) :
    X.vertexTensorEquiv 1
      (mapLeft (k := k) X.Evaluation
        (leftMultiply (e := vertexId (P := P) 0) (arrow01 P h) (arrow01_target h))
        ((X.vertexTensorEquiv 0).symm y)) =
      (Fin.cases (motive := fun _ => Module.End k Y) 1 X.generator h) y := by
  rw [tensor_leftMultiply X 0 1 _ _ (arrow01_source h)]
  erw [X.arrow01_smul]
  rfl

theorem tensor_arrow12 (h : Fin (d+1)) (y : Y) :
    X.vertexTensorEquiv 2
      (mapLeft (k := k) X.Evaluation
        (leftMultiply (e := vertexId (P := P) 1) (arrow12 P h) (arrow12_target h))
        ((X.vertexTensorEquiv 1).symm y)) =
      (Fin.cases (motive := fun _ => Module.End k Y) 1 X.generator h) y := by
  rw [tensor_leftMultiply X 1 2 _ _ (arrow12_source h)]
  erw [X.arrow12_smul]
  rfl
end LittleFinitistic.QuadraticEncoding.Representation

end

end OAI
