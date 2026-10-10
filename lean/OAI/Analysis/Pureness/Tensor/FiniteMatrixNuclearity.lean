import OAI.Analysis.Pureness.Tensor.FiniteMatrixTensor
import OAI.Analysis.Pureness.Cuntz.MatrixNormCorner
import OAI.Analysis.Pureness.Stabilization.MatrixCorners

namespace OAI
noncomputable section
namespace CuntzPureness
open CuntzTrace
open scoped TensorProduct
universe u v
variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem IsNuclear.finMatrix (hA : IsNuclear.{u,v} A) (n : ℕ) (hn : 1 ≤ n) :
    IsNuclear.{u,v} (FinMatrix A n) := by
  intro B _
  constructor
  intro p q
  let e : FinMatrix A n ⊗[ℂ] B ≃⋆ₐ[ℂ] Matrix (Fin n) (Fin n) (A ⊗[ℂ] B) :=
    (matrixTensorStarEquiv n).trans CStarMatrix.ofMatrixStarAlgEquiv.symm
  let p' := p.comapNonUnital e.symm.toNonUnitalStarAlgHom e.symm.injective
  let q' := q.comapNonUnital e.symm.toNonUnitalStarAlgHom e.symm.injective
  let o : Fin n := ⟨0,hn⟩
  have hc := (hA B).elim
    (p'.comapNonUnital (algebraicMatrixCorner o) (algebraicMatrixCorner_injective o))
    (q'.comapNonUnital (algebraicMatrixCorner o) (algebraicMatrixCorner_injective o))
  have he : p'=q' := matrixNorm_eq_of_corner_eq o p' q' (fun a => by
    have h := congrArg (fun r : CStarAlgebraNorm (A ⊗[ℂ] B) => r.toAlgebraNorm a) hc
    simp only [CStarAlgebraNorm.comapNonUnital_apply] at h
    exact h)
  have heval (z : FinMatrix A n ⊗[ℂ] B) : p.toAlgebraNorm z=q.toAlgebraNorm z := by
    have h := congrArg (fun r : CStarAlgebraNorm (Matrix (Fin n) (Fin n) (A ⊗[ℂ] B)) =>
      r.toAlgebraNorm (e z)) he
    rw [p.comapNonUnital_apply e.symm.toNonUnitalStarAlgHom e.symm.injective (e z),
      q.comapNonUnital_apply e.symm.toNonUnitalStarAlgHom e.symm.injective (e z)] at h
    simpa only [StarAlgEquiv.toNonUnitalStarAlgHom_apply, StarAlgEquiv.symm_apply_apply] using h
  have hpq : p.toAlgebraNorm=q.toAlgebraNorm := AlgebraNorm.ext heval
  cases p
  cases q
  cases hpq
  rfl
end CuntzPureness

end

end OAI
