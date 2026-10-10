import OAI.Analysis.Pureness.Completion.CStarAlgebraNorm
import Mathlib.Algebra.Star.TensorProduct

namespace OAI
noncomputable section
namespace CuntzPureness
open scoped TensorProduct
universe u v

def IsNuclear (A : Type u) [CStarAlgebra A] : Prop :=
  ∀ (B : Type v) [CStarAlgebra B], Subsingleton (CStarAlgebraNorm (A ⊗[ℂ] B))

variable {A : Type u} [CStarAlgebra A] {B : Type v} [CStarAlgebra B]

theorem IsNuclear.faithful_tensor_norm_eq (hA : IsNuclear.{u, v} A)
    {E F : Type*} [CStarAlgebra E] [CStarAlgebra F]
    (f : A ⊗[ℂ] B →⋆ₐ[ℂ] E) (g : A ⊗[ℂ] B →⋆ₐ[ℂ] F)
    (hf : Function.Injective f) (hg : Function.Injective g) (z : A ⊗[ℂ] B) :
    ‖f z‖ = ‖g z‖ := by
  have he := (hA B).elim (CStarAlgebraNorm.ofFaithful f hf)
    (CStarAlgebraNorm.ofFaithful g hg)
  exact congrArg (fun p : CStarAlgebraNorm (A ⊗[ℂ] B) => p.toAlgebraNorm z) he
end CuntzPureness

end

end OAI
