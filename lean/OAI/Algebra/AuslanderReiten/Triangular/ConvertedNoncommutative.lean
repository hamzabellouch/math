import OAI.Algebra.AuslanderReiten.Triangular.ConvertedStructure
import Mathlib.RingTheory.Flat.Basic

namespace OAI

noncomputable section
open scoped TensorProduct
namespace ArExplicit
namespace BaseAlgebra
variable {k : Type*} [Field k] (q : k)

theorem e_u_ne_u_e :
    basisVector q Letter.e * basisVector q Letter.u ≠
      basisVector q Letter.u * basisVector q Letter.e := by
  intro h
  have hh := congrArg (fun a : BaseAlgebra k q => a.coeff Letter.u) h
  simp [basis_mul, multiplicationTable] at hh

end BaseAlgebra
namespace ConvertedAlgebra
variable {k : Type*} [Field k] (q : k) (F : Type*) [AddCommGroup F]
variable [Module (A k q) F] [Module (A k q)ᵐᵒᵖ F]

def noncommE : ConvertedAlgebra k q F := ⟨T.lower q Letter.e ⊗ₜ[k] 1, 0, 0⟩

theorem explicit_noncommuting_pair :
    noncommE q F * radicalU q F ≠ radicalU q F * noncommE q F := by
  intro h
  have hh := congrArg (fun a : ConvertedAlgebra k q F => A.originalProjection q a.top) h
  apply BaseAlgebra.e_u_ne_u_e q
  have he : A.originalProjection q (T.lower q Letter.e ⊗ₜ[k] 1) =
      BaseAlgebra.basisVector q Letter.e := by
    simp [A.originalProjection, T.lower, TrivialExtension.inl]
  simpa only [Triangular.top_mul, noncommE, radicalU, map_mul,
    A.originalProjection_radicalU, he] using hh

theorem noncommutative : ¬ ∀ a b : ConvertedAlgebra k q F, a*b = b*a := by
  intro h
  exact explicit_noncommuting_pair q F (h _ _)

end ConvertedAlgebra

theorem noncommuting_scalarExtension {k R : Type*} [Field k] [Ring R] [Algebra k R]
    (E : Type*) [Field E] [Algebra k E] (a b : R) (h : a*b ≠ b*a) :
    ((1 : E) ⊗ₜ[k] a) * ((1 : E) ⊗ₜ[k] b) ≠
      ((1 : E) ⊗ₜ[k] b) * ((1 : E) ⊗ₜ[k] a) := by
  intro he
  apply h
  apply Module.Flat.tensorProduct_mk_injective (R := k) (S := E) (M := R)
  change (1 : E) ⊗ₜ[k] (a*b) = (1 : E) ⊗ₜ[k] (b*a)
  simpa only [Algebra.TensorProduct.tmul_mul_tmul, one_mul] using he

end ArExplicit

end

end OAI
