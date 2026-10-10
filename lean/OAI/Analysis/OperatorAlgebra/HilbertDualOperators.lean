import OAI.Analysis.NuclearUltrapower.HilbertSchmidt

namespace OAI

/-! The concrete opposite-algebra representation on the conjugate Hilbert
space, needed for the spatial vector functionals of finite density roots. -/

noncomputable section
open scoped InnerProductSpace

namespace WeakPureInfiniteness

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def hilbertDualOperator (T : H →L[ℂ] H) : StrongDual ℂ H →L[ℂ] StrongDual ℂ H :=
  (ContinuousLinearMap.compL ℂ H H ℂ).flip T

@[simp] lemma hilbertDualOperator_apply (T : H →L[ℂ] H) (f : StrongDual ℂ H) (x : H) :
    hilbertDualOperator T f x = f (T x) := rfl

lemma hilbertDualOperator_toDual (T : H →L[ℂ] H) (x : H) :
    hilbertDualOperator T (InnerProductSpace.toDual ℂ H x) =
      InnerProductSpace.toDual ℂ H (star T x) := by
  ext y
  exact (ContinuousLinearMap.adjoint_inner_left T y x).symm

lemma hilbertDualOperator_star (T : H →L[ℂ] H) :
    hilbertDualOperator (star T) = star (hilbertDualOperator T) := by
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro f g
  obtain ⟨x, rfl⟩ := (InnerProductSpace.toDual ℂ H).surjective f
  obtain ⟨y, rfl⟩ := (InnerProductSpace.toDual ℂ H).surjective g
  rw [hilbertDualOperator_toDual, hilbertDualOperator_toDual, star_star,
    NuclearUltrapower.dual_inner_toDual, NuclearUltrapower.dual_inner_toDual]
  exact (ContinuousLinearMap.adjoint_inner_left T x y).symm

/-- Precomposition reverses multiplication, so the conjugate Hilbert space
carries an actual star representation of the opposite operator algebra. -/
def hilbertDualRepresentation :
    (H →L[ℂ] H)ᵐᵒᵖ →⋆ₐ[ℂ] (StrongDual ℂ H →L[ℂ] StrongDual ℂ H) where
  toFun T := hilbertDualOperator (MulOpposite.unop T)
  map_zero' := by ext f x; simp
  map_one' := by ext f x; rfl
  map_add' T S := by ext f x; simp
  map_mul' T S := by ext f x; rfl
  commutes' c := by ext f x; simp [Algebra.algebraMap_eq_smul_one]
  map_star' T := hilbertDualOperator_star _

end WeakPureInfiniteness

end

end OAI
