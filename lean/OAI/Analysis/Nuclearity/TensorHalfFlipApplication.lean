import OAI.Analysis.OInfinity.ConnectedHalfFlipGenerators
import OAI.Analysis.OInfinity.MixedTower

namespace OAI

/-! The two actual tensor-factor Cuntz rows and the zero-target case for the
connected half-flip. These contain no uniqueness or absorption assumption. -/
noncomputable section
open scoped TensorProduct
namespace WeakPureInfiniteness

variable {E : Type*} [CStarAlgebra E]

def tensorOInfinityLeftHom (f : OInfinity ⊗[ℂ] OInfinity →⋆ₐ[ℂ] E) :
    OInfinity →⋆ₐ[ℂ] E :=
  f.comp
    { __ := (Algebra.TensorProduct.includeLeft :
        OInfinity →ₐ[ℂ] OInfinity ⊗[ℂ] OInfinity)
      map_star' a := by simp }

def tensorOInfinityRightHom (f : OInfinity ⊗[ℂ] OInfinity →⋆ₐ[ℂ] E) :
    OInfinity →⋆ₐ[ℂ] E :=
  f.comp
    { __ := (Algebra.TensorProduct.includeRight :
        OInfinity →ₐ[ℂ] OInfinity ⊗[ℂ] OInfinity)
      map_star' a := by simp }

lemma tensorOInfinityLeftHom_apply (f : OInfinity ⊗[ℂ] OInfinity →⋆ₐ[ℂ] E)
    (a : OInfinity) : tensorOInfinityLeftHom f a = f (a ⊗ₜ[ℂ] 1) := rfl

lemma tensorOInfinityRightHom_apply (f : OInfinity ⊗[ℂ] OInfinity →⋆ₐ[ℂ] E)
    (a : OInfinity) : tensorOInfinityRightHom f a = f (1 ⊗ₜ[ℂ] a) := rfl

lemma tensorOInfinity_factors_commute (f : OInfinity ⊗[ℂ] OInfinity →⋆ₐ[ℂ] E)
    (a b : OInfinity) : Commute (tensorOInfinityLeftHom f a) (tensorOInfinityRightHom f b) := by
  change f (a ⊗ₜ[ℂ] 1) * f (1 ⊗ₜ[ℂ] b) = f (1 ⊗ₜ[ℂ] b) * f (a ⊗ₜ[ℂ] 1)
  rw [← map_mul, ← map_mul]
  simp only [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]

lemma oInfinityHom_cuntz_relations (f : OInfinity →⋆ₐ[ℂ] E) (i j : ℕ) :
    star (f (oInfinityIsometry i)) * f (oInfinityIsometry j) = if i = j then 1 else 0 := by
  have h := congrArg f (oInfinityIsometry_relations i j)
  simpa only [map_mul, map_star, apply_ite, map_one, map_zero] using h

lemma tensorOInfinity_rows_commute (f : OInfinity ⊗[ℂ] OInfinity →⋆ₐ[ℂ] E) :
    bergRowsCommute (fun i => tensorOInfinityLeftHom f (oInfinityIsometry i))
      (fun i => tensorOInfinityRightHom f (oInfinityIsometry i)) := by
  intro i j
  refine ⟨tensorOInfinity_factors_commute f _ _, ?_⟩
  simpa only [map_star] using
    tensorOInfinity_factors_commute f (oInfinityIsometry i) (star (oInfinityIsometry j))

lemma connectedHalfFlip_of_subsingleton [Subsingleton E]
    (f : OInfinity ⊗[ℂ] OInfinity →⋆ₐ[ℂ] E) :
    CStarAbsorption.ConnectedApproximateInnerHalfFlip f := by
  intro F ε hε
  refine ⟨1, Joined.refl _, ?_⟩
  intro d _
  have hz : (1 : E) * f (d ⊗ₜ[ℂ] 1) * star (1 : E) - f (1 ⊗ₜ[ℂ] d) = 0 :=
    Subsingleton.elim _ _
  change ‖(1 : E) * f (d ⊗ₜ[ℂ] 1) * star (1 : E) - f (1 ⊗ₜ[ℂ] d)‖ < ε
  rw [hz, norm_zero]
  exact hε

end WeakPureInfiniteness

end

end OAI
