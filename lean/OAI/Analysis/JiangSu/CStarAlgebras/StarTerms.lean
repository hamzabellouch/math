import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.CStarAlgebras.FourEdgeGroupSurgery

namespace OAI

section

noncomputable section
namespace StarTerms
inductive Term (J : Type*) where
  | scalar : ℂ → Term J
  | gen : J → Term J
  | add : Term J → Term J → Term J
  | mul : Term J → Term J → Term J
  | adjoint : Term J → Term J

variable {J : Type*} {A B : Type*} [Semiring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
  [Semiring B] [StarRing B] [Algebra ℂ B] [StarModule ℂ B]
 def Term.eval (v : J→A) : Term J→A
  | .scalar z => algebraMap ℂ A z
  | .gen j => v j
  | .add e f => e.eval v+f.eval v
  | .mul e f => e.eval v*f.eval v
  | .adjoint e => star (e.eval v)
omit [StarModule ℂ A] [StarModule ℂ B] in
lemma Term.map_eval (e : Term J) (v : J→A) (π : A →⋆ₐ[ℂ] B) :
    π (e.eval v)=e.eval (π∘v) := by
  induction e with
  | scalar z => exact π.commutes z
  | gen j => rfl
  | add e f he hf => simp only [Term.eval,map_add,he,hf]
  | mul e f he hf => simp only [Term.eval,map_mul,he,hf]
  | adjoint e he => simp only [Term.eval,map_star,he]

 def evalRange (v : J→A) : StarSubalgebra ℂ A where
  carrier := Set.range (Term.eval v)
  zero_mem' := ⟨.scalar 0,map_zero _⟩
  one_mem' := ⟨.scalar 1,map_one _⟩
  add_mem' := by rintro a b ⟨e,rfl⟩ ⟨f,rfl⟩; exact ⟨.add e f,rfl⟩
  mul_mem' := by rintro a b ⟨e,rfl⟩ ⟨f,rfl⟩; exact ⟨.mul e f,rfl⟩
  algebraMap_mem' z := ⟨.scalar z,rfl⟩
  star_mem' := by rintro a ⟨e,rfl⟩; exact ⟨.adjoint e,rfl⟩
lemma evalRange_eq_adjoin (v : J→A) : evalRange v=StarAlgebra.adjoin ℂ (Set.range v) := by
  apply le_antisymm
  · rintro a ⟨e,rfl⟩
    induction e with
    | scalar z => exact StarSubalgebra.algebraMap_mem _ z
    | gen j => exact StarAlgebra.subset_adjoin ℂ _ ⟨j,rfl⟩
    | add e f he hf => exact add_mem he hf
    | mul e f he hf => exact mul_mem he hf
    | adjoint e he => exact star_mem he
  · apply StarAlgebra.adjoin_le_iff.mpr
    rintro a ⟨j,rfl⟩
    exact ⟨.gen j,rfl⟩

end StarTerms

end
end

end OAI
