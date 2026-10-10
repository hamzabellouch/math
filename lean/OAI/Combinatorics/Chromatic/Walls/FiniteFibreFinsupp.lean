import Mathlib

namespace OAI

section
namespace ElementaryPositivity
open Function
attribute [local instance] Classical.propDecidable
variable {A B : Type*} (p : A → B)

def fibreConstant : Submodule ℚ (A →₀ ℚ) where
  carrier := {f | ∀ a a',p a=p a' → f a=f a'}
  zero_mem' := by intro a a' h; rfl
  add_mem' := by intro f g hf hg a a' h; simp only [Finsupp.add_apply,hf a a' h,hg a a' h]
  smul_mem' := by intro r f hf a a' h; simp only [Finsupp.smul_apply,hf a a' h]

noncomputable def finiteFibrePullback (hp : ∀ b,Set.Finite {a | p a=b}) :
    (B →₀ ℚ) →ₗ[ℚ] (A →₀ ℚ) where
  toFun f := Finsupp.ofSupportFinite (fun a=>f (p a)) (by
    have H:=(f.support.finite_toSet.biUnion (fun b (_ : b∈f.support)=>hp b))
    apply H.subset
    intro a ha
    exact Set.mem_iUnion₂.mpr ⟨p a,Finsupp.mem_support_iff.mpr ha,rfl⟩)
  map_add' f g := by ext a; rfl
  map_smul' r f := by ext a; rfl

@[simp] lemma finiteFibrePullback_apply (hp : ∀ b,Set.Finite {a | p a=b})
    (f : B →₀ ℚ) (a : A) : finiteFibrePullback p hp f a=f (p a) := rfl

noncomputable def fibreConstantEquiv (hp : ∀ b,Set.Finite {a | p a=b})
    (s : B → A) (hs : Function.RightInverse s p) :
    fibreConstant p ≃ₗ[ℚ] (B →₀ ℚ) where
  toFun f := Finsupp.lcomapDomain s hs.injective f.val
  invFun f := ⟨finiteFibrePullback p hp f,by intro a a' h; simp only [finiteFibrePullback_apply,h]⟩
  left_inv f := by
    apply Subtype.ext
    ext a
    exact f.property _ _ (hs (p a))
  right_inv f := by ext b; exact congrArg f (hs b)
  map_add' f g := map_add (Finsupp.lcomapDomain s hs.injective) f.val g.val
  map_smul' r f := map_smul (Finsupp.lcomapDomain s hs.injective) r f.val

noncomputable def fibreConstantBasis (hp : ∀ b,Set.Finite {a | p a=b})
    (s : B → A) (hs : Function.RightInverse s p) :
    Module.Basis B ℚ (fibreConstant p) :=
  (Finsupp.basisSingleOne : Module.Basis B ℚ (B →₀ ℚ)).map (fibreConstantEquiv p hp s hs).symm

lemma fibreConstantBasis_apply (hp : ∀ b,Set.Finite {a | p a=b})
    (s : B → A) (hs : Function.RightInverse s p) (b : B) (a : A) :
    (fibreConstantBasis p hp s hs b).val a=if p a=b then 1 else 0 := by
  classical
  change Finsupp.single b (1:ℚ) (p a)=_
  simp [Finsupp.single_apply,eq_comm]
end ElementaryPositivity

end

end OAI
