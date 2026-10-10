import OAI.Algebra.Finitistic.Localization.ProjectiveComplexes

namespace OAI
noncomputable section
open CategoryTheory Limits
namespace LittleFinitistic.VertexProjectives
universe u
variable {B : Type u} [Ring B]

/-- eB, represented in the opposite regular module to encode right linearity. -/
def ideal (e : B) : Submodule Bᵐᵒᵖ Bᵐᵒᵖ :=
  (LinearMap.mulRight Bᵐᵒᵖ (MulOpposite.op e)).range

theorem fixed (e : B) (he : e * e = e) (x : ideal e) :
    x.val * MulOpposite.op e = x.val := by
  obtain ⟨y,hy⟩ := x.property
  change y * MulOpposite.op e = x.val at hy
  rw [← hy, mul_assoc, ← MulOpposite.op_mul, he]

instance finite (e : B) : Module.Finite Bᵐᵒᵖ (ideal e) :=
  inferInstanceAs (Module.Finite Bᵐᵒᵖ (LinearMap.mulRight Bᵐᵒᵖ (MulOpposite.op e)).range)

theorem projective (e : B) (he : e * e = e) : Module.Projective Bᵐᵒᵖ (ideal e) := by
  apply Module.Projective.of_split (ideal e).subtype
    (LinearMap.mulRight Bᵐᵒᵖ (MulOpposite.op e)).rangeRestrict
  ext x
  exact fixed e he x

/-- The actual finitely generated projective right module eB. -/
def object (e : B) (he : e * e = e) : ProjectiveComplexes.Proj B :=
  ⟨ModuleCat.of Bᵐᵒᵖ (ideal e), finite e, projective e he⟩

/-- Left multiplication by an arrow a with target idempotent e'. -/
def arrow {e e' : B} (he : e * e = e) (he' : e' * e' = e')
    (a : B) (ha : e' * a = a) : object e he ⟶ object e' he' :=
  ObjectProperty.homMk (ModuleCat.ofHom
    (((LinearMap.mulRight Bᵐᵒᵖ (MulOpposite.op a)).comp (ideal e).subtype).codRestrict
      (ideal e') (fun x => ⟨x.val * MulOpposite.op a, by
        change (x.val * MulOpposite.op a) * MulOpposite.op e' = x.val * MulOpposite.op a
        rw [mul_assoc, ← MulOpposite.op_mul, ha]⟩)))

@[simp] theorem arrow_apply {e e' : B} (he : e * e = e) (he' : e' * e' = e')
    (a : B) (ha : e' * a = a) (x : ideal e) :
    ((arrow he he' a ha).hom.hom x).val = x.val * MulOpposite.op a := rfl

theorem arrow_comp {e₀ e₁ e₂ : B}
    (h₀ : e₀*e₀=e₀) (h₁ : e₁*e₁=e₁) (h₂ : e₂*e₂=e₂)
    (a b : B) (ha : e₁*a=a) (hb : e₂*b=b) :
    arrow h₀ h₁ a ha ≫ arrow h₁ h₂ b hb =
      arrow h₀ h₂ (b*a) (by rw [← mul_assoc, hb]) := by
  apply ObjectProperty.hom_ext
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change (x.val * MulOpposite.op a) * MulOpposite.op b = x.val * MulOpposite.op (b*a)
  simp only [MulOpposite.op_mul, mul_assoc]

end LittleFinitistic.VertexProjectives

end

end OAI
