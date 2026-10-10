import Mathlib.LinearAlgebra.Prod

namespace OAI

namespace ArExplicit
universe u
variable {k : Type u} [Field k]
variable {V₀ V₁ W₀ W₁ U₀ U₁ : Type u}
variable [AddCommGroup V₀] [AddCommGroup V₁] [AddCommGroup W₀]
  [AddCommGroup W₁] [AddCommGroup U₀] [AddCommGroup U₁]
variable [Module k V₀] [Module k V₁] [Module k W₀]
  [Module k W₁] [Module k U₀] [Module k U₁]

theorem linearEquivActionTransfer
    (e₀ : V₀ ≃ₗ[k] W₀) (e₁ : V₁ ≃ₗ[k] W₁)
    (f₀ : W₀ ≃ₗ[k] U₀) (f₁ : W₁ ≃ₗ[k] U₁)
    (g : W₀ → W₁) (h : U₀ → U₁) {x : V₀} {y : V₁}
    (he : e₁ y = g (e₀ x)) (hf : f₁ (g (e₀ x)) = h (f₀ (e₀ x))) :
    (e₁.trans f₁) y = h ((e₀.trans f₀) x) :=
  (congrArg f₁ he).trans hf

theorem linearEquivEqSmul (e : V₀ ≃ₗ[k] W₀) (c : k)
    {x y : V₀} {z : W₀} (he : e y = z) (hz : z = c • e x) : y = c • x :=
  e.injective (he.trans (hz.trans (e.map_smul c x).symm))

end ArExplicit

end OAI
