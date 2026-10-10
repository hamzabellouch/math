import OAI.Algebra.Finitistic.Ordinary.OrdinaryProjectiveTensor

namespace OAI
noncomputable section
namespace LittleFinitistic.BalancedTensor
universe u
variable {k A M M' M'' N N' N'' : Type u} [Field k] [Ring A] [Algebra k A]
variable [AddCommGroup M] [Module k M] [Module Aᵐᵒᵖ M] [IsScalarTower k Aᵐᵒᵖ M]
variable [AddCommGroup M'] [Module k M'] [Module Aᵐᵒᵖ M'] [IsScalarTower k Aᵐᵒᵖ M']
variable [AddCommGroup M''] [Module k M''] [Module Aᵐᵒᵖ M''] [IsScalarTower k Aᵐᵒᵖ M'']
variable [AddCommGroup N] [Module k N] [Module A N] [IsScalarTower k A N]
variable [AddCommGroup N'] [Module k N'] [Module A N'] [IsScalarTower k A N']
variable [AddCommGroup N''] [Module k N''] [Module A N''] [IsScalarTower k A N'']

/-- The actual balanced tensor map in both variables. -/
def bimap (f : M →ₗ[Aᵐᵒᵖ] M') (g : N →ₗ[A] N') : Tensor k A M N →ₗ[k] Tensor k A M' N' :=
  (mapRightTo g).comp (mapLeft N f)

@[simp] theorem bimap_mk (f : M →ₗ[Aᵐᵒᵖ] M') (g : N →ₗ[A] N') (m : M) (n : N) :
    bimap (k := k) f g (mk k A M N m n) = mk k A M' N' (f m) (g n) := rfl

@[simp] theorem bimap_comp (f : M →ₗ[Aᵐᵒᵖ] M') (f' : M' →ₗ[Aᵐᵒᵖ] M'')
    (g : N →ₗ[A] N') (g' : N' →ₗ[A] N'') :
    (bimap (k := k) f' g').comp (bimap f g) = bimap (f'.comp f) (g'.comp g) := by
  apply ext
  intro m n
  rfl

@[simp] theorem bimap_zero_left (g : N →ₗ[A] N') :
    bimap (k := k) (0 : M →ₗ[Aᵐᵒᵖ] M') g = 0 := by
  apply ext
  intro m n
  simp only [bimap_mk,LinearMap.zero_apply,map_zero,LinearMap.zero_apply]

@[simp] theorem bimap_zero_right (f : M →ₗ[Aᵐᵒᵖ] M') :
    bimap (k := k) f (0 : N →ₗ[A] N') = 0 := by
  apply ext
  intro m n
  simp only [bimap_mk,LinearMap.zero_apply,map_zero]
end LittleFinitistic.BalancedTensor

end

end OAI
