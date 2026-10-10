import OAI.Algebra.Finitistic.Tensor.BalancedTensor

namespace OAI
noncomputable section
namespace LittleFinitistic.BalancedTensor
universe u v w w' w'' z
variable {k : Type u} [Field k] {A : Type v} [Ring A] [Algebra k A]
variable {M : Type w} [AddCommGroup M] [Module k M] [Module Aᵐᵒᵖ M]
variable {M' : Type w'} [AddCommGroup M'] [Module k M'] [Module Aᵐᵒᵖ M']
variable {M'' : Type w''} [AddCommGroup M''] [Module k M''] [Module Aᵐᵒᵖ M'']
variable (N : Type z) [AddCommGroup N] [Module k N] [Module A N]
variable [IsScalarTower k Aᵐᵒᵖ M] [IsScalarTower k Aᵐᵒᵖ M']
  [IsScalarTower k Aᵐᵒᵖ M'']

/-- Tensor an actual right-module homomorphism with the identity. -/
def mapLeft (f : M →ₗ[Aᵐᵒᵖ] M') : Tensor k A M N →ₗ[k] Tensor k A M' N :=
  lift ((mk k A M' N).compl₁₂ (f.restrictScalars k) LinearMap.id) (by
    intro a m n
    change mk k A M' N (f (MulOpposite.op a • m)) n = mk k A M' N (f m) (a • n)
    rw [map_smul]
    exact balance a (f m) n)

@[simp] theorem mapLeft_mk (f : M →ₗ[Aᵐᵒᵖ] M') (m : M) (n : N) :
    mapLeft (k := k) N f (mk k A M N m n) = mk k A M' N (f m) n := rfl

@[simp] theorem mapLeft_id : mapLeft (k := k) N (LinearMap.id : M →ₗ[Aᵐᵒᵖ] M) = LinearMap.id := by
  apply ext
  intro m n
  rfl

@[simp] theorem mapLeft_comp (f : M →ₗ[Aᵐᵒᵖ] M') (g : M' →ₗ[Aᵐᵒᵖ] M'') :
    mapLeft (k := k) N (g.comp f) = (mapLeft (k := k) N g).comp (mapLeft (k := k) N f) := by
  apply ext
  intro m n
  rfl

@[simp] theorem mapLeft_add (f g : M →ₗ[Aᵐᵒᵖ] M') :
    mapLeft (k := k) N (f+g) = mapLeft (k := k) N f + mapLeft (k := k) N g := by
  apply ext
  intro m n
  simp
end LittleFinitistic.BalancedTensor

end

end OAI
