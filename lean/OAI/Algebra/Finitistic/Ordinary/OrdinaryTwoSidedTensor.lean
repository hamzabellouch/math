import OAI.Algebra.Finitistic.Ordinary.OrdinaryBalancedActions

namespace OAI
noncomputable section
open scoped TensorProduct
namespace LittleFinitistic
universe u
/-- Balanced tensor with its two outside coefficient algebras recorded in the type. -/
def TwoSidedTensor (k A _S _T M N : Type u) [Field k] [Ring A] [Algebra k A]
    [AddCommGroup M] [Module k M] [Module Aᵐᵒᵖ M]
    [AddCommGroup N] [Module k N] [Module A N] := BalancedTensor.Tensor k A M N

variable (k A S T M N : Type u) [Field k] [Ring A] [Algebra k A] [Ring S] [Algebra k S]
  [Ring T] [Algebra k T]
  [AddCommGroup M] [Module k M] [Module Aᵐᵒᵖ M] [IsScalarTower k Aᵐᵒᵖ M]
  [Module S M] [IsScalarTower k S M] [SMulCommClass S Aᵐᵒᵖ M]
  [AddCommGroup N] [Module k N] [Module A N] [IsScalarTower k A N]
  [Module T N] [IsScalarTower k T N] [SMulCommClass T A N]

namespace TwoSidedTensor
instance : AddCommGroup (TwoSidedTensor k A S T M N) := inferInstanceAs (AddCommGroup (BalancedTensor.Tensor k A M N))
instance : Module k (TwoSidedTensor k A S T M N) := inferInstanceAs (Module k (BalancedTensor.Tensor k A M N))

def action : (S ⊗[k] T) →ₐ[k] Module.End k (TwoSidedTensor k A S T M N) :=
  BalancedTensor.bimoduleAction
instance : Module (S ⊗[k] T) (TwoSidedTensor k A S T M N) := Module.compHom _ (action k A S T M N).toRingHom
instance : IsScalarTower k (S ⊗[k] T) (TwoSidedTensor k A S T M N) where
  smul_assoc r x z := by
    change action k A S T M N (r • x) z = r • action k A S T M N x z
    rw [map_smul]
    rfl

def mk : M →ₗ[k] N →ₗ[k] TwoSidedTensor k A S T M N := BalancedTensor.mk k A M N

@[simp] theorem tmul_smul_mk (s : S) (t : T) (m : M) (n : N) :
    (s ⊗ₜ[k] t) • mk k A S T M N m n = mk k A S T M N (s • m) (t • n) := rfl

variable {k A S T M N}
variable {M' : Type u} [AddCommGroup M'] [Module k M'] [Module Aᵐᵒᵖ M'] [IsScalarTower k Aᵐᵒᵖ M']
  [Module S M'] [IsScalarTower k S M'] [SMulCommClass S Aᵐᵒᵖ M']

/-- Functoriality of the actual tensor with both outside actions retained. -/
def map (f : M →ₗ[Aᵐᵒᵖ] M') (hf : ∀ (s : S) m, f (s • m) = s • f m) :
    TwoSidedTensor k A S T M N →ₗ[S ⊗[k] T] TwoSidedTensor k A S T M' N where
  __ := (BalancedTensor.mapLeft (k := k) N f).toAddHom
  map_smul' x z := by
    let F : TwoSidedTensor k A S T M N →ₗ[k] TwoSidedTensor k A S T M' N :=
      BalancedTensor.mapLeft (k := k) N f
    have h : F.comp (action k A S T M N x) = (action k A S T M' N x).comp F := by
      induction x using TensorProduct.inductionOn with
      | tmul s t =>
        apply BalancedTensor.ext
        intro m n
        change BalancedTensor.mk k A M' N (f (s • m)) (t • n) =
          BalancedTensor.mk k A M' N (s • f m) (t • n)
        rw [hf]
      | add x y hx hy =>
        simp only [map_add, LinearMap.comp_add, LinearMap.add_comp, hx, hy]
    exact congrArg (fun g => g z) h

@[simp] theorem map_mk (f : M →ₗ[Aᵐᵒᵖ] M') (hf : ∀ (s : S) m, f (s • m) = s • f m) (m : M) (n : N) :
    map (T := T) (N := N) f hf (mk k A S T M N m n) = mk k A S T M' N (f m) n := rfl

/-- Actual equivalences of the right factor on the left preserve the outside bimodule. -/
def congrLeft (e : M ≃ₗ[Aᵐᵒᵖ] M') (he : ∀ (s : S) m, e (s • m) = s • e m) :
    TwoSidedTensor k A S T M N ≃ₗ[S ⊗[k] T] TwoSidedTensor k A S T M' N where
  __ := map (T := T) (N := N) e.toLinearMap he
  invFun := map (T := T) (N := N) e.symm.toLinearMap (fun s m => by
    apply e.injective
    change e (e.symm (s • m)) = e (s • e.symm m)
    rw [LinearEquiv.apply_symm_apply,he,LinearEquiv.apply_symm_apply])
  left_inv z := by
    change BalancedTensor.mapLeft (k := k) N e.symm.toLinearMap
      (BalancedTensor.mapLeft (k := k) N e.toLinearMap z) = z
    induction z using BalancedTensor.induction_on with
    | hz => simp only [map_zero]
    | ht m n =>
      change mk k A S T M N (e.symm (e m)) n = mk k A S T M N m n
      rw [LinearEquiv.symm_apply_apply]
    | ha x y hx hy => simp only [map_add,hx,hy]
  right_inv z := by
    change BalancedTensor.mapLeft (k := k) N e.toLinearMap
      (BalancedTensor.mapLeft (k := k) N e.symm.toLinearMap z) = z
    induction z using BalancedTensor.induction_on with
    | hz => simp only [map_zero]
    | ht m n =>
      change mk k A S T M' N (e (e.symm m)) n = mk k A S T M' N m n
      rw [LinearEquiv.apply_symm_apply]
    | ha x y hx hy => simp only [map_add,hx,hy]
end TwoSidedTensor
end LittleFinitistic

end

end OAI
