import OAI.Algebra.AuslanderReiten.Modules.CoinducedEmbedding
import OAI.Algebra.AuslanderReiten.Modules.SplitModules

namespace OAI

noncomputable section

namespace ArExplicit

@[ext] structure CoinducedModule (k R M : Type*) [Field k] [Ring R] [Algebra k R]
    [AddCommGroup M] [Module k M] where
  functional : R →ₗ[k] M

namespace CoinducedModule

variable {k R M : Type*} [Field k] [Ring R] [Algebra k R]
variable [AddCommGroup M] [Module k M]

def coordinates : CoinducedModule k R M ≃ (R →ₗ[k] M) where
  toFun := functional
  invFun := CoinducedModule.mk
  left_inv _ := rfl
  right_inv _ := rfl

instance : AddCommGroup (CoinducedModule k R M) := coordinates.addCommGroup
instance : Module k (CoinducedModule k R M) := coordinates.addEquiv.module k

@[simp] theorem functional_zero (r : R) : (0 : CoinducedModule k R M).functional r = 0 := rfl
@[simp] theorem functional_add (f g : CoinducedModule k R M) (r : R) :
    (f + g).functional r = f.functional r + g.functional r := rfl
@[simp] theorem functional_smul (a : k) (f : CoinducedModule k R M) (r : R) :
    (a • f).functional r = a • f.functional r := rfl

instance : SMul R (CoinducedModule k R M) :=
  ⟨fun r f => ⟨{ toFun := fun t => f.functional (t * r)
                 map_add' := fun s t => by simp [add_mul]
                 map_smul' := fun a t => by simp }⟩⟩

@[simp] theorem functional_action (r t : R) (f : CoinducedModule k R M) :
    (r • f).functional t = f.functional (t * r) := rfl

instance : Module R (CoinducedModule k R M) where
  one_smul f := by ext t; simp
  mul_smul r s f := by ext t; simp [mul_assoc]
  smul_zero r := by ext t; simp
  smul_add r f g := by ext t; simp
  zero_smul f := by ext t; simp
  add_smul r s f := by ext t; simp [mul_add]

instance : IsScalarTower k R (CoinducedModule k R M) where
  smul_assoc a r f := by ext t; simp

instance : SMulCommClass k R (CoinducedModule k R M) where
  smul_comm a r f := by ext t; rfl

def scalarEquiv : CoinducedModule k R M ≃ₗ[k] (R →ₗ[k] M) :=
  coordinates.addEquiv.linearEquiv k

instance [Module.Finite k R] [Module.Finite k M] : Module.Finite k (CoinducedModule k R M) :=
  Module.Finite.equiv scalarEquiv.symm

section Embedding

variable [Module R M] [IsScalarTower k R M]

def embedding : M →ₗ[R] CoinducedModule k R M where
  toFun m := ⟨{ toFun := fun t => t • m
                map_add' := fun r s => add_smul r s m
                map_smul' := fun a r => smul_assoc a r m }⟩
  map_add' m n := by ext t; exact smul_add t m n
  map_smul' r m := by ext t; exact (mul_smul t r m).symm

@[simp] theorem embedding_apply (m : M) (t : R) :
    (embedding (k := k) m).functional t = t • m := rfl

theorem embedding_injective : Function.Injective (embedding (k := k) (R := R) (M := M)) := by
  intro m n h
  have h' := congrArg (fun f : CoinducedModule k R M => f.functional 1) h
  simpa using h'

end Embedding

variable [Module.Finite k M]

private def coefficients : M ≃ₗ[k] (Fin (Module.finrank k M) → k) :=
  (Module.finBasis k M).equivFun

def coordinateEquiv : CoinducedModule k R M ≃ₗ[R]
    (Fin (Module.finrank k M) → Coinduced k R) where
  toFun f i := ⟨(LinearMap.proj i).comp (coefficients.toLinearMap.comp f.functional)⟩
  invFun g := ⟨coefficients.symm.toLinearMap.comp
    (LinearMap.pi fun i => (g i).functional)⟩
  left_inv f := by
    ext t
    exact coefficients.symm_apply_apply (f.functional t)
  right_inv g := by
    funext i
    apply Coinduced.ext
    apply LinearMap.ext
    intro t
    exact congrFun (coefficients.apply_symm_apply (fun j => (g j).functional t)) i
  map_add' f g := by funext i; apply Coinduced.ext; ext t; simp
  map_smul' r f := by funext i; apply Coinduced.ext; ext t; rfl

def freeEquiv [Module.Finite k R] (τ : FrobeniusTrace k R) :
    CoinducedModule k R M ≃ₗ[R] (Fin (Module.finrank k M) → R) :=
  coordinateEquiv.trans (LinearEquiv.piCongrRight fun _ => τ.leftEquiv.symm)

theorem finite [Module.Finite k R] (τ : FrobeniusTrace k R) :
    Module.Finite R (CoinducedModule k R M) := Module.Finite.equiv (freeEquiv τ).symm

theorem free [Module.Finite k R] (τ : FrobeniusTrace k R) :
    Module.Free R (CoinducedModule k R M) := Module.Free.of_equiv (freeEquiv τ).symm

theorem projective [Module.Finite k R] (τ : FrobeniusTrace k R) :
    Module.Projective R (CoinducedModule k R M) := by
  let := free (M := M) τ
  exact Module.Projective.of_free

end CoinducedModule
end ArExplicit

end

end OAI
