import OAI.Algebra.AuslanderReiten.Tensor.BalancedTensorAction

namespace OAI

namespace ArExplicit.BalancedTensor

open TensorProduct

variable {k R F M N : Type*} [CommRing k] [Ring R]
variable [AddCommGroup F] [AddCommGroup M] [Module k F] [Module k M]
variable [Module Rᵐᵒᵖ F] [Module R M]

@[elab_as_elim] theorem induction_on {motive : BalancedTensor k R F M → Prop}
    (z : BalancedTensor k R F M) (zero : motive 0)
    (tmul : ∀ f m, motive (tmul f m))
    (add : ∀ x y, motive x → motive y → motive (x + y)) : motive z := by
  classical
  by_cases hz : z = 0
  · simpa only [hz] using zero
  clear hz
  induction z using Submodule.Quotient.induction_on with
  | H z =>
    induction z using TensorProduct.inductionOn with
    | tmul f m => exact tmul f m
    | add x y hx hy => exact add _ _ hx hy

variable {F' M' : Type*} [AddCommGroup F'] [AddCommGroup M']
variable [Module k F'] [Module k M'] [Module Rᵐᵒᵖ F'] [Module R M']

def map (a : F →ₗ[k] F') (b : M →ₗ[k] M')
    (ha : ∀ (r : Rᵐᵒᵖ) f, a (r • f) = r • a f)
    (hb : ∀ (r : R) m, b (r • m) = r • b m) :
    BalancedTensor k R F M →ₗ[k] BalancedTensor k R F' M' :=
  lift
    { toFun := fun f => (mk (a f)).comp b
      map_add' := by intros; ext m; simp
      map_smul' := by intros; ext m; simp }
    (by
      intro f r m
      change tmul (a (MulOpposite.op r • f)) (b m) = tmul (a f) (b (r • m))
      rw [ha, hb, balance])

@[simp] theorem map_tmul (a : F →ₗ[k] F') (b : M →ₗ[k] M')
    (ha : ∀ (r : Rᵐᵒᵖ) f, a (r • f) = r • a f)
    (hb : ∀ (r : R) m, b (r • m) = r • b m) (f : F) (m : M) :
    map a b ha hb (tmul f m) = tmul (a f) (b m) := rfl

theorem map_surjective (a : F →ₗ[k] F') (b : M →ₗ[k] M')
    (ha : ∀ (r : Rᵐᵒᵖ) f, a (r • f) = r • a f)
    (hb : ∀ (r : R) m, b (r • m) = r • b m)
    (asurj : Function.Surjective a) (bsurj : Function.Surjective b) :
    Function.Surjective (map a b ha hb) := by
  intro z
  induction z using induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | tmul f m =>
    obtain ⟨f, rfl⟩ := asurj f
    obtain ⟨m, rfl⟩ := bsurj m
    exact ⟨tmul f m, rfl⟩
  | add x y hx hy =>
    obtain ⟨x, rfl⟩ := hx
    obtain ⟨y, rfl⟩ := hy
    exact ⟨x + y, map_add _ x y⟩

section LeftLinear

variable {S : Type*} [Ring S] [AddCommGroup N] [Module k N]
variable [Module S F] [Module S N]
variable [SMulCommClass k S F] [SMulCommClass S Rᵐᵒᵖ F]

def liftLeft (b : F →ₗ[k] M →ₗ[k] N)
    (hb : ∀ (f : F) (r : R) (m : M), b (MulOpposite.op r • f) m = b f (r • m))
    (hs : ∀ (s : S) f m, b (s • f) m = s • b f m) :
    BalancedTensor k R F M →ₗ[S] N where
  __ := (lift b hb).toAddHom
  map_smul' s z := by
    change lift b hb (s • z) = s • lift b hb z
    induction z using induction_on with
    | zero => simp
    | tmul f m => simpa only [smul_tmul, lift_tmul, RingHom.id_apply] using hs s f m
    | add x y hx hy => simp only [smul_add, map_add] at *; rw [hx, hy]

@[simp] theorem liftLeft_tmul (b : F →ₗ[k] M →ₗ[k] N)
    (hb : ∀ (f : F) (r : R) (m : M), b (MulOpposite.op r • f) m = b f (r • m))
    (hs : ∀ (s : S) f m, b (s • f) m = s • b f m) (f : F) (m : M) :
    liftLeft b hb hs (tmul f m) = b f m := rfl

end LeftLinear

end ArExplicit.BalancedTensor

end OAI
