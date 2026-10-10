import OAI.Algebra.AuslanderReiten.Tensor.BalancedTensorMap

namespace OAI

namespace ArExplicit.BalancedTensor

variable {k R S F M N L : Type*} [CommRing k] [Ring R] [Ring S] [Algebra k R]
variable [AddCommGroup F] [Module k F] [Module Rᵐᵒᵖ F]
variable [Module S F] [SMulCommClass k S F] [SMulCommClass S Rᵐᵒᵖ F]
variable [AddCommGroup M] [Module k M] [Module R M] [IsScalarTower k R M]
variable [AddCommGroup N] [Module k N] [Module R N] [IsScalarTower k R N]
variable [AddCommGroup L] [Module k L] [Module R L] [IsScalarTower k R L]

def mapRight (b : M →ₗ[R] N) : BalancedTensor k R F M →ₗ[S] BalancedTensor k R F N :=
  liftLeft
    { toFun := fun f => (mk f).comp (b.restrictScalars k)
      map_add' := by intros; ext m; simp
      map_smul' := by intros; ext m; simp }
    (by
      intro f r m
      change tmul (MulOpposite.op r • f) (b m) = tmul f (b (r • m))
      rw [b.map_smul, balance])
    (by intro s f m; exact (smul_tmul s f (b m)).symm)

@[simp] theorem mapRight_tmul (b : M →ₗ[R] N) (f : F) (m : M) :
    mapRight (k := k) (S := S) b (tmul f m) = tmul f (b m) := rfl

omit [Algebra k R] [IsScalarTower k R M] in
@[ext] theorem leftHom_ext {Q : Type*} [AddCommGroup Q] [Module S Q]
    (f g : BalancedTensor k R F M →ₗ[S] Q)
    (h : ∀ x y, f (tmul x y) = g (tmul x y)) : f = g := by
  apply LinearMap.ext
  intro z
  induction z using induction_on with
  | zero => simp
  | tmul x y => exact h x y
  | add x y hx hy => simp only [map_add, hx, hy]

@[simp] theorem mapRight_id : mapRight (k := k) (S := S) (LinearMap.id : M →ₗ[R] M) =
    (LinearMap.id : BalancedTensor k R F M →ₗ[S] BalancedTensor k R F M) := by
  apply leftHom_ext
  intro f m
  rfl

@[simp] theorem mapRight_comp (b : M →ₗ[R] N) (c : N →ₗ[R] L) :
    mapRight (k := k) (F := F) (S := S) (c.comp b) = (mapRight c).comp (mapRight b) := by
  apply leftHom_ext
  intro f m
  rfl

@[simp] theorem mapRight_zero : mapRight (k := k) (S := S) (0 : M →ₗ[R] N) =
    (0 : BalancedTensor k R F M →ₗ[S] BalancedTensor k R F N) := by
  apply leftHom_ext
  intro f m
  exact tmul_zero f

theorem mapRight_add (b c : M →ₗ[R] N) :
    mapRight (k := k) (F := F) (S := S) (b + c) = mapRight b + mapRight c := by
  apply leftHom_ext
  intro f m
  exact tmul_add f (b m) (c m)

theorem mapRight_surjective (b : M →ₗ[R] N) (hb : Function.Surjective b) :
    Function.Surjective (mapRight (k := k) (F := F) (S := S) b) := by
  intro z
  induction z using induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | tmul f n =>
    obtain ⟨m, rfl⟩ := hb n
    exact ⟨tmul f m, rfl⟩
  | add x y hx hy =>
    obtain ⟨x, rfl⟩ := hx
    obtain ⟨y, rfl⟩ := hy
    exact ⟨x + y, map_add _ x y⟩

end ArExplicit.BalancedTensor

end OAI
