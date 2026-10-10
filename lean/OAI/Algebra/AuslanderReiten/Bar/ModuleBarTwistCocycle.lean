import OAI.Algebra.AuslanderReiten.Bar.ModuleBarAutomorphism
import OAI.Algebra.AuslanderReiten.Algebras.TSimpleTwist

namespace OAI

noncomputable section
open CategoryTheory
open scoped TensorProduct
namespace ArExplicit.ModuleBar
universe u
variable (k R M : Type u) [Field k] [Ring R] [Algebra k R]
  [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower k R M]
variable (h : R ≃ₐ[k] R) (e : M ≃ₗ[k] M)
variable (he : ∀ a m, e (a • m) = h a • e m)
variable (p : AbsoluteBar.Cochain3 k R) (c : k)
variable (hp : ∀ a b d m, p (h a) (h b) (h d) • e m = c • e (p a b d • m))
include hp

theorem transport_suffix3 (x : object k R M 3) :
    suffix3 k R M p (transport k R M h e 3 x) = c • e (suffix3 k R M p x) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, smul_add, hx, hy]
  | tmul a x =>
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, smul_add, hx, hy]
    | tmul b x =>
      induction x using TensorProduct.inductionOn with
      | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, smul_add, hx, hy]
      | tmul d m => exact hp a b d m

include he

theorem transport_cochain3 (x : object k R M 4) :
    cochain3Linear k R M p (transport k R M h e 4 x) =
      c • e (cochain3Linear k R M p x) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, smul_add, hx, hy]
  | tmul a x =>
    change h a • suffix3 k R M p (transport k R M h e 3 x) =
      c • e (a • suffix3 k R M p x)
    rw [transport_suffix3 k R M h e p c hp, he]
    exact (smul_comm c (h a) _).symm

end ArExplicit.ModuleBar

namespace ArExplicit.T
universe u
variable {k : Type u} [Field k] (q : k) (H : kˣ)

theorem inverseTwist_simple_compatible (a : T k q) (m : Resolution.Simple q) :
    (LinearEquiv.refl k (Resolution.Simple q)) (a • m) =
      (TrivialExtension.twist H).symm a • (LinearEquiv.refl k (Resolution.Simple q)) m := rfl

theorem inverseTwist_bar_cocycle
    (x : ModuleBar.object k (T k q) (Resolution.Simple q) 4) :
    ModuleBar.cochain3Linear k (T k q) (Resolution.Simple q) (CocycleData.p q)
      (ModuleBar.transport k (T k q) (Resolution.Simple q)
        (TrivialExtension.twist H).symm (LinearEquiv.refl k _) 4 x) =
      ((H⁻¹ : kˣ) : k) •
        ModuleBar.cochain3Linear k (T k q) (Resolution.Simple q) (CocycleData.p q) x := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, smul_add, hx, hy]
  | tmul a x =>
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, smul_add, hx, hy]
    | tmul b x =>
      induction x using TensorProduct.inductionOn with
      | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, smul_add, hx, hy]
      | tmul c x =>
        induction x using TensorProduct.inductionOn with
        | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, smul_add, hx, hy]
        | tmul d m =>
          rw [ModuleBar.transport_tmul, ModuleBar.transport_tmul,
            ModuleBar.transport_tmul, ModuleBar.transport_tmul, ModuleBar.transport_zero,
            LinearEquiv.refl_apply, ModuleBar.cochain3Linear_tmul, ModuleBar.cochain3Linear_tmul,
            mul_smul, mul_smul, p_inverse_twist_simple]
          have ha (v : Resolution.Simple q) : (TrivialExtension.twist H).symm a • v = a • v := rfl
          rw [ha]
          exact (smul_comm ((H⁻¹ : kˣ) : k) a _).symm

end ArExplicit.T

end

end OAI
