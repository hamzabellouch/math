import OAI.GroupTheory.PolycyclicRecognition.Algebra.RationalRankOneAction
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic

namespace OAI

/-! # Cancelling a rational character on its one-dimensional representation -/

noncomputable section
namespace PolycyclicRecognition
open CategoryTheory
open scoped TensorProduct
variable {G M : Type} [Group G] [AddCommGroup M] [Module ℤ M]

theorem rationalActionCharacter_action (ρ : G →* AddMonoid.End M)
    (e : (ℚ ⊗[ℤ] M) ≃ₗ[ℚ] ℚ) (g : G) (z : ℚ ⊗[ℤ] M) :
    rationalizedAction ρ g z = rationalActionCharacter ρ e g • z := by
  apply e.injective
  let F := e.toLinearMap.comp ((rationalizedAction ρ g).comp e.symm.toLinearMap)
  have h := F.map_smul (e z) 1
  change e (rationalizedAction ρ g (e.symm ((e z) • (1 : ℚ)))) =
    (e z) • e (rationalizedAction ρ g (e.symm 1)) at h
  simp only [smul_eq_mul, mul_one, LinearEquiv.symm_apply_apply] at h
  rw [map_smul]
  exact h.trans (mul_comm _ _)

def rationalScalarMap (r : ℚ) : ModuleCat.of ℤ ℚ ⟶ ModuleCat.of ℤ ℚ :=
  ModuleCat.ofHom (r • (LinearMap.id : ℚ →ₗ[ℤ] ℚ))

@[simp] theorem rationalScalarMap_apply (r q : ℚ) :
    (rationalScalarMap r).hom q = r * q := rfl

theorem rationalTensorAction_cancel (ρ : G →* AddMonoid.End M)
    (e : (ℚ ⊗[ℤ] M) ≃ₗ[ℚ] ℚ) (g : G) (r : ℚ)
    (hr : r * rationalActionCharacter ρ e g = 1) (z : ℚ ⊗[ℤ] M) :
    TensorProduct.map (rationalScalarMap r).hom (integralLinear (ρ g)) z = z := by
  have hm : TensorProduct.map (rationalScalarMap r).hom (integralLinear (ρ g)) z =
      r • rationalizedAction ρ g z := by
    induction z using TensorProduct.inductionOn with
    | tmul q x =>
      change (r * q) ⊗ₜ[ℤ] (ρ g x) = r • (q ⊗ₜ[ℤ] (ρ g x))
      exact TensorProduct.smul_tmul' r q (ρ g x)
    | add x y hx hy => simp only [map_add, smul_add, hx, hy]
  rw [hm, rationalActionCharacter_action, smul_smul, hr, one_smul]

end PolycyclicRecognition

end

end OAI
