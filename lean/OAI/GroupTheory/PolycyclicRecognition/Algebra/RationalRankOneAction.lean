import OAI.GroupTheory.PolycyclicRecognition.Finiteness.RationalRankOneHomology
import Mathlib.RepresentationTheory.Rep.Basic

namespace OAI

/-! # The rational character of an action on a rank-one abelian group -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory
open scoped TensorProduct
variable {G M : Type} [Group G] [AddCommGroup M] [Module ℤ M]

def integralLinear (f : M →+ M) : M →ₗ[ℤ] M where
  toFun := f
  map_add' := f.map_add
  map_smul' r x := by
    exact (congrArg f (int_smul_eq_zsmul (inferInstance : Module ℤ M) r x)).trans
      ((map_zsmul f r x).trans (int_smul_eq_zsmul (inferInstance : Module ℤ M) r (f x)).symm)

def rationalizedAction (ρ : G →* AddMonoid.End M) :
    Representation ℚ G (ℚ ⊗[ℤ] M) where
  toFun g := (integralLinear (ρ g)).baseChange ℚ
  map_one' := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro r x
    change r ⊗ₜ[ℤ] ((ρ 1) x) = r ⊗ₜ[ℤ] x
    rw [map_one]
    rfl
  map_mul' g h := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro r x
    change r ⊗ₜ[ℤ] ((ρ (g * h)) x) = r ⊗ₜ[ℤ] ((ρ g) ((ρ h) x))
    rw [map_mul]
    rfl

def rationalActionCharacter (ρ : G →* AddMonoid.End M)
    (e : (ℚ ⊗[ℤ] M) ≃ₗ[ℚ] ℚ) : G →* ℚ where
  toFun g := e (rationalizedAction ρ g (e.symm 1))
  map_one' := by simp
  map_mul' g h := by
    let F := e.toLinearMap.comp ((rationalizedAction ρ g).comp e.symm.toLinearMap)
    have hf (r : ℚ) : F r = r * F 1 := by
      simpa only [smul_eq_mul, mul_one] using F.map_smul r 1
    change e (rationalizedAction ρ (g * h) (e.symm 1)) = _
    rw [map_mul, Module.End.mul_apply]
    have hv := hf (e (rationalizedAction ρ h (e.symm 1)))
    dsimp [F] at hv
    rw [LinearEquiv.symm_apply_apply] at hv
    exact hv.trans (mul_comm _ _)

theorem rationalActionCharacter_ne_zero (ρ : G →* AddMonoid.End M)
    (e : (ℚ ⊗[ℤ] M) ≃ₗ[ℚ] ℚ) (g : G) : rationalActionCharacter ρ e g ≠ 0 := by
  intro hz
  have h := map_mul (rationalActionCharacter ρ e) g g⁻¹
  rw [mul_inv_cancel, map_one, hz, zero_mul] at h
  exact one_ne_zero h

theorem rationalActionCharacter_of_zsmul (ρ : G →* AddMonoid.End M)
    (e : (ℚ ⊗[ℤ] M) ≃ₗ[ℚ] ℚ) (g : G) (r : ℤ)
    (hρ : ∀ x, ρ g x = r • x) : rationalActionCharacter ρ e g = (r : ℚ) := by
  have hf : integralLinear (ρ g) = r • (1 : Module.End ℤ M) := by
    apply LinearMap.ext
    intro x
    exact hρ x
  have hb : (r • (1 : Module.End ℤ M)).baseChange ℚ =
      r • (1 : Module.End ℚ (ℚ ⊗[ℤ] M)) := by
    exact ((Module.End.baseChangeHom ℤ ℚ M).map_zsmul r 1).trans
      (congrArg (fun f => r • f) (Module.End.baseChangeHom ℤ ℚ M).map_one)
  change e ((integralLinear (ρ g)).baseChange ℚ (e.symm 1)) = (r : ℚ)
  rw [hf, hb]
  change e (r • e.symm 1) = (r : ℚ)
  rw [map_zsmul, LinearEquiv.apply_symm_apply]
  simp only [zsmul_eq_mul, mul_one]

end PolycyclicRecognition

end

end OAI
