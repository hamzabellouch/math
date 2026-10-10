import Mathlib.LinearAlgebra.Determinant
import Mathlib.GroupTheory.Commutator.Basic

namespace OAI

/-! # Determinants of scalar commutators on an invariant subspace

Restricting an action to a genuinely invariant subspace gives an action
by linear equivalences. Its commutators have determinant one, so a scalar
commutator has scalar a root of unity of degree the subspace dimension.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped commutatorElement
variable {G K V : Type*} [Group G] [Field K] [AddCommGroup V] [Module K V]

def invariantSubspaceAction (ρ : G →* (V ≃ₗ[K] V)) (W : Submodule K V)
    (hW : ∀ g : G, ∀ v ∈ W, ρ g v ∈ W) : G →* (W ≃ₗ[K] W) where
  toFun g :=
    { (ρ g).toLinearMap.restrict (hW g) with
      invFun := fun v => ⟨ρ g⁻¹ v, hW g⁻¹ v v.property⟩
      left_inv := by
        intro v
        apply Subtype.ext
        change ρ g⁻¹ (ρ g v) = v
        rw [← LinearEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one]
        rfl
      right_inv := by
        intro v
        apply Subtype.ext
        change ρ g (ρ g⁻¹ v) = v
        rw [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one]
        rfl }
  map_one' := by
    ext v
    change ρ 1 v = v
    rw [map_one]
    rfl
  map_mul' g h := by
    ext v
    change ρ (g * h) v = ρ g (ρ h v)
    rw [map_mul]
    rfl

theorem invariantSubspaceAction_scalar (ρ : G →* (V ≃ₗ[K] V)) (W : Submodule K V)
    (hW : ∀ g : G, ∀ v ∈ W, ρ g v ∈ W) (g : G) (c : K)
    (hs : ∀ v ∈ W, ρ g v = c • v) :
    (invariantSubspaceAction ρ W hW g).toLinearMap = c • (1 : Module.End K W) := by
  ext v
  exact hs v v.property

theorem scalar_commutator_root_of_unity [Module.Finite K V]
    (ρ : G →* (V ≃ₗ[K] V)) (W : Submodule K V)
    (hW : ∀ g : G, ∀ v ∈ W, ρ g v ∈ W) (g h : G) (c : K)
    (hs : ∀ v ∈ W, ρ ⁅g, h⁆ v = c • v) : c ^ Module.finrank K W = 1 := by
  let δ := LinearEquiv.det.comp (invariantSubspaceAction ρ W hW)
  have hd : δ ⁅g, h⁆ = 1 := by
    rw [map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm _ _)
  have hh := congrArg (fun a : Kˣ => (a : K)) hd
  have hdet : LinearMap.det (invariantSubspaceAction ρ W hW ⁅g, h⁆).toLinearMap = 1 := by
    simpa only [δ, MonoidHom.comp_apply, LinearEquiv.coe_det, Units.val_one] using hh
  rw [invariantSubspaceAction_scalar ρ W hW _ c hs, LinearMap.det_smul, map_one, mul_one] at hdet
  exact hdet

end PolycyclicRecognition

end

end OAI
