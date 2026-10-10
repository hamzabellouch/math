import OAI.Algebra.AuslanderReiten.Bar.ModuleBarFreeCoordinate

namespace OAI

noncomputable section
namespace ArExplicit.ModuleBar
open scoped TensorProduct
universe u
variable (k R M : Type u) [Field k] [Ring R] [Algebra k R]
variable [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower k R M]
variable (e : M ≃ₗ[k] k)

def cyclicCover : R →ₗ[R] moduleObject k R M 0 where
  toFun a := a • e.symm 1
  map_add' a b := add_smul a b _
  map_smul' a b := by
    change (a * b) • e.symm 1 = a • (b • e.symm 1)
    exact mul_smul a b _

@[simp] theorem cyclicCover_apply (a : R) :
    cyclicCover k R M e a = a • e.symm 1 := rfl

theorem freeCoordinate_augmentation :
    (cyclicCover k R M e).comp (freeCoordinate k R M e).toLinearMap =
      differential k R M 0 := by
  apply LinearMap.ext
  intro x
  change cyclicCover k R M e (freeCoordinateScalar k R M e x) = boundary k R M 0 x
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]; rfl
  | tmul a m =>
    change cyclicCover k R M e (freeCoordinateScalar k R M e (a ⊗ₜ[k] m)) = a • m
    rw [freeCoordinateScalar_tmul, cyclicCover_apply]
    have hm : e m • e.symm 1 = m := by
      rw [← e.symm.map_smul]
      simp
    rw [smul_assoc, smul_comm, hm]

end ArExplicit.ModuleBar

end

end OAI
