import OAI.Algebra.AuslanderReiten.Bar.ModuleBar

namespace OAI

noncomputable section
namespace ArExplicit.ModuleBar
open scoped TensorProduct
universe u
variable (k R M : Type u) [Field k] [Ring R] [Algebra k R]
variable [AddCommGroup M] [Module R M] [Module k M] [IsScalarTower k R M]
variable (e : M ≃ₗ[k] k)

def freeCoordinateScalar : (R ⊗[k] M) ≃ₗ[k] R :=
  (TensorProduct.congr (LinearEquiv.refl k R) e).trans (TensorProduct.rid k R)

omit [Module R M] [IsScalarTower k R M] in
@[simp] theorem freeCoordinateScalar_tmul (a : R) (m : M) :
    freeCoordinateScalar k R M e (a ⊗ₜ[k] m) = e m • a := by
  change (TensorProduct.rid k R) (a ⊗ₜ[k] e m) = _
  exact TensorProduct.rid_tmul _ _

def freeCoordinate : moduleObject k R M 1 ≃ₗ[R] R where
  __ := (freeCoordinateScalar k R M e).toAddEquiv
  map_smul' a x := by
    change freeCoordinateScalar k R M e (left k R M 1 a x) =
      a * freeCoordinateScalar k R M e x
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add, mul_add, hx, hy]
    | tmul b m =>
      rw [left_tmul, freeCoordinateScalar_tmul, freeCoordinateScalar_tmul]
      simpa only [Algebra.smul_def, mul_assoc] using
        congrArg (fun z : R => z * b) (Algebra.commutes (e m) a)

@[simp] theorem freeCoordinate_tmul (a : R) (m : M) :
    freeCoordinate k R M e (a ⊗ₜ[k] m) = e m • a :=
  freeCoordinateScalar_tmul k R M e a m

end ArExplicit.ModuleBar

end

end OAI
