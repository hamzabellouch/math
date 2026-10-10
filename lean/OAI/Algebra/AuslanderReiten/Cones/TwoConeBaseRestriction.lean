import OAI.Algebra.AuslanderReiten.Cones.TwoConeRestriction

namespace OAI

noncomputable section
namespace ArExplicit.TwoCone
open CategoryTheory
universe u
variable {R S : Type u} [Ring R] [Ring S] (j : S →+* R) (D : Data R)

def baseCokernelRestrictionEquiv (n : ℕ) :
    (ModuleCat.restrictScalars j).obj (ModuleCat.of R (BaseCokernel D n)) ≃ₗ[S]
      BaseCokernel (D.restrict j) n where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def baseCokernelTransport (n : ℕ) {M : ModuleCat R} {N : ModuleCat S}
    (e : BaseCokernel D n ≃ₗ[R] M)
    (f : (ModuleCat.restrictScalars j).obj M ≃ₗ[S] N) :
    BaseCokernel (D.restrict j) n ≃ₗ[S] N :=
  (baseCokernelRestrictionEquiv j D n).symm.trans
    ((Iso.toLinearEquiv ((ModuleCat.restrictScalars j).mapIso e.toModuleIso)).trans f)

end ArExplicit.TwoCone

end

end OAI
