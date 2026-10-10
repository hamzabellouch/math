import OAI.Algebra.AuslanderReiten.Cones.TwoConeCells
import OAI.Algebra.AuslanderReiten.Cones.TwoConeProjective

namespace OAI

noncomputable section
namespace ArExplicit.TwoCone
universe u
variable {R : Type u} [Ring R] (D : Data R)

def topCokernelMap (n : ℕ) : Cokernel D n →ₗ[R] BaseCokernel D (n+4) :=
  (LinearMap.range (d D n)).liftQ
    (((LinearMap.range (D.d (n+4))).mkQ).comp (topProjection D n)) (by
      rintro x ⟨y,rfl⟩
      change (LinearMap.range (D.d (n+4))).mkQ (topProjection D n (d D n y)) = 0
      rw [show topProjection D n (d D n y) = D.d (n+4) (topProjection D (n+1) y) from
        LinearMap.congr_fun (topProjection_comm D n) y]
      exact LinearMap.congr_fun (LinearMap.range_mkQ_comp (D.d (n+4))) _)

@[simp] theorem topCokernelMap_mk (n : ℕ) (x : term D n) :
    topCokernelMap D n (Submodule.Quotient.mk x) = Submodule.Quotient.mk (topProjection D n x) := rfl

end ArExplicit.TwoCone

end

end OAI
