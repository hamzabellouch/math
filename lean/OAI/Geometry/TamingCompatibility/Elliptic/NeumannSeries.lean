import Mathlib

namespace OAI

noncomputable section
namespace TamingCompatibility.Neumann
variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G] [CompleteSpace G]

def inverseEquiv (A : G →L[ℂ] G) (hA : ‖A‖ < 1) : G ≃L[ℂ] G :=
  ContinuousLinearEquiv.ofUnit (Units.oneSub (-A) (by simpa using hA))

lemma inverseEquiv_apply (A : G →L[ℂ] G) (hA : ‖A‖ < 1) (x : G) :
    inverseEquiv A hA x = x + A x := by
  change ((1 : G →L[ℂ] G) - (-A)) x = _
  simp

theorem existsUnique (A : G →L[ℂ] G) (hA : ‖A‖ < 1) (y : G) :
    ∃! x, x + A x = y := by
  let L := inverseEquiv A hA
  refine ⟨L.symm y, ?_, ?_⟩
  · exact (inverseEquiv_apply A hA _).symm.trans (L.apply_symm_apply y)
  · intro z hz
    apply L.injective
    rw [L.apply_symm_apply, inverseEquiv_apply]
    exact hz
end TamingCompatibility.Neumann

end

end OAI
