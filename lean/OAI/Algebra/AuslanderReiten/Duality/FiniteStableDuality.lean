import OAI.Algebra.AuslanderReiten.Duality.SymmetricHomology
import OAI.Algebra.AuslanderReiten.Complete.FiniteCompleteResolution
import OAI.Algebra.AuslanderReiten.Stable.StableHomEquiv

namespace OAI

namespace ArExplicit.FiniteLeftModule

universe u

variable {k R : Type u} [Field k] [Ring R] [Algebra k R] [Module.Finite k R]
variable (τ : FrobeniusTrace k R)
variable (hs : ∀ a b : R, τ.trace (a * b) = τ.trace (b * a))
variable (M : FiniteLeftModule k R)
variable (N : Type u) [AddCommGroup N] [Module R N] [Module k N]
variable [IsScalarTower k R N] [SMulCommClass R k N]

noncomputable def seamKernelEquiv : LinearMap.ker (M.seam τ) ≃ₗ[R] M.syzygy.carrier :=
  LinearEquiv.ofEq _ _ (M.seam_kernel τ)

noncomputable def stableDuality :
    Module.Dual k (StableHom R M.carrier N) ≃ₗ[k] StableHom R N M.syzygy.carrier := by
  let e := M.positiveDifferential 0
  let d := M.seam τ
  have hex : LinearMap.range e = LinearMap.ker d := by
    change LinearMap.range (M.positiveDifferential 0) = LinearMap.ker (M.seam τ)
    rw [M.positiveDifferential_range, M.seam_kernel]
    rfl
  have h : d.comp e = 0 := LinearMap.range_le_ker_iff.mp (le_of_eq hex)
  let C : StableHomology.Cokernel e ≃ₗ[R] M.carrier := M.completeCokernelEquiv τ
  exact (StableHom.sourceEquiv (k := k) (N := N) C).symm.dualMap |>.trans
    ((τ.freeStableDuality hs e d h hex).trans
      (StableHom.targetEquiv (k := k) (M.seamKernelEquiv τ)))

end ArExplicit.FiniteLeftModule

end OAI
