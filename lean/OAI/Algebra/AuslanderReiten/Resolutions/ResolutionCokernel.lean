import Mathlib.CategoryTheory.Abelian.Projective.Resolution
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Category.ModuleCat.Projective

namespace OAI

noncomputable section
namespace ArExplicit
open CategoryTheory CategoryTheory.Limits
universe u
variable {R : Type u} [Ring R] {M : ModuleCat.{u} R}
variable (P : ProjectiveResolution M)

theorem resolution_range_eq_ker :
    LinearMap.range (P.complex.d 1 0).hom = LinearMap.ker (P.π.f 0).hom := by
  have h := P.exact₀
  rw [ShortComplex.moduleCat_exact_iff_range_eq_ker] at h
  exact h

def resolutionCokernelEquiv :
    (P.complex.X 0 ⧸ LinearMap.range (P.complex.d 1 0).hom) ≃ₗ[R] M :=
  (Submodule.quotEquivOfEq _ _ (resolution_range_eq_ker P)).trans
    ((P.π.f 0).hom.quotKerEquivOfSurjective
      ((ModuleCat.epi_iff_surjective (P.π.f 0)).mp inferInstance))

theorem resolutionCokernelEquiv_mk (x : P.complex.X 0) :
    resolutionCokernelEquiv P (Submodule.Quotient.mk x) = (P.π.f 0).hom x := rfl

end ArExplicit

end

end OAI
