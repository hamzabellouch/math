import OAI.Analysis.CircleDomains.Topology.RegularJordanBoundaryFlow
import OAI.Analysis.CircleDomains.Topology.PositiveJordanOrientation

namespace OAI

/-! The exact regular-level Jordan boundary admits a positive regular
parametrization, using only the retained circle classification and Green inputs. -/
open Set
open scoped ContDiff
noncomputable section
namespace CircleDomainRigidity

lemma exists_positive_parametrization_of_regular_jordan_boundary
    (hgreen : UnorientedFiniteCircleGreenFormula)
    (H : ℂ ≃ₜ ℂ) {f : ℂ → ℝ} {t : ℝ} (hf : ContDiff ℝ ∞ f)
    (ht : IsPlanarRegularValue f t)
    (hlevel : frontier (jordanInterior H) ⊆ {z | f z = t}) :
    ∃ γ : ℝ → ℂ, PositiveJordanParametrization H γ := by
  obtain ⟨γ, hγ⟩ := regular_jordan_boundary_parametrization H hf ht hlevel
  exact exists_positive_jordan_parametrization hgreen H γ hγ

end CircleDomainRigidity

end

end OAI
