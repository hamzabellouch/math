import OAI.Analysis.LipschitzHilbert.OneInputMain
import OAI.Analysis.LipschitzHilbert.Geometry.LaceyLiProof

namespace OAI

/-! The main results of “A uniform Hilbert transform estimate for Lipschitz
directions” (25 September 2026). The estimates hold uniformly for Lipschitz
unit vector fields depending on both coordinates, at the reciprocal-Lipschitz
truncation scale. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal
namespace LipschitzHilbert

/-- Uniform hard truncations, the actual symmetric principal value,
weak-(2,2), and bounded L2 extensions at an absolute short scale. -/
theorem main :
    ∃ a : ℝ, a∈Ioo 0 (1/2) ∧ ∃ C : ℝ≥0, 0<C ∧ ShortHilbertConclusion a C :=
  main_of_laceyLi_input laceyLiInput_proved

/-- The reciprocal-Lipschitz-scale formulation, uniform over all inner
truncations and all Lipschitz unit vector fields. -/
theorem uniform_truncation :
    ∃ C : ℝ, 0<C ∧ ∀ K : ℝ≥0, 0<K → ∀ epsilon R : ℝ,
      0<epsilon → epsilon≤R → R≤1/(1000000*(K:ℝ)) →
      ∀ v : Plane → Plane, LipschitzWith K v → (∀ x, ‖v x‖=1) →
      ∀ f : SchwartzMap Plane ℂ,
        eLpNorm (shortTransform v epsilon R f) 2 volume≤ENNReal.ofReal (C*‖f.toLp 2 volume‖) :=
  uniform_truncation_of_laceyLi_input laceyLiInput_proved

end LipschitzHilbert

end

end OAI
