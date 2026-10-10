import Mathlib
import OAI.Analysis.HardSphere.Geometry.ScalarNormSqIntegral
import OAI.Analysis.HardSphere.Cutoffs.DifferentialFormula

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal BigOperators
open scoped RealInnerProductSpace
namespace HardSphere

lemma IsGroundVector.ae_gradient_phase {N : ℕ} {L : Length} {a : ℝ} {u : Jet N L}
    (hu : IsGroundVector N L a u) (p : Direction N) :
    ∀ᵐ X ∂volume, u.2 p X = u.1 X / (‖u.1 X‖ : ℂ) * (modulusJet u).2 p X := by
  filter_upwards [hu.ae_norm_modulusPartial p, coe_modulusPartial u.1 (u.2 p)] with X h1 h2
  change u.2 p X = u.1 X / (‖u.1 X‖ : ℂ) * modulusPartial u.1 (u.2 p) X
  rw [h2]
  exact ComplexRegularization.phase_differential_of_norm_eq _ _ h1

end HardSphere

end
end
end

end OAI
