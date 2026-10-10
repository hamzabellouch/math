import Mathlib

namespace OAI

namespace EuclideanFiveColor

def ProperColoring (k : ℕ) (c : ℂ → Fin k) : Prop :=
  ∀ x y : ℂ, ‖x - y‖ = 1 → c x ≠ c y

end EuclideanFiveColor

noncomputable section
open MeasureTheory
namespace EuclideanFiveColor
instance anglePeriodPositive : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
abbrev Angles := AddCircle (2*Real.pi)
def angularMeasure : Measure Angles := AddCircle.haarAddCircle
def direction (t : Angles) : ℂ := AddCircle.toCircle t
instance : IsProbabilityMeasure angularMeasure := inferInstanceAs (IsProbabilityMeasure (AddCircle.haarAddCircle (T := 2*Real.pi)))
instance : angularMeasure.IsAddHaarMeasure := inferInstanceAs (AddCircle.haarAddCircle (T := 2*Real.pi)).IsAddHaarMeasure
lemma direction_continuous : Continuous direction := continuous_subtype_val.comp AddCircle.continuous_toCircle
@[simp] lemma direction_norm (t : Angles) : ‖direction t‖ = 1 := Circle.norm_coe _
@[simp] lemma direction_real (t : ℝ) : direction (t : Angles) = (Circle.exp t : ℂ) := by
  simp [direction,AddCircle.toCircle_apply_mk,Real.pi_ne_zero]
/-- Exactly the manuscript weak measurable condition, using normalized Haar angular measure.
A function is understood up to a plane-null set; no regularity is imposed on a proper coloring. -/
def WeakColoring (k : ℕ) (c : ℂ → Fin k) : Prop :=
  AEMeasurable c (volume : Measure ℂ) ∧ ∀ᵐ p ∂(volume : Measure ℂ).prod angularMeasure,
    c p.1 ≠ c (p.1+direction p.2)

end EuclideanFiveColor
end

end OAI
