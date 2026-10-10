import Mathlib
import OAI.MeasureTheory.FalconerCompletion.Sphere.SphereAmbient2

namespace OAI

/-! Angular cutoffs and derivative estimates. -/

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace Attempt4PrefixShell
open MeasureTheory Set
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable [MeasurableSpace V]
noncomputable def sourceAngularTransformND (ρ : Measure V) (X : Set V) (M : ℝ)
    (b : V → V → ℂ) (r : ℝ) (w : V) : ℂ :=
  M⁻¹ • ∫ x in X, spherePlaneWaveND r x w*b x w ∂ρ
end Attempt4PrefixShell
end GraphLiteralSupport
end
end

end OAI
