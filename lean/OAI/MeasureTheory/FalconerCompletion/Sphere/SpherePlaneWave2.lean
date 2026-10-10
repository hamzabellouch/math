import Mathlib
import OAI.MeasureTheory.FalconerCompletion.Graphs.GraphFixedSpatialTerm

namespace OAI

/-! Canonical spherical measures and differential identities. -/

section
section
namespace CurrentFalconer
open MeasureTheory Set
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
noncomputable def spherePlaneWaveND (Λ : ℝ) (e x : V) : ℂ :=
  Complex.exp (Complex.I*Λ*(inner ℝ x e : ℂ))

lemma spherePlaneWaveND_norm (Λ : ℝ) (e w : V) : ‖spherePlaneWaveND Λ e w‖=1 := by
  simp [spherePlaneWaveND,Complex.norm_exp]
variable [MeasurableSpace V]
noncomputable def sourceAngularTransformND (ρ : Measure V) (X : Set V) (M : ℝ)
    (b : V → V → ℂ) (r : ℝ) (w : V) : ℂ :=
  M⁻¹ • ∫ x in X, spherePlaneWaveND r x w*b x w ∂ρ
end CurrentFalconer
end
end

end OAI
