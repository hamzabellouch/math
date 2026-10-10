import Mathlib
import OAI.MeasureTheory.FalconerCompletion.Angular.CompactMultiplierDerivativeBound2
import OAI.MeasureTheory.FalconerCompletion.Sphere.SphereChartAmplitudeDerivativeBound2

namespace OAI

/-! Canonical spherical measures and differential identities. -/

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace Attempt4PrefixShell
open MeasureTheory Set Metric
open scoped ContDiff RealInnerProductSpace
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]

lemma sphere_parts_derivative_bound (m : ℕ) (C : ℝ) (hC : 0 ≤ C) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (b : WithLp 2 (V × ℝ) → ℂ) (A : ℝ),
      ContDiff ℝ ∞ b → 1 ≤ A →
      (∀ j ≤ m, ∀ w, ‖w‖ = 1 → ‖iteratedFDeriv ℝ j b w‖ ≤ C*A^j) →
      ∀ j ≤ m, ∀ w, ‖w‖ = 1 →
        ‖iteratedFDeriv ℝ j (sphereNorthPartND b) w‖ ≤ D*A^j ∧
        ‖iteratedFDeriv ℝ j (sphereReflectedSouthPartND b) w‖ ≤ D*A^j := by
  obtain ⟨D₁,hD₁,h₁⟩ := compact_multiplier_derivative_bound
    (w := sphereNorthCutoffND (V := V)) (isCompact_sphere 0 1)
    sphereNorthCutoffND_contDiff m C hC
  obtain ⟨D₂,hD₂,h₂⟩ := compact_multiplier_derivative_bound
    (w := fun w : WithLp 2 (V × ℝ) => 1-sphereNorthCutoffND w) (isCompact_sphere 0 1)
    (contDiff_const.sub sphereNorthCutoffND_contDiff) m C hC
  refine ⟨max D₁ D₂,le_max_of_le_left hD₁,?_⟩
  intro b A hb hA hderiv j hj w hw
  have hderiv' : ∀ j ≤ m, ∀ w ∈ sphere (0 : WithLp 2 (V × ℝ)) 1,
      ‖iteratedFDeriv ℝ j b w‖ ≤ C*A^j := by
    simpa only [mem_sphere,dist_zero_right] using hderiv
  constructor
  · exact (h₁ b A hb hA hderiv' j hj w (by simpa using hw)).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  · apply (norm_iteratedFDeriv_antipodal_conj
      ((contDiff_const.sub sphereNorthCutoffND_contDiff).mul hb) j w).trans
    exact (h₂ b A hb hA hderiv' j hj (-w) (by simpa using hw)).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))

end Attempt4PrefixShell
end GraphLiteralSupport
end
end

end OAI
