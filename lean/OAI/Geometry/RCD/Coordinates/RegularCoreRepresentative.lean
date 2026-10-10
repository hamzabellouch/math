import OAI.Geometry.RCD.Coordinates.RegularDirichletCore

namespace OAI

/-! # Bounded compact Lipschitz representatives of the actual regular core -/

open Set Filter MeasureTheory
open scoped NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) (Q : QuadraticCheegerEnergy μ)

omit [BorelSpace X] [ProperSpace X] in
theorem regular_core_representative (u : compactLaplacianCore μ Q univ) :
    ∃ (V : X → ℝ) (L A : ℝ≥0), LipschitzWith L V ∧ HasCompactSupport V ∧
      (SobolevSpace.toLp μ Q u.val =ᵐ[μ] V) ∧
      ∀ᵐ x ∂μ, |SobolevSpace.toLp μ Q u.val x| ≤ A := by
  obtain ⟨V,L,hV,hVc,_hs,hu⟩ := u.property.1
  obtain ⟨B,hB⟩ := hVc.exists_bound_of_continuous hV.continuous
  let A : ℝ≥0 := ⟨max B 0,le_max_right _ _⟩
  refine ⟨V,L,A,hV,hVc,hu,?_⟩
  filter_upwards [hu] with x hx
  rw [hx]
  exact (show |V x| ≤ B by simpa only [Real.norm_eq_abs] using hB x).trans (le_max_left _ _)

end RegularPointCoordinates

end

end OAI
