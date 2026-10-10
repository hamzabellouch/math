import OAI.Analysis.IrrationalRotation.Analysis.ParameterOrbitIdentity
import OAI.Analysis.IrrationalRotation.Rotation.CircleRationalGraphFields

namespace OAI

noncomputable section
open MeasureTheory

namespace Invariant233.CircleParameterLaws
variable {θ : ℝ} {p : CircleParameterData} (hp : CircleParameterLaws θ p)

theorem exists_rational_graph_field
    {P : Rotation.Hilbert →L[ℂ] Rotation.Hilbert}
    (hmem : P ∈ Rotation.algebra θ) (hP : IsStarProjection P)
    (hT : (1 - P) * p.measurableOperator θ hp * P = 0) :
    ∃ F : Circle → Rotation.Fiber →L[ℂ] Rotation.Fiber,
      (∀ x, IsStarProjection (F x)) ∧
      (∀ x, ‖F x‖ ≤ ‖P‖) ∧
      (∀ v : Rotation.Fiber, StronglyMeasurable fun x => F x v) ∧
      (∀ ξ : Rotation.Hilbert, P ξ =ᵐ[circleMeasure] fun x => F x (ξ x)) ∧
      p.RationalGraphIdentities θ F := by
  obtain ⟨F, hproj, hnorm, hmeas, hrep, _, horbit⟩ :=
    hp.exists_measurableOperator_positive_orbit_field hmem hP hT
  refine ⟨F, hproj, hnorm, hmeas, hrep, ?_⟩
  apply hp.rationalGraphIdentities_of_positive_orbits F hproj
    (fun k => (hmeas (lp.single 2 k 1)).measurable)
  intro n hn
  filter_upwards [horbit] with x hx
  exact hx n

theorem rational_graphs_of_representation
    {P : Rotation.Hilbert →L[ℂ] Rotation.Hilbert}
    (hmem : P ∈ Rotation.algebra θ) (hP : IsStarProjection P)
    (hT : (1 - P) * p.measurableOperator θ hp * P = 0)
    (F : Circle → Rotation.Fiber →L[ℂ] Rotation.Fiber)
    (hrep : ∀ ξ : Rotation.Hilbert, P ξ =ᵐ[circleMeasure] fun x => F x (ξ x)) :
    p.RationalGraphIdentities θ F := by
  obtain ⟨G, _, _, _, hGrep, hG⟩ := hp.exists_rational_graph_field hmem hP hT
  have heq : G =ᵐ[circleMeasure] F :=
    L2Multiplication.field_unique_of_representation
      (default : HilbertBasis ℤ ℂ Rotation.Fiber) P G F hGrep hrep
  exact (p.rationalGraphIdentities_congr_ae θ heq).mp hG

end Invariant233.CircleParameterLaws

end

end OAI
