import OAI.Analysis.IrrationalRotation.Rotation.ParameterPositiveDiagonal
import OAI.Analysis.IrrationalRotation.Rotation.CircleTruncationMass

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal InnerProductSpace

namespace Invariant233.CircleParameterLaws

variable {θ : ℝ} {p : CircleParameterData} (hp : CircleParameterLaws θ p)
local notation "e₀" => PositiveDiagonalModel.e0

theorem exists_projection_truncation_mass_threshold (hθ : Irrational θ)
    (hr : ∀ i, 0 < MixedRadix.radices p.q i)
    (P : Rotation.Hilbert →L[ℂ] Rotation.Hilbert)
    (hPm : P ∈ Rotation.algebra θ) (hP : IsStarProjection P)
    (hinv : (1 - P) * p.measurableOperator θ hp * P = 0)
    (hP0 : P ≠ 0) (hP1 : P ≠ 1)
    (F : Circle → Rotation.Fiber →L[ℂ] Rotation.Fiber)
    (hbound : ∀ x, ‖F x‖ ≤ ‖P‖)
    (hmeas : ∀ v, StronglyMeasurable fun x => F x v)
    (hrep : ∀ ξ : Rotation.Hilbert, P ξ =ᵐ[circleMeasure] fun x => F x (ξ x)) :
    ∃ J : ℕ, 1 ≤ J ∧ ∀ j : ℕ, J ≤ j →
      Real.exp (-90) / 2 ≤ (CircleCoupling.law p j).real
        (CircleCoupling.truncationEvent p j hr
          (fun x => (inner ℂ e₀ (F x e₀)).re)) := by
  let r : Circle → ℝ := fun x => (inner ℂ e₀ (F x e₀)).re
  have hm : Measurable r :=
    ((Complex.continuous_re.comp (continuous_const.inner continuous_id)).comp_stronglyMeasurable
      (hmeas e₀)).measurable
  have hi : ∀ᵐ x ∂(volume : Measure Circle), 0 < r x ∧ r x < 1 :=
    hp.ae_strict_diagonal_measurableOperator_of_nontrivial hθ P hPm hP hinv
      hP0 hP1 F hbound hmeas hrep
  exact CircleCoupling.exists_truncationEvent_mass_threshold hp hr (r := r) hm hi

theorem exists_rational_graph_field_with_truncation_mass (hθ : Irrational θ)
    (hr : ∀ i, 0 < MixedRadix.radices p.q i)
    {P : Rotation.Hilbert →L[ℂ] Rotation.Hilbert}
    (hPm : P ∈ Rotation.algebra θ) (hP : IsStarProjection P)
    (hinv : (1 - P) * p.measurableOperator θ hp * P = 0)
    (hP0 : P ≠ 0) (hP1 : P ≠ 1) :
    ∃ F : Circle → Rotation.Fiber →L[ℂ] Rotation.Fiber,
      (∀ x, IsStarProjection (F x)) ∧
      (∀ x, ‖F x‖ ≤ ‖P‖) ∧
      (∀ v, StronglyMeasurable fun x => F x v) ∧
      (∀ ξ : Rotation.Hilbert, P ξ =ᵐ[circleMeasure] fun x => F x (ξ x)) ∧
      p.RationalGraphIdentities θ F ∧
      ∃ J : ℕ, 1 ≤ J ∧ ∀ j : ℕ, J ≤ j →
        Real.exp (-90) / 2 ≤ (CircleCoupling.law p j).real
          (CircleCoupling.truncationEvent p j hr
            (fun x => (inner ℂ e₀ (F x e₀)).re)) := by
  obtain ⟨F, hproj, hbound, hmeas, hrep, hgraph, _⟩ :=
    hp.exists_strict_rational_graph_field hθ hPm hP hinv hP0 hP1
  exact ⟨F, hproj, hbound, hmeas, hrep, hgraph,
    hp.exists_projection_truncation_mass_threshold hθ hr P hPm hP hinv hP0 hP1
      F hbound hmeas hrep⟩

end Invariant233.CircleParameterLaws

end

end OAI
