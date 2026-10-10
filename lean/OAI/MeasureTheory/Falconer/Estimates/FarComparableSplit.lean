import OAI.MeasureTheory.Falconer.Estimates.ActualNoncomparableFar
import OAI.MeasureTheory.Falconer.Estimates.ActualComparableFarError

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
attribute [local instance] Classical.propDecidable

theorem integral_noncomparable_comparable (μ : Measure (Fin 4 → Plane))
    (F : (Fin 4 → Plane) → ℂ) (hF : Integrable F μ) :
    (∫ x, F x ∂μ) = (∫ x in angularLengthLeft ∪ angularLengthRight, F x ∂μ) +
      (∫ x in angularLengthComparable, F x ∂μ) := by
  have hu : (angularLengthLeft ∪ angularLengthRight) ∪ angularLengthComparable = univ := by
    apply Set.eq_univ_of_forall
    intro x
    rcases angular_length_trichotomy x with h | h | h
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h)
    · exact Or.inr h
  have hd : Disjoint (angularLengthLeft ∪ angularLengthRight) angularLengthComparable :=
    disjoint_union_left.mpr ⟨angular_length_left_comparable_disjoint,angular_length_right_comparable_disjoint⟩
  have hh := setIntegral_union hd measurable_angularLengthComparable hF.integrableOn hF.integrableOn
  simpa only [hu,Measure.restrict_univ] using hh

theorem angular_far_comparable_split (Q₁ Q₂ : DyadicSquare)
    (ρ ν : Measure Plane) [IsFiniteMeasure ρ] [IsFiniteMeasure ν]
    (A B : CellPath) (a d : ℕ) (v : ℝ) {Ψ : ℝ → ℝ}
    (hΨ : Measurable Ψ) (hpos : ∀ t, 0 ≤ Ψ t)
    (hs : ∀ t, Ψ t ≠ 0 → t ∈ Ioo (1/4:ℝ) 4)
    {W : ℝ} (hW : 0 ≤ W) (hw : ∀ t, Ψ t ≤ W)
    (Ma₁ Ma₂ : ℝ) {Mp₁ Mp₂ : ℝ} (hMp₁ : 0 < Mp₁) (hMp₂ : 0 < Mp₂)
    (β γ : Plane → UnitCircle → ℂ)
    (hβ : Measurable (fun z : Plane × UnitCircle => β z.1 z.2))
    (hγ : Measurable (fun z : Plane × UnitCircle => γ z.1 z.2))
    {D₁ D₂ : ℝ} (hD₁ : 0 ≤ D₁) (hD₂ : 0 ≤ D₂)
    (hbβ : ∀ x u, ‖β x u‖ ≤ D₁) (hbγ : ∀ x u, ‖γ x u‖ ≤ D₂) :
    angularCellContribution Q₁ Q₂ ρ ν A B d a v Ψ Ma₁ Ma₂ Mp₁ Mp₂ β γ
      (fun row col => ¬ angularNear Q₁ Q₂ (a+d) row col) =
    angularNoncomparableFarContribution Q₁ Q₂ ρ ν A B a d v Ma₁ Ma₂
      (angularOriginalSpatialKernel β γ v Ψ) +
    angularComparableFarContribution Q₁ Q₂ ρ ν A B a d v Ma₁ Ma₂
      (angularOriginalSpatialKernel β γ v Ψ) := by
  rw [angular_contribution_spatial_sum Q₁ Q₂ ρ ν A B d a v hΨ hpos hs hW hw
    Ma₁ Ma₂ hMp₁ hMp₂ β γ hβ hγ hD₁ hD₂ hbβ hbγ]
  unfold angularNoncomparableFarContribution angularComparableFarContribution
  rw [← smul_add,← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro row hr
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro col hc
  by_cases hf : ¬ angularNear Q₁ Q₂ (a+d) row col
  · simp only [hf,not_false_eq_true,↓reduceIte]
    rw [angularCellSpatialIntegral_pair]
    exact integral_noncomparable_comparable (angularFourCellMeasure Q₁ Q₂ ρ ν row col) _
      (angularOriginalSpatialKernel_integrable _ β γ hβ hγ hD₁ hD₂ hbβ hbγ v hΨ hs hW
        (fun t => by rw [abs_of_nonneg (hpos t)]; exact hw t))
  · simp [hf]

end PlanarFalconer

end OAI
