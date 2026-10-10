import OAI.MeasureTheory.Falconer.Estimates.RegularSourceClasses

namespace OAI

/-! # Simultaneous actual leaf representatives for the retained classes -/

namespace Falconer.Regularization
open Set MeasureTheory
open scoped ENNReal
variable {d : ℕ}

theorem source_representatives (Q : DyadicCube d) (μ : Measure (Space d))
    (N B : ℕ) (t : ℝ≥0∞) (s lam : ℝ)
    (h : ∀ T ∈ regularizationIndex Q μ N B t,
      ∃ p ∈ regularizationLeaves Q μ N, regularizationLabel Q μ N B p = T ∧
        RegularizedProfileData Q (sourceClass Q μ N B p) N s lam (sourceUnitProfile Q μ N B p)) :
    ∃ p : List ℕ → CellPath d,
      (∀ T ∈ regularizationIndex Q μ N B t, p T ∈ regularizationLeaves Q μ N) ∧
      (∀ T ∈ regularizationIndex Q μ N B t, regularizationLabel Q μ N B (p T) = T) ∧
      (∀ T ∈ regularizationIndex Q μ N B t,
        RegularizedProfileData Q (sourceClass Q μ N B (p T)) N s lam (sourceUnitProfile Q μ N B (p T))) := by
  classical
  let p : List ℕ → CellPath d := fun T =>
    if hT : T ∈ regularizationIndex Q μ N B t then (h T hT).choose else []
  refine ⟨p,?_,?_,?_⟩
  · intro T hT
    simpa only [p,dite_eq_left hT] using (h T hT).choose_spec.1
  · intro T hT
    simpa only [p,dite_eq_left hT] using (h T hT).choose_spec.2.1
  · intro T hT
    simpa only [p,dite_eq_left hT] using (h T hT).choose_spec.2.2

end Falconer.Regularization

end OAI
