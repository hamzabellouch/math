import OAI.Algebra.Finitistic.Selected.SelectedRectification
import OAI.Algebra.Finitistic.Localization.TensorCohomologyDiagram
import OAI.Algebra.Finitistic.Rectification.FullTensorProperties

namespace OAI
noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace LittleFinitistic.SelectedTensor
open SelectedFixedDiagram SelectedRectification QuadraticEncoding
variable (N : Type) [AddCommGroup N] [Module ℂ N] [Module (B P) N]

/-- Evaluate the one fixed selecting bimodule, retaining its full left action. -/
abbrev complex := FullTensorRectification.tensor P D0 D1 D2 f g relations N
abbrev source (v : Fin 3) := FullTensorRectification.source P D0 D1 D2 N v
abbrev comparison (v : Fin 3) (n : ℤ) :=
  TensorCohomologyDiagram.comparison P D0 D1 D2 f g relations N v n

/-- Every cohomology comparison is invertible for the fixed selected representatives. -/
instance comparison_isIso (v : Fin 3) (n : ℤ) : IsIso (comparison N v n) := by
  obtain ⟨l₀,h₀,b₀⟩ := UnderlyingRepresentatives.bounded P fixed.D0
  obtain ⟨l₁,h₁,b₁⟩ := UnderlyingRepresentatives.bounded P fixed.D1
  obtain ⟨l₂,h₂,b₂⟩ := UnderlyingRepresentatives.bounded P fixed.D2
  let lo := min l₀ (min l₁ l₂)
  let hi := max h₀ (max h₁ h₂)
  refine TensorCohomologyDiagram.comparison_isIso P D0 D1 D2 f g relations N v n lo hi
    (fun n hn => b₀ n ?_) (fun n hn => b₁ n ?_) (fun n hn => b₂ n ?_)
    (UnderlyingRepresentatives.projective P fixed.D0)
    (UnderlyingRepresentatives.projective P fixed.D1)
    (UnderlyingRepresentatives.projective P fixed.D2)
  all_goals dsimp [lo,hi] at hn; omega

def comparisonIso (v : Fin 3) (n : ℤ) := asIso (comparison N v n)

/-- The actual tensor complex has bounded support. -/
theorem bounded : ∃ lo hi : ℤ, ∀ n, n < lo ∨ hi < n → IsZero ((complex N).X n) := by
  obtain ⟨lo,hi,h⟩ := SelectedRectification.verified
  exact ⟨lo-2,hi,FullTensorProperties.bounded ℂ (B P) N bimodule (lo-2) hi h.bounded⟩

/-- Every actual evaluated term is finite-dimensional. -/
theorem finite [FiniteDimensional ℂ N] (n : ℤ) :
    FiniteDimensional ℂ ((ModuleCat.restrictScalars (algebraMap ℂ (B P))).obj ((complex N).X n)) := by
  obtain ⟨lo,hi,h⟩ := SelectedRectification.verified
  have : FiniteDimensional ℂ ((ExternalTensor.Section4.forgetK ℂ (B P)).obj (bimodule.X n)) := h.finite n
  exact FullTensorProperties.finite ℂ (B P) N (bimodule.X n)
end LittleFinitistic.SelectedTensor

end

end OAI
