import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedCancellationDataNorm

namespace OAI

noncomputable section
open scoped SchwartzMap
namespace Ostmann.Characters.TemplateOneSidedCancellation

theorem gatedData_false_ranges {σ τ : Type*} [Fintype σ] [Fintype τ]
    (d : HistoryPolynomialData σ τ) (ρ : 𝓢(ℝ,ℂ)) {A B : τ → ℝ} {M : ℝ}
    (hM : 0 ≤ M) (hAB : ∀t,A t ≤ B t) (hscale : ∀t,0 < d.scale t)
    (hbound : ∀t,(d.profile t).bound ρ (B t) ≤ M) :
    (gatedData false d).Ranges ρ A B M := by
  refine ⟨hM,hAB,hscale,?_,?_,hbound⟩
  · intro x hx t
    have hh := (gatedData_support false d x).mp hx
    exact False.elim (Bool.false_ne_true hh.1)
  · intro x hx t
    have hh := (gatedData_support false d x).mp hx
    exact False.elim (Bool.false_ne_true hh.1)

end Ostmann.Characters.TemplateOneSidedCancellation

end

end OAI
