import Mathlib
import OAI.Combinatorics.KMedian.Hardness.ProjectionEncoding
import OAI.Combinatorics.KMedian.Hardness.Reduction

namespace OAI

section Inline_PCPInherited

namespace MetricKMedian.Coverage
open Complexity

def ProjectionReduction (ε : ℚ) (L : Language) : Prop :=
  ∃ r a b : ℕ, ∃ reduce : Word → ProjectionInput r a b,
    FinitePolyTime id ProjectionInput.encode reduce ∧
    (∀ x, x ∈ L → (reduce x).Perfect) ∧
    (∀ x, x ∉ L → (reduce x).Sound (ε : ℝ))

def ProjectionGapNPReductions : Prop :=
  ∀ ε : ℚ, 0 < ε → ∀ L ∈ NP, ProjectionReduction ε L

theorem reduction_from_projections {δ : ℝ} (P : PartitionParameters δ)
    {L : Language} (h : ProjectionReduction P.ε L) :
    ∃ reduce : Word → Input, FinitePolyTime id Input.encode reduce ∧
      (∀ x, x ∈ L → (reduce x).Perfect) ∧
      (∀ x, x ∉ L → (reduce x).Sound δ) := by
  obtain ⟨r,a,b,f,hf,hy,hn⟩ := h
  have hD : 0 < P.D := by have := P.D_ge; omega
  let g : ProjectionInput r a b → Input := fun G => G.toCoverage P.D hD
  refine ⟨g ∘ f,hf.comp (ProjectionInput.coverage_finite_poly P.D hD),?_,?_⟩
  · intro x hx
    exact (f x).coverage_perfect P.D hD (hy x hx)
  · intro x hx
    exact (f x).coverage_sound P (hn x hx)

theorem remaining_projection_obstruction (hPNP : PNeNP) {α : ℝ}
    (hα : α ∈ approximationFactors) (hsmall : α < 1+2/Real.exp 1) :
    ∃ ε : ℚ, 0 < ε ∧ ∃ L : Language, L ∈ NP ∧ ¬ ProjectionReduction ε L := by
  obtain ⟨δ,hδ,L,hL,hno⟩ := remaining_gap_obstruction hPNP hα hsmall
  obtain ⟨P⟩ := partition_parameters_exist hδ
  exact ⟨P.ε,P.ε_pos,L,hL,fun h => hno (reduction_from_projections P h)⟩

end MetricKMedian.Coverage

end Inline_PCPInherited

end OAI
