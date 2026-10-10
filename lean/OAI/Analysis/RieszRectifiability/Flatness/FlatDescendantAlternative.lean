import Mathlib
import OAI.Analysis.RieszRectifiability.Flatness.CellFlatAnnularAlternative
import OAI.Analysis.RieszRectifiability.Flatness.FlatCellSeeds

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set

theorem exists_uniform_flat_descendant_annular_alternative {n d : ℕ}
    (hn : 1 ≤ n) (hnd : n ≤ d) (C G B A α : ℝ)
    (hC : 0 < C) (hA : 1 ≤ A) (hα : 0 < α) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 / 16 ∧ ∃ I : ℕ, 0 < I ∧
      ∀ μ : Measure (Ambient d), GlobalUpperGrowth n G μ →
      (∀ x ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
        ENNReal.ofReal (r ^ n / C) ≤ μ (ball x r)) →
      ∀ (R₀ : ℝ) (hR₀ : 0 < R₀) (k : ℕ) (z : (supportLatticeNets μ R₀ hR₀ k).points),
      AdmissibleRadius μ (latticeRadius R₀ k / 8) →
      HasFlatDescendant n μ R₀ hR₀ k z I A α ∨
        HasLargeCellAnnulus n μ R₀ hR₀ k z ρ B := by
  obtain ⟨ρ, hρ, hρcap, hchoose⟩ := exists_uniform_cell_flat_annular_alternative hn hnd C G B
    (α / (1024 * (A + 2))) hC (by positivity)
  obtain ⟨I, hI, hflat⟩ := exists_uniform_flat_ball_to_cell hnd ρ A α hρ hA hα
  refine ⟨ρ, hρ, hρcap, I, hI, ?_⟩
  intro μ hg hlower R₀ hR₀ k z hcore
  rcases hchoose μ hg hlower R₀ hR₀ k z hcore with hf | ha
  · exact Or.inl (hflat μ R₀ hR₀ k z hf)
  · exact Or.inr ha

end

end RieszRectifiability

end OAI
