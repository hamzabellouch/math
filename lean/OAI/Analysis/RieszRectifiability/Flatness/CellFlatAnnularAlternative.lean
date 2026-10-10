import Mathlib
import OAI.Analysis.RieszRectifiability.Flatness.PhysicalFlatAnnularAlternative
import OAI.Analysis.RieszRectifiability.Nets.CellAnnularWitnesses

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set

theorem exists_uniform_cell_flat_annular_alternative {n d : ℕ} (hn : 1 ≤ n) (hnd : n ≤ d)
    (C G B ε : ℝ) (hC : 0 < C) (hε : 0 < ε) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 / 16 ∧ ∀ μ : Measure (Ambient d),
      GlobalUpperGrowth n G μ →
      (∀ x ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
        ENNReal.ofReal (r ^ n / C) ≤ μ (ball x r)) →
      ∀ (R₀ : ℝ) (hR₀ : 0 < R₀) (k : ℕ) (z : (supportLatticeNets μ R₀ hR₀ k).points),
      AdmissibleRadius μ (latticeRadius R₀ k / 8) →
      HasFlatBallAbove n μ (ball (z : Ambient d) (latticeRadius R₀ k / 16))
        (ρ * latticeRadius R₀ k) (latticeRadius R₀ k / 16) ε ∨
        HasLargeCellAnnulus n μ R₀ hR₀ k z ρ B := by
  obtain ⟨ρ, hρ, hρcap, hchoose⟩ := exists_uniform_physical_flat_annular_radius hn hnd C G B ε hC hε
  refine ⟨ρ, hρ, hρcap, ?_⟩
  intro μ hg hlower R₀ hR₀ k z hcore
  have hs := latticeRadius_pos R₀ hR₀ k
  rcases hchoose μ hg hlower z (supportLatticeCenter μ R₀ hR₀ k z).property
    (latticeRadius R₀ k) hs hcore with hflat | hann
  · exact Or.inl hflat
  · right
    obtain ⟨a, ha, hanear, r, R, hr, hrR, hρr, hRcap, hnorm⟩ := hann
    have hnear : dist a (z : Ambient d) ≤ latticeRadius R₀ k / 8 := by
      have ht : dist a (z : Ambient d) < latticeRadius R₀ k / 16 := hanear
      linarith
    let W : CellAnnulus μ R₀ hR₀ k z ρ :=
      { center := a, center_mem := ha, center_dist := hnear,
        innerRadius := r, outerRadius := R, inner_pos := hr, inner_le_outer := hrR,
        inner_lower := hρr, outer_upper := by linarith }
    exact ⟨W, hnorm.le⟩

end

end RieszRectifiability

end OAI
