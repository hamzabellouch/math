import OAI.Geometry.SurfaceImmersion.Atlas.PhaseChartStability

namespace OAI

/-! Uniform mode coefficients and normal fields on the fixed local phase chart. -/
noncomputable section
open Set
open scoped ContDiff
namespace ClosedSurfaceR4.PhaseGeometry
open SmallModes RealModes WeightedEstimates

/-- The radius and all constant profiles are fixed before the perturbed map.
Only its weighted two-jet size enters, with the explicit polynomial power. -/
theorem GoodPhaseChart.uniform_mode_bounds {F : RField 4} (hF : ContDiff ℝ ∞ F)
    {φ : Base → ℝ} (c : GoodPhaseChart F φ) :
    ∃ (ρ : ℝ) (D E : ℕ → ℝ), 0 < ρ ∧ (∀ m, 1 ≤ D m) ∧ (∀ m, 1 ≤ E m) ∧
      ∀ (G : RField 4), ContDiff ℝ ∞ G → ∀ C₀ : ℝ, 0 ≤ C₀ → C₀ < ρ →
      WeightedBound univ 1 2 C₀ (G-F) →
      RealModeDomain (G ∘ c.chart.symm) c.chart.target ∧
      ∀ (m : ℕ) (s C : ℝ), 0 < s → 1 ≤ C →
        WeightedBound c.chart.target s m C (realTwoJet (G ∘ c.chart.symm)) →
        ReconstructionCoefficientBound (fun p => complexify ((G ∘ c.chart.symm) p))
          c.chart.target s m ((m.factorial : ℝ) * D m * C^m) ∧
        WeightedBound c.chart.target s m ((m.factorial : ℝ) * E m * C^m)
          (freeNormal (G ∘ c.chart.symm)) := by
  obtain ⟨ρ,Q,hρ,hQ,hQa,hnear⟩ := c.uniform_jet_neighborhood hF
  choose D hD hd using fun m => compact_real_reconstruction_bounds c.chart.open_target
    admissibleRealJets_domain hQ hQa m
  choose E hE he using fun m => compact_freeNormal_bound c.chart.open_target
    admissibleRealJets_domain hQ hQa m
  refine ⟨ρ,D,E,hρ,hD,hE,?_⟩
  intro G hG C₀ hC₀ hCρ hb
  obtain ⟨hmap,hdom⟩ := hnear G hG C₀ hC₀ hCρ hb
  refine ⟨hdom,?_⟩
  intro m s C hs hC hj
  exact ⟨hd m (G ∘ c.chart.symm) s C hs hC (hG.comp c.smoothInverse) hmap hj,
    he m (G ∘ c.chart.symm) s C hs hC (hG.comp c.smoothInverse) hmap hj⟩

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
