import Mathlib
import OAI.Analysis.RieszRectifiability.Packing.FiniteAnnularCarleson

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal NNReal

theorem exists_uniform_large_annulus_carleson_constant (n d : ℕ) (hn : 1 ≤ n)
    (C G ρ v : ℝ) (D : ℝ≥0) (hC : 0 < C) (hG : 0 < G) (hρ : 0 < ρ) (hv : 0 < v) :
    ∃ K : ℝ, 0 < K ∧ ∀ μ : Measure (Ambient d),
      GlobalUpperGrowth n G μ →
      (∀ x ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
        ENNReal.ofReal (r ^ n / C) ≤ μ (ball x r)) →
      (∀ ε : ℝ, 0 < ε → ∀ f : Ambient d → ℝ, MemLp f 2 μ →
        MemLp (truncated n μ ε f) 2 μ ∧
          eLpNorm (truncated n μ ε f) 2 μ ≤ (D : ℝ≥0∞) * eLpNorm f 2 μ) →
      ∀ (R₀ : ℝ) (hR₀ : 0 < R₀) (k : ℕ) (z : (supportLatticeNets μ R₀ hR₀ k).points),
      AdmissibleRadius μ (latticeRadius R₀ k / 8) →
      ∀ s : Finset (SupportCellDescendant μ R₀ hR₀ k z),
        (∀ i ∈ s, HasLargeCellAnnulus n μ R₀ hR₀ (k + i.depth) ⟨i.center, i.mem_net⟩
          ρ (annularCellComparisonError n C G D + v)) →
        ∑ i ∈ s, μ.real i.cell ≤ K * μ.real (cleanSupportCell μ R₀ hR₀ k z) := by
  classical
  obtain ⟨I, hI, hdepth⟩ := exists_uniform_depth_for_cell_annuli ρ hρ
  let K₀ := haarTopBallPackingConstant n C G 4 v D I
  have hK₀ : 0 ≤ K₀ := by
    have hm := haarCellMassRatio_pos n C G I hC hG
    unfold K₀ haarTopBallPackingConstant
    positivity
  refine ⟨K₀ + 1, by linarith, ?_⟩
  intro μ hg hlower hRiesz R₀ hR₀ k z hcore s hlarge
  have hchoice (i : s) : ∃ W : CellAnnulus μ R₀ hR₀ (k + i.val.depth)
      ⟨i.val.center, i.val.mem_net⟩ ρ, annularCellComparisonError n C G D + v ≤ ‖W.transform n‖ :=
    hlarge i.val i.property
  choose W hW using hchoice
  have hb := finite_annular_witness_mass_packing hn μ C G ρ v hC hG hv hg hlower
    R₀ hR₀ k I hI z hcore s W
    (fun i => hdepth d μ R₀ hR₀ (k + i.val.depth) ⟨i.val.center, i.val.mem_net⟩ (W i))
    D hRiesz hW
  exact hb.trans (mul_le_mul_of_nonneg_right (by change K₀ ≤ K₀ + 1; linarith) measureReal_nonneg)

end

end RieszRectifiability

end OAI
