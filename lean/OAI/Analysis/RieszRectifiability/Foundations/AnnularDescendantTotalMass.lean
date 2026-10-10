import Mathlib
import OAI.Analysis.RieszRectifiability.Packing.UniformAnnularCarleson
import OAI.Analysis.RieszRectifiability.Nets.LatticeOscillationTotalMass

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal NNReal

def LargeAnnularDescendant {d : ℕ} (n : ℕ) (μ : Measure (Ambient d)) (R₀ : ℝ) (hR₀ : 0 < R₀)
    (k : ℕ) (z : (supportLatticeNets μ R₀ hR₀ k).points) (ρ β : ℝ) :=
  {i : SupportCellDescendant μ R₀ hR₀ k z //
    HasLargeCellAnnulus n μ R₀ hR₀ (k + i.depth) ⟨i.center, i.mem_net⟩ ρ β}

theorem exists_uniform_large_annulus_total_mass (n d : ℕ) (hn : 1 ≤ n)
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
      ∑' i : LargeAnnularDescendant n μ R₀ hR₀ k z ρ (annularCellComparisonError n C G D + v),
        μ i.val.cell ≤ ENNReal.ofReal K * μ (cleanSupportCell μ R₀ hR₀ k z) := by
  classical
  obtain ⟨K, hK, hpack⟩ := exists_uniform_large_annulus_carleson_constant n d hn C G ρ v D hC hG hρ hv
  refine ⟨K, hK, ?_⟩
  intro μ hg hlower hRiesz R₀ hR₀ k z hcore
  let A := LargeAnnularDescendant n μ R₀ hR₀ k z ρ (annularCellComparisonError n C G D + v)
  let emb : A ↪ SupportCellDescendant μ R₀ hR₀ k z := ⟨Subtype.val, Subtype.val_injective⟩
  have hbound (s : Finset A) : ∑ i ∈ s, μ.real i.val.cell ≤
      K * μ.real (cleanSupportCell μ R₀ hR₀ k z) := by
    have hs : ∀ i ∈ s.map emb, HasLargeCellAnnulus n μ R₀ hR₀ (k + i.depth)
        ⟨i.center, i.mem_net⟩ ρ (annularCellComparisonError n C G D + v) := by
      intro i hi
      obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp hi
      exact j.property
    have hb := hpack μ hg hlower hRiesz R₀ hR₀ k z hcore (s.map emb) hs
    simpa only [Finset.sum_map] using! hb
  have hb := measure_tsum_le_of_real_finset_bounds μ (fun i : A => i.val.cell)
    (K * μ.real (cleanSupportCell μ R₀ hR₀ k z))
    (fun i => (cleanSupportCell_finite_of_growth μ G hg R₀ hR₀ (k + i.val.depth)
      ⟨i.val.center, i.val.mem_net⟩).ne) hbound
  have hf := (cleanSupportCell_finite_of_growth μ G hg R₀ hR₀ k z).ne
  simpa only [ENNReal.ofReal_mul hK.le, Measure.real, ENNReal.ofReal_toReal hf] using! hb

end

end RieszRectifiability

end OAI
