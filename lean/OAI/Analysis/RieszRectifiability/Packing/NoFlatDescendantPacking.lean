import Mathlib
import OAI.Analysis.RieszRectifiability.Flatness.FlatDescendantAlternative
import OAI.Analysis.RieszRectifiability.Foundations.AnnularDescendantTotalMass

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal NNReal

def NoFlatDescendant {d : ℕ} (n : ℕ) (μ : Measure (Ambient d)) (R₀ : ℝ) (hR₀ : 0 < R₀)
    (k : ℕ) (z : (supportLatticeNets μ R₀ hR₀ k).points) (I : ℕ) (A α : ℝ) :=
  {i : SupportCellDescendant μ R₀ hR₀ k z //
    ¬ HasFlatDescendant n μ R₀ hR₀ (k + i.depth) ⟨i.center, i.mem_net⟩ I A α}

theorem exists_uniform_no_flat_descendant_total_mass {n d : ℕ} (hn : 1 ≤ n) (hnd : n ≤ d)
    (C G A α : ℝ) (D : ℝ≥0) (hC : 0 < C) (hG : 0 < G) (hA : 1 ≤ A) (hα : 0 < α) :
    ∃ I : ℕ, 0 < I ∧ ∃ K : ℝ, 0 < K ∧ ∀ μ : Measure (Ambient d),
      GlobalUpperGrowth n G μ →
      (∀ x ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
        ENNReal.ofReal (r ^ n / C) ≤ μ (ball x r)) →
      (∀ ε : ℝ, 0 < ε → ∀ f : Ambient d → ℝ, MemLp f 2 μ →
        MemLp (truncated n μ ε f) 2 μ ∧
          eLpNorm (truncated n μ ε f) 2 μ ≤ (D : ℝ≥0∞) * eLpNorm f 2 μ) →
      ∀ (R₀ : ℝ) (hR₀ : 0 < R₀) (k : ℕ) (z : (supportLatticeNets μ R₀ hR₀ k).points),
      AdmissibleRadius μ (latticeRadius R₀ k / 8) →
      ∑' i : NoFlatDescendant n μ R₀ hR₀ k z I A α,
        μ i.val.cell ≤ ENNReal.ofReal K * μ (cleanSupportCell μ R₀ hR₀ k z) := by
  classical
  obtain ⟨ρ, hρ, _, I, hI, hchoose⟩ := exists_uniform_flat_descendant_annular_alternative hn hnd
    C G (annularCellComparisonError n C G D + 1) A α hC hA hα
  obtain ⟨K, hK, hpack⟩ := exists_uniform_large_annulus_carleson_constant n d hn C G ρ 1 D
    hC hG hρ (by norm_num)
  refine ⟨I, hI, K, hK, ?_⟩
  intro μ hg hlower hRiesz R₀ hR₀ k z hcore
  let Bad := NoFlatDescendant n μ R₀ hR₀ k z I A α
  have hann (i : Bad) : HasLargeCellAnnulus n μ R₀ hR₀ (k + i.val.depth)
      ⟨i.val.center, i.val.mem_net⟩ ρ (annularCellComparisonError n C G D + 1) := by
    have hicore : AdmissibleRadius μ (latticeRadius R₀ (k + i.val.depth) / 8) := by
      simpa only [one_div_mul_eq_div, SupportCellDescendant.radius] using! i.val.core_admissible hcore
    exact (hchoose μ hg hlower R₀ hR₀ (k + i.val.depth)
      ⟨i.val.center, i.val.mem_net⟩ hicore).resolve_left i.property
  let emb : Bad ↪ SupportCellDescendant μ R₀ hR₀ k z := ⟨Subtype.val, Subtype.val_injective⟩
  have hbound (s : Finset Bad) : ∑ i ∈ s, μ.real i.val.cell ≤
      K * μ.real (cleanSupportCell μ R₀ hR₀ k z) := by
    have hs : ∀ i ∈ s.map emb, HasLargeCellAnnulus n μ R₀ hR₀ (k + i.depth)
        ⟨i.center, i.mem_net⟩ ρ (annularCellComparisonError n C G D + 1) := by
      intro i hi
      obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp hi
      exact hann j
    have hb := hpack μ hg hlower hRiesz R₀ hR₀ k z hcore (s.map emb) hs
    simpa only [Finset.sum_map] using! hb
  have hb := measure_tsum_le_of_real_finset_bounds μ (fun i : Bad => i.val.cell)
    (K * μ.real (cleanSupportCell μ R₀ hR₀ k z))
    (fun i => (cleanSupportCell_finite_of_growth μ G hg R₀ hR₀ (k + i.val.depth)
      ⟨i.val.center, i.val.mem_net⟩).ne) hbound
  have hf := (cleanSupportCell_finite_of_growth μ G hg R₀ hR₀ k z).ne
  simpa only [ENNReal.ofReal_mul hK.le, Measure.real, ENNReal.ofReal_toReal hf] using! hb

end

end RieszRectifiability

end OAI
