import Mathlib
import OAI.Analysis.RieszRectifiability.Nets.BadCellTestFamily
import OAI.Analysis.RieszRectifiability.Flatness.FlatCellChainPropagation

namespace OAI

/-!
# An oscillation witness above a nonflat descendant

Uniform flat-cell chain propagation forces a nonflat positive-depth descendant to have an
earlier ancestor where the scalar oscillation bound fails. The resulting bad descendant contains
the entire offending cell; its depth, testing radius, and oscillation threshold retain the
uniform propagation parameters chosen before the measure.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal ENNReal

theorem exists_uniform_flat_seed_bad_cell_witness {p d : ℕ} (hnd : p + 1 ≤ d)
    (C G H ε : ℝ) (D : ℝ≥0) (hC : 0 < C) (hG : 0 ≤ G) (hH : 1 ≤ H) (hε : 0 < ε) :
    ∃ J : ℕ, ∃ α : ℝ, 0 < α ∧ 2 * α < ε * H ∧
      ∀ μ : Measure (Ambient d), GlobalUpperGrowth (p + 1) G μ →
      (∀ x ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
        ENNReal.ofReal (r ^ (p + 1) / C) ≤ μ (ball x r)) →
      (∀ η : ℝ, 0 < η → ∀ f : Ambient d → ℝ, MemLp f 2 μ →
        MemLp (truncated (p + 1) μ η f) 2 μ ∧
          eLpNorm (truncated (p + 1) μ η f) 2 μ ≤ (D : ℝ≥0∞) * eLpNorm f 2 μ) →
      ∀ (R : ℝ) (hR : 0 < R) (k : ℕ) (z : (supportLatticeNets μ R hR k).points),
      AdmissibleRadius μ ((H * latticeRadius R k) * (2 : ℝ) ^ propagationHorizon J) →
      HasFlatCell (p + 1) μ R hR k z (H * (2 : ℝ) ^ propagationHorizon J + 2) α →
      ∀ i : SupportCellDescendant μ R hR k z, 0 < i.depth →
      ε ≤ bilateralBeta (p + 1) μ i.center (H * i.radius) →
      ∃ q : BadSupportDescendant (p + 1) μ R hR k z
        (H * propagationTestRadius J + 2) ((H / 64) ^ (p + 2) * propagationScale J ^ 3),
        q.val.depth < i.depth ∧ i.cell ⊆ q.val.cell := by
  classical
  obtain ⟨J, α, hα, hsmall, hprop⟩ := exists_uniform_flat_cell_chain_propagation hnd C G H ε D
    hC hG hH hε
  refine ⟨J, α, hα, hsmall, ?_⟩
  intro μ hg hlower hRiesz R hR k z horizon hflat i hi hbad
  have hnot : ¬ ∀ q : SupportCellDescendant μ R hR k z,
      q.depth < i.depth → i.center ∈ q.cell →
      ScalarOscillationBound (p + 1) μ q.center ((H * propagationTestRadius J + 2) * q.radius)
        (((H / 64) ^ (p + 2) * propagationScale J ^ 3) * q.radius ^ (p + 2)) := by
    intro hall
    exact (not_lt_of_ge hbad) ((hprop μ hg hlower hRiesz R hR k z horizon hflat).2 i hi hall)
  push Not at hnot
  obtain ⟨q, hqi, hc, hfail⟩ := hnot
  exact ⟨⟨q, hfail⟩, hqi, i.cell_subset_of_center_mem q hqi.le hc⟩

end

end RieszRectifiability

end OAI
