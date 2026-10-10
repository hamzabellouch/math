import Mathlib
import OAI.Analysis.RieszRectifiability.Nets.CellChainComposition
import OAI.Analysis.RieszRectifiability.Flatness.FlatCellBadDescendantWitness

namespace OAI

/-!
# Charging nonflat descendants below a flat seed

The propagation horizon and positive flatness threshold are chosen uniformly before
the measure. A descendant with large bilateral beta below a flat seed then yields a
bad oscillation cell at an intermediate depth. Composition of relative descendants
places this witness in the original cell tree, preserving containment between the
nonflat descendant, its charged bad cell, and the flat seed.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal ENNReal

theorem exists_uniform_flat_seed_global_charge {p d : ℕ} (hnd : p + 1 ≤ d)
    (C G H ε : ℝ) (D : ℝ≥0) (hC : 0 < C) (hG : 0 ≤ G) (hH : 1 ≤ H) (hε : 0 < ε) :
    ∃ J : ℕ, ∃ α : ℝ, 0 < α ∧ 2 * α < ε * H ∧
      ∀ μ : Measure (Ambient d), GlobalUpperGrowth (p + 1) G μ →
      (∀ x ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
        ENNReal.ofReal (r ^ (p + 1) / C) ≤ μ (ball x r)) →
      (∀ η : ℝ, 0 < η → ∀ f : Ambient d → ℝ, MemLp f 2 μ →
        MemLp (truncated (p + 1) μ η f) 2 μ ∧
          eLpNorm (truncated (p + 1) μ η f) 2 μ ≤ (D : ℝ≥0∞) * eLpNorm f 2 μ) →
      ∀ (R : ℝ) (hR : 0 < R) (k : ℕ) (z : (supportLatticeNets μ R hR k).points),
      ∀ S : SupportCellDescendant μ R hR k z,
      AdmissibleRadius μ ((H * S.radius) * (2 : ℝ) ^ propagationHorizon J) →
      HasFlatCell (p + 1) μ R hR (k + S.depth) ⟨S.center, S.mem_net⟩
        (H * (2 : ℝ) ^ propagationHorizon J + 2) α →
      ∀ Q : SupportCellDescendant μ R hR k z, S.depth < Q.depth → Q.cell ⊆ S.cell →
      ε ≤ bilateralBeta (p + 1) μ Q.center (H * Q.radius) →
      ∃ t : BadSupportDescendant (p + 1) μ R hR k z
        (H * propagationTestRadius J + 2) ((H / 64) ^ (p + 2) * propagationScale J ^ 3),
        S.depth ≤ t.val.depth ∧ t.val.depth < Q.depth ∧ Q.cell ⊆ t.val.cell ∧ t.val.cell ⊆ S.cell := by
  obtain ⟨J, α, hα, hsmall, hcharge⟩ := exists_uniform_flat_seed_bad_cell_witness hnd C G H ε D
    hC hG hH hε
  refine ⟨J, α, hα, hsmall, ?_⟩
  intro μ hg hlower hRiesz R hR k z S horizon hflat Q hSQ hQsub hbad
  obtain ⟨q, hqdepth, hqcenter, hqcell, hqradius⟩ := S.exists_relative_descendant Q hSQ.le hQsub
  have hqpos : 0 < q.depth := by omega
  have hqbad : ε ≤ bilateralBeta (p + 1) μ q.center (H * q.radius) := by
    rw [hqcenter, hqradius]
    exact hbad
  obtain ⟨t, htdepth, hsub⟩ := hcharge μ hg hlower hRiesz R hR (k + S.depth)
    ⟨S.center, S.mem_net⟩ horizon hflat q hqpos hqbad
  have hfail : ¬ ScalarOscillationBound (p + 1) μ (S.compose t.val).center
      ((H * propagationTestRadius J + 2) * (S.compose t.val).radius)
      (((H / 64) ^ (p + 2) * propagationScale J ^ 3) * (S.compose t.val).radius ^ (p + 2)) := by
    rw [S.compose_radius]
    exact t.property
  refine ⟨⟨S.compose t.val, hfail⟩, ?_, ?_, ?_, ?_⟩
  · simp only [SupportCellDescendant.compose_depth, Nat.le_add_right]
  · simp only [SupportCellDescendant.compose_depth]
    omega
  · rw [S.compose_cell, ← hqcell]
    exact hsub
  · rw [S.compose_cell]
    exact t.val.cell_subset_top

end

end RieszRectifiability

end OAI
