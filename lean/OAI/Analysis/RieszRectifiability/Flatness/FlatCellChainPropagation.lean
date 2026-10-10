import Mathlib
import OAI.Analysis.RieszRectifiability.Flatness.FlatCellCenterTransfer
import OAI.Analysis.RieszRectifiability.Nets.CellDyadicScales
import OAI.Analysis.RieszRectifiability.Nets.CellOscillationTransfer
import OAI.Analysis.RieszRectifiability.Flatness.FlatSeedChainPropagation

namespace OAI

/-!
# Flatness propagation along cell chains

A flat initial cell and oscillation bounds on its ancestors control bilateral beta at every
descendant center. Six binary steps correspond to one lattice depth; nearby-ball transfer
provides the intervening dyadic bounds required by flat-seed propagation.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal ENNReal

theorem exists_uniform_flat_cell_chain_propagation {p d : ℕ} (hnd : p + 1 ≤ d)
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
      bilateralBeta (p + 1) μ z (H * latticeRadius R k) < ε ∧
      ∀ i : SupportCellDescendant μ R hR k z, 0 < i.depth →
      (∀ q : SupportCellDescendant μ R hR k z, q.depth < i.depth → i.center ∈ q.cell →
        ScalarOscillationBound (p + 1) μ q.center ((H * propagationTestRadius J + 2) * q.radius)
          (((H / 64) ^ (p + 2) * propagationScale J ^ 3) * q.radius ^ (p + 2))) →
      bilateralBeta (p + 1) μ i.center (H * i.radius) < ε := by
  obtain ⟨J, _, α₀, hα₀, _, hchain⟩ := exists_uniform_flat_seed_chain_propagation hnd C G hC hG
    (5 / 4) (by norm_num) (by norm_num) D ε hε 0
  have hHp : 0 < H := by linarith
  let α := min α₀ (ε * H / 4)
  have hα : 0 < α := lt_min hα₀ (by positivity)
  have hα₀le : α ≤ α₀ := min_le_left _ _
  have hsmall : 2 * α < ε * H := by
    have hh : α ≤ ε * H / 4 := min_le_right _ _
    nlinarith [mul_pos hε hHp]
  refine ⟨J, α, hα, hsmall, ?_⟩
  intro μ hg hlower hRiesz R hR k z horizon hflat
  have hpow : 1 ≤ (2 : ℝ) ^ propagationHorizon J := one_le_pow₀ (by norm_num)
  constructor
  · exact HasFlatCell.beta_lt μ R hR k z _ H α ε hHp (by nlinarith) hα.le hsmall hflat
  · intro i hi hosc
    have htube := HasFlatCell.tube_at_descendant_center μ R hR k z H α₀
      (propagationHorizon J) hH hα₀.le
      (HasFlatCell.mono μ R hR k z _ _ α α₀ le_rfl hα₀le hflat) i
    have hbinary (j : ℕ) (hj : j < 6 * i.depth) :
        ScalarOscillationBound (p + 1) μ i.center
          (descendantRadius (H * latticeRadius R k) j * propagationTestRadius J)
          (descendantRadius (H * latticeRadius R k) j ^ (p + 2) * propagationScale J ^ 3) := by
      obtain ⟨q, hq, _, hicell⟩ := i.exists_ancestor_at_depth (j / 6) (by omega)
      have hqbefore : q.depth < i.depth := by omega
      have hqr : q.radius = latticeRadius R (k + j / 6) := by
        simp only [SupportCellDescendant.radius, hq]
      have hbounds := descendantRadius_cell_bounds R H hR hHp k j
      rw [← hqr] at hbounds
      apply cell_oscillation_controls_nearby_ball μ G hg i.center q.center
        (descendantRadius (H * latticeRadius R k) j) q.radius H (propagationTestRadius J)
        (propagationScale J) (descendantRadius_pos _ (mul_pos hHp (latticeRadius_pos R hR k)) j)
        q.radius_pos hHp (by unfold propagationTestRadius; positivity)
        (propagationScale_pos J).le (q.dist_center_of_mem i.center hicell)
        hbounds.2 hbounds.1 (hosc q hqbefore hicell)
    have hgood := hchain μ hg hlower i.center i.center_mem_support (H * latticeRadius R k)
      (mul_pos hHp (latticeRadius_pos R hR k)) horizon htube hRiesz (6 * i.depth)
      hbinary (6 * i.depth) le_rfl
    have heq : descendantRadius (H * latticeRadius R k) (6 * i.depth) = H * i.radius := by
      change _ = H * latticeRadius R (k + i.depth)
      rw [latticeRadius_eq_descendantRadius]
      simp only [descendantRadius]
      ring
    rw [heq] at hgood
    exact hgood.2 (by omega)

end

end RieszRectifiability

end OAI
