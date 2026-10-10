import Mathlib
import OAI.Analysis.RieszRectifiability.Restart.ActiveRegionStopMassArea

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal

theorem radius_eight_growth_le_original_cell_mass {n d : ℕ}
    (μ : Measure (Ambient d)) (C G : ℝ) (hC : 0 < C) (hG : 0 < G)
    (hg : GlobalUpperGrowth n G μ)
    (hlower : ∀ x ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
      ENNReal.ofReal (r ^ n / C) ≤ μ (ball x r))
    (R : ℝ) (hR : 0 < R) (k : ℕ) (hcore : AdmissibleRadius μ (latticeRadius R k / 8))
    (z : (supportLatticeNets μ R hR k).points) (K : ℝ) (hK : 0 ≤ K) :
    ENNReal.ofReal (K * (8 * latticeRadius R k) ^ n) ≤
      ENNReal.ofReal (K * C * (64 : ℝ) ^ n) * μ (cleanSupportCell μ R hR k z) := by
  have hmass := (cleanSupportCell_measure_bounds μ C G hC hG hg hlower R hR k hcore z).1
  have heq : ENNReal.ofReal (K * (8 * latticeRadius R k) ^ n) =
      ENNReal.ofReal (K * C * (64 : ℝ) ^ n) * ENNReal.ofReal ((latticeRadius R k / 8) ^ n / C) := by
    rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ K * C * (64 : ℝ) ^ n)]
    congr 1
    rw [show (64 : ℝ) = 8 * 8 by norm_num, mul_pow, mul_pow, div_pow]
    field_simp
  rw [heq]
  exact mul_le_mul' le_rfl hmass

theorem exists_depth_for_weighted_geometric_loss
    (ρ : ℝ) (hρ : 0 ≤ ρ) (hρ1 : ρ < 1)
    (W : ℝ≥0∞) (hW : W < ⊤) (A : ℝ) (hA : 0 ≤ A) (δ : ℝ) (hδ : 0 < δ) :
    ∃ J : ℕ, W * (ENNReal.ofReal ρ) ^ J * ENNReal.ofReal A ≤ ENNReal.ofReal δ := by
  let B : ℝ := W.toReal * A + 1
  have hB : 0 < B := by dsimp only [B]; positivity
  have htend := tendsto_pow_atTop_nhds_zero_of_lt_one hρ hρ1
  have hevent : ∀ᶠ J : ℕ in atTop, ρ ^ J < δ / B :=
    htend.eventually (gt_mem_nhds (div_pos hδ hB))
  obtain ⟨J, hJ⟩ := hevent.exists
  have hJ' : ρ ^ J * B < δ := (lt_div_iff₀ hB).mp hJ
  have hpow : 0 ≤ ρ ^ J := pow_nonneg hρ J
  refine ⟨J, ?_⟩
  rw [← ENNReal.ofReal_toReal hW.ne, ← ENNReal.ofReal_pow hρ,
    ← ENNReal.ofReal_mul ENNReal.toReal_nonneg,
    ← ENNReal.ofReal_mul (mul_nonneg ENNReal.toReal_nonneg hpow)]
  apply ENNReal.ofReal_le_ofReal
  dsimp only [B] at hJ'
  nlinarith

end

end RieszRectifiability

end OAI
