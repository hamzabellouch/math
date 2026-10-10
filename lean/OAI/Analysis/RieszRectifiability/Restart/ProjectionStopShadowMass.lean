import Mathlib
import OAI.Analysis.RieszRectifiability.Restart.ActiveLevelOriginalMass
import OAI.Analysis.RieszRectifiability.Nets.FittedCellShadow

namespace OAI

/-!
# Projected mass of stopping-cell shadows

The stopping-cell radius bound converts individual fitted-plane shadow estimates into
a Hausdorff measure bound for their projected union, controlled by the top cell's mass.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal

def projectionStopShadowConstant (n : ℕ) (C σ κ : ℝ) : ℝ :=
  ((planeUnitHausdorffMeasure n).toReal * (2 : ℝ) ^ n * (3 : ℝ) ^ n) *
    (σ + κ) * (2 : ℝ) ^ n * (C * (8 : ℝ) ^ n)

theorem cellRegion_stopping_radius_power_le_top {n d : ℕ}
    (ν : Measure (Ambient d)) (C G : ℝ) (hC : 0 < C) (hG : 0 < G)
    (hg : GlobalUpperGrowth n G ν)
    (hlower : ∀ x ∈ ν.support, ∀ r : ℝ, AdmissibleRadius ν r →
      ENNReal.ofReal (r ^ n / C) ≤ ν (ball x r))
    (R : ℝ) (hR : 0 < R) (k : ℕ) (hcore : AdmissibleRadius ν (latticeRadius R k / 8))
    (z : (supportLatticeNets ν R hR k).points)
    (Good : SupportCellDescendant ν R hR k z → Prop) :
    (∑' i : cellRegionStops ν R hR k z Good, (ENNReal.ofReal i.val.radius) ^ n) ≤
      ENNReal.ofReal (C * (8 : ℝ) ^ n) * ν (cleanSupportCell ν R hR k z) := by
  calc
    _ ≤ ∑' i : cellRegionStops ν R hR k z Good,
        ENNReal.ofReal (C * (8 : ℝ) ^ n) * ν i.val.cell :=
      ENNReal.tsum_le_tsum (fun i =>
        SupportCellDescendant.radius_power_le_mass ν C G hC hG hg hlower R hR k hcore z i.val)
    _ = ENNReal.ofReal (C * (8 : ℝ) ^ n) * ∑' i : cellRegionStops ν R hR k z Good, ν i.val.cell :=
      ENNReal.tsum_mul_left
    _ ≤ _ := mul_le_mul' le_rfl (cellRegion_stopping_mass_le_top ν R hR k z Good)

theorem projection_conditioned_stopping_shadow_le_top {n d : ℕ}
    (ν : Measure (Ambient d)) (C G : ℝ) (hC : 0 < C) (hG : 0 < G)
    (hg : GlobalUpperGrowth n G ν)
    (hlower : ∀ x ∈ ν.support, ∀ r : ℝ, AdmissibleRadius ν r →
      ENNReal.ofReal (r ^ n / C) ≤ ν (ball x r))
    (R : ℝ) (hR : 0 < R) (k : ℕ) (hcore : AdmissibleRadius ν (latticeRadius R k / 8))
    (z : (supportLatticeNets ν R hR k).points)
    (S : SupportCellDescendant ν R hR k z → AffineSubspace ℝ (Ambient d))
    (hS : ∀ i, IsAffineNPlane n (S i)) (hcenter : ∀ i, i.center ∈ S i)
    (P : Submodule ℝ (Ambient d)) (σ κ : ℝ)
    (hσ : 0 < σ) (hκ : 0 ≤ κ) (hwidth : σ + κ ≤ 1)
    (hfit : ∀ i, ∀ x ∈ ν.support ∩ closedBall i.center (1024 * i.radius),
      infDist x (S i : Set (Ambient d)) ≤ σ * i.radius)
    (T : Ambient d →L[ℝ] Ambient n) (hT : ∀ x, ‖T x‖ ≤ ‖x‖)
    (hnorm : ∀ x, ‖T x‖ = ‖P.starProjection x‖) :
    (μH[(n : ℝ)] : Measure (Ambient n))
      (T '' (⋃ i : cellRegionStops ν R hR k z (cellProjectionNoncollapse S P κ), i.val.cell)) ≤
        ENNReal.ofReal (projectionStopShadowConstant n C σ κ) * ν (cleanSupportCell ν R hR k z) := by
  let := supportCellDescendant_countable ν R hR k z
  let Good := cellProjectionNoncollapse S P κ
  let B : ℝ := ((planeUnitHausdorffMeasure n).toReal * (2 : ℝ) ^ n * (3 : ℝ) ^ n) *
    (σ + κ) * (2 : ℝ) ^ n
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hcell : ∀ i : cellRegionStops ν R hR k z Good,
      (μH[(n : ℝ)] : Measure (Ambient n)) (T '' i.val.cell) ≤
        ENNReal.ofReal B * (ENNReal.ofReal i.val.radius) ^ n := by
    intro i
    have h := projection_conditioned_cell_shadow_bound ν R hR k z S hS hcenter P σ κ
      hσ hκ hwidth hfit T hT hnorm i
    convert! h using 1
    rw [← ENNReal.ofReal_pow i.val.radius_pos.le, ← ENNReal.ofReal_mul hB]
    congr 1
    dsimp only [B]
    rw [mul_pow]
    ring
  have hrad := cellRegion_stopping_radius_power_le_top ν C G hC hG hg hlower R hR k hcore z Good
  calc
    _ = (μH[(n : ℝ)] : Measure (Ambient n))
        (⋃ i : cellRegionStops ν R hR k z Good, T '' i.val.cell) := by rw [Set.image_iUnion]
    _ ≤ ∑' i : cellRegionStops ν R hR k z Good,
        (μH[(n : ℝ)] : Measure (Ambient n)) (T '' i.val.cell) := measure_iUnion_le _
    _ ≤ ∑' i : cellRegionStops ν R hR k z Good,
        ENNReal.ofReal B * (ENNReal.ofReal i.val.radius) ^ n := ENNReal.tsum_le_tsum hcell
    _ = ENNReal.ofReal B * ∑' i : cellRegionStops ν R hR k z Good,
        (ENNReal.ofReal i.val.radius) ^ n := ENNReal.tsum_mul_left
    _ ≤ ENNReal.ofReal B * (ENNReal.ofReal (C * (8 : ℝ) ^ n) * ν (cleanSupportCell ν R hR k z)) :=
      mul_le_mul' le_rfl hrad
    _ = _ := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul hB]
      rfl

end

end RieszRectifiability

end OAI
