import Mathlib
import OAI.Analysis.RieszRectifiability.Restart.ActiveLevelOriginalMass
import OAI.Analysis.RieszRectifiability.Restart.ActiveRegionZeroSet
import OAI.Analysis.RieszRectifiability.Nets.HausdorffFiniteCoverBound

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal

def activeRegionZeroAreaConstant (n : ℕ) (C : ℝ) : ℝ≥0∞ :=
  (6 : ℝ≥0∞) ^ n * ENNReal.ofReal (C * 8 ^ n)

theorem activeRegionZeroAreaConstant_lt_top (n : ℕ) (C : ℝ) :
    activeRegionZeroAreaConstant n C < ⊤ := by
  exact ENNReal.mul_lt_top (by finiteness) ENNReal.ofReal_lt_top

theorem active_region_zero_set_area_le_top {n d : ℕ}
    (μ : Measure (Ambient d)) (C G : ℝ) (hC : 0 < C) (hG : 0 < G)
    (hg : GlobalUpperGrowth n G μ)
    (hlower : ∀ x ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
      ENNReal.ofReal (r ^ n / C) ≤ μ (ball x r))
    (R : ℝ) (hR : 0 < R) (k : ℕ) (hcore : AdmissibleRadius μ (latticeRadius R k / 8))
    (z : (supportLatticeNets μ R hR k).points)
    (Good : SupportCellDescendant μ R hR k z → Prop) :
    (μH[(n : ℝ)] : Measure (Ambient d)) (cellRegionZeroSet μ R hR k z Good) ≤
      activeRegionZeroAreaConstant n C * μ (cleanSupportCell μ R hR k z) := by
  classical
  let ι (t : ℕ) := ↥(activeLevelIndex μ R hR k z Good t)
  let B (t : ℕ) (i : ι t) := closedBall i.val.center (3 * latticeRadius R (k + t))
  have hrad (t : ℕ) (i : ι t) : i.val.radius = latticeRadius R (k + t) := by
    have hi := (mem_activeLevelIndex μ R hR k z Good t i).mp i.property
    simp only [SupportCellDescendant.radius, hi.1]
  have hdiam (t : ℕ) (i : ι t) : ediam (B t i) ≤ ENNReal.ofReal (6 * latticeRadius R (k + t)) := by
    apply ediam_le_of_forall_dist_le
    intro x hx y hy
    have hx' : dist x i.val.center ≤ 3 * latticeRadius R (k + t) := hx
    have hy' : dist y i.val.center ≤ 3 * latticeRadius R (k + t) := hy
    have ht := dist_triangle_right x y i.val.center
    linarith
  have hcover (t : ℕ) : cellRegionZeroSet μ R hR k z Good ⊆ ⋃ i : ι t, B t i := by
    intro x hx
    have hsmall : cellRegionStoppingScale μ R hR k z Good x < latticeRadius R (k + t) := by
      rw [show cellRegionStoppingScale μ R hR k z Good x = 0 from hx]
      exact latticeRadius_pos R hR (k + t)
    obtain ⟨i, hi, hxi⟩ := exists_active_level_center_of_small_stopping_scale μ R hR k z Good t x hsmall
    exact mem_iUnion.mpr ⟨⟨i, (mem_activeLevelIndex μ R hR k z Good t i).mpr hi⟩, hxi.le⟩
  have hdecay : Tendsto (fun t : ℕ => 6 * latticeRadius R (k + t)) atTop (𝓝 0) := by
    simp_rw [latticeRadius_add]
    simpa only [mul_zero] using! (latticeRadius_tendsto_zero (latticeRadius R k)).const_mul 6
  have hdecay' : Tendsto (fun t : ℕ => ENNReal.ofReal (6 * latticeRadius R (k + t))) atTop (𝓝 0) := by
    simpa only [ENNReal.ofReal_zero] using! (ENNReal.continuous_ofReal.tendsto 0).comp hdecay
  apply hausdorff_measure_le_of_shrinking_finite_covers n _ ι _ hdecay' B hdiam hcover
  intro t
  have hmass := active_level_radius_power_sum_le_top μ C G hC hG hg hlower R hR k hcore z Good t
  calc
    _ ≤ ∑ i : ι t, (ENNReal.ofReal (6 * latticeRadius R (k + t))) ^ n :=
      Finset.sum_le_sum (fun i _ => pow_le_pow_left' (hdiam t i) n)
    _ = (6 : ℝ≥0∞) ^ n * ∑ i : ι t, (ENNReal.ofReal i.val.radius) ^ n := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [hrad t i, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 6), ENNReal.ofReal_ofNat, mul_pow]
    _ ≤ (6 : ℝ≥0∞) ^ n * (ENNReal.ofReal (C * 8 ^ n) * μ (cleanSupportCell μ R hR k z)) :=
      mul_le_mul_right hmass _
    _ = _ := by unfold activeRegionZeroAreaConstant; rw [mul_assoc]

end

end RieszRectifiability

end OAI
