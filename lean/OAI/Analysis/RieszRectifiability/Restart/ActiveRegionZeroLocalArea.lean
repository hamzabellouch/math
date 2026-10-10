import Mathlib
import OAI.Analysis.RieszRectifiability.Restart.ActiveRegionZeroSetArea
import OAI.Analysis.RieszRectifiability.Restart.ActiveLevelLocalMass

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal

def activeRegionZeroLocalAreaConstant (n : ℕ) (C G : ℝ) : ℝ≥0∞ :=
  (6 : ℝ≥0∞) ^ n * ENNReal.ofReal (C * 8 ^ n) * ENNReal.ofReal G * (2 : ℝ≥0∞) ^ n

theorem activeRegionZeroLocalAreaConstant_lt_top (n : ℕ) (C G : ℝ) :
    activeRegionZeroLocalAreaConstant n C G < ⊤ := by
  unfold activeRegionZeroLocalAreaConstant
  finiteness

theorem active_region_zero_local_ball_area_le {n d : ℕ}
    (μ : Measure (Ambient d)) (C G : ℝ) (hC : 0 < C) (hG : 0 < G)
    (hg : GlobalUpperGrowth n G μ)
    (hlower : ∀ x ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
      ENNReal.ofReal (r ^ n / C) ≤ μ (ball x r))
    (R : ℝ) (hR : 0 < R) (k : ℕ) (hcore : AdmissibleRadius μ (latticeRadius R k / 8))
    (z : (supportLatticeNets μ R hR k).points)
    (Good : SupportCellDescendant μ R hR k z → Prop)
    (p : Ambient d) (r : ℝ) (hr : 0 < r) :
    (μH[(n : ℝ)] : Measure (Ambient d)) (cellRegionZeroSet μ R hR k z Good ∩ closedBall p r) ≤
      activeRegionZeroLocalAreaConstant n C G * (ENNReal.ofReal r) ^ n := by
  classical
  obtain ⟨N, hN⟩ := exists_annular_lattice_depth R k r hr
  let F (t : ℕ) := (activeLevelIndex μ R hR k z Good (N + t)).filter
    (fun i => dist i.center p ≤ r + 3 * latticeRadius R (k + (N + t)))
  let ι (t : ℕ) := ↥(F t)
  let B (t : ℕ) (i : ι t) := closedBall i.val.center (3 * latticeRadius R (k + (N + t)))
  have hF (t : ℕ) : F t ⊆ activeLevelIndex μ R hR k z Good (N + t) := Finset.filter_subset _ _
  have hrad (t : ℕ) (i : ι t) : i.val.radius = latticeRadius R (k + (N + t)) := by
    have hi := (mem_activeLevelIndex μ R hR k z Good (N + t) i).mp (hF t i.property)
    simp only [SupportCellDescendant.radius, hi.1]
  have hrsmall (t : ℕ) : latticeRadius R (k + (N + t)) ≤ r / 8 :=
    (latticeRadius_antitone R hR.le (by omega : k + N ≤ k + (N + t))).trans hN
  have hdiam (t : ℕ) (i : ι t) : ediam (B t i) ≤ ENNReal.ofReal (6 * latticeRadius R (k + (N + t))) := by
    apply ediam_le_of_forall_dist_le
    intro x hx y hy
    have hx' : dist x i.val.center ≤ 3 * latticeRadius R (k + (N + t)) := hx
    have hy' : dist y i.val.center ≤ 3 * latticeRadius R (k + (N + t)) := hy
    have ht := dist_triangle_right x y i.val.center
    linarith
  have hcover (t : ℕ) : cellRegionZeroSet μ R hR k z Good ∩ closedBall p r ⊆ ⋃ i : ι t, B t i := by
    intro x hx
    have hsmall : cellRegionStoppingScale μ R hR k z Good x < latticeRadius R (k + (N + t)) := by
      rw [show cellRegionStoppingScale μ R hR k z Good x = 0 from hx.1]
      exact latticeRadius_pos R hR _
    obtain ⟨i, hi, hxi⟩ := exists_active_level_center_of_small_stopping_scale μ R hR k z Good (N + t) x hsmall
    have hip : dist i.center p ≤ r + 3 * latticeRadius R (k + (N + t)) := by
      have hxp : dist x p ≤ r := hx.2
      have ht := dist_triangle i.center x p
      rw [dist_comm i.center x] at ht
      linarith
    have hiF : i ∈ F t := Finset.mem_filter.mpr
      ⟨(mem_activeLevelIndex μ R hR k z Good (N + t) i).mpr hi, hip⟩
    exact mem_iUnion.mpr ⟨⟨i, hiF⟩, hxi.le⟩
  have hdecay : Tendsto (fun t : ℕ => ENNReal.ofReal (6 * latticeRadius R (k + (N + t)))) atTop (𝓝 0) := by
    have hreal : Tendsto (fun t : ℕ => 6 * latticeRadius R (k + (N + t))) atTop (𝓝 0) := by
      simpa only [latticeRadius, pow_add, mul_assoc, mul_zero] using!
        (latticeRadius_tendsto_zero (latticeRadius R (k + N))).const_mul 6
    simpa only [ENNReal.ofReal_zero] using! (ENNReal.continuous_ofReal.tendsto 0).comp hreal
  apply hausdorff_measure_le_of_shrinking_finite_covers n _ ι _ hdecay B hdiam hcover
  intro t
  have hcells : ∀ i ∈ F t, i.cell ⊆ ball p (2 * r) := by
    intro i hi y hy
    have hip := (Finset.mem_filter.mp hi).2
    have hyi := i.dist_center_of_mem y hy
    have hri : i.radius = latticeRadius R (k + (N + t)) := hrad t ⟨i, hi⟩
    rw [hri] at hyi
    have ht := dist_triangle y i.center p
    change dist y p < 2 * r
    linarith [hrsmall t]
  have hmass := active_level_subfamily_radius_power_sum_le μ C G hC hG hg hlower R hR k hcore z Good
    (N + t) (F t) (hF t) (ball p (2 * r)) hcells
  have hμ := hg.2 p (2 * r) (by positivity)
  calc
    _ ≤ ∑ i : ι t, (ENNReal.ofReal (6 * latticeRadius R (k + (N + t)))) ^ n :=
      Finset.sum_le_sum (fun i _ => pow_le_pow_left' (hdiam t i) n)
    _ = (6 : ℝ≥0∞) ^ n * ∑ i : ι t, (ENNReal.ofReal i.val.radius) ^ n := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [hrad t i, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 6), ENNReal.ofReal_ofNat, mul_pow]
    _ ≤ (6 : ℝ≥0∞) ^ n * (ENNReal.ofReal (C * 8 ^ n) * μ (ball p (2 * r))) :=
      mul_le_mul_right hmass _
    _ ≤ (6 : ℝ≥0∞) ^ n * (ENNReal.ofReal (C * 8 ^ n) * ENNReal.ofReal (G * (2 * r) ^ n)) := by
      gcongr
    _ = activeRegionZeroLocalAreaConstant n C G * (ENNReal.ofReal r) ^ n := by
      rw [ENNReal.ofReal_mul hG.le, ENNReal.ofReal_pow (by positivity : 0 ≤ 2 * r),
        ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat, mul_pow]
      unfold activeRegionZeroLocalAreaConstant
      ring

end

end RieszRectifiability

end OAI
