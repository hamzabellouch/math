import OAI.Geometry.RCD.Coordinates.RegularNetSeparation
import OAI.Geometry.RCD.Coordinates.PatchCoverData

namespace OAI

/-! # Actual finite heat-coordinate covers on the working region -/

open Set Metric MeasureTheory
open scoped InnerProductSpace NNReal ContDiff

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- Maximal metric nets and a fixed Euclidean cutoff produce localized
finite covers with one dimensional overlap constant at every scale. -/
theorem regular_finite_patch_cover {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular]
    {base : X} {a κ B J C A Cχ enlargement zeta eta : ℝ}
    {ker : ℝ → X → X → ℝ}
    {hk : IsContinuousHeatKernel (hausdorff n X) hX.quadratic ker}
    (e : RegularProjectionEnvironment hX base hk a κ B J C A Cχ enlargement zeta eta)
    (hzeta : zeta ≤ 1 / 64) (i : ℕ) (psi : Euclidean n → ℝ)
    (hsmooth : ContDiff ℝ ∞ psi) (hzero : ∀ z, 0 ≤ psi z) (hone : ∀ z, psi z ≤ 1)
    (hcore : ∀ z, ‖z‖ ≤ 2 → psi z = 1) (hsupport : tsupport psi ⊆ closedBall 0 3) :
    let region := regularPatchRegion base e.heat.radius e.heat.shift
    let r : ℝ≥0 := ⟨regularNetRadius e.heat.radius e.heat.shift i,
      (div_pos e.heat.radius_pos (by positivity)).le⟩
    let T := fun q => (e.heat.frozenAt q i).toContinuousLinearMap
    IsLocalizedPatchCover region r e.heat.values (maximalPatchNet r region)
      (normalizedPatchCutoff r e.heat.values T psi) (patchOverlapBound n (1 / 2) 2 3) 144 3 := by
  intro region r T
  have hr : 0 < (r : ℝ) := div_pos e.heat.radius_pos (by positivity)
  have hN : (256 : ℝ) ≤ (2 : ℝ) ^ (e.heat.shift + i + 28) := by
    have h := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
      (show 8 ≤ e.heat.shift + i + 28 by omega)
    norm_num at h ⊢
    exact h
  have hrR : (r : ℝ) ≤ e.heat.radius / 256 :=
    div_le_div_of_nonneg_left e.heat.radius_pos.le (by norm_num) hN
  have hscale : (patchLocalizationFactor (1 / 2) 2 3 + 1) * (r : ℝ) ≤ 2 * e.heat.radius := by
    norm_num [patchLocalizationFactor]
    linarith [e.heat.radius_pos]
  have hcover := bounded_maximal_normalized_patch_cover (hausdorff n X) region
    (show Bornology.IsBounded region from isBounded_ball) r
    (show 0 < r by exact_mod_cast hr) e.heat.values T psi n
    (R := 2 * e.heat.radius) (omega := euclideanUnitVolume n) (c := 1 / 2) (M := 2) (L := 3)
    (euclideanUnitVolume_pos n) (by norm_num) (by norm_num) hscale
    (fun x hx t ht htR => (e.volume x (e.heat.patch_region_subset hx) t ht htR).trans (by norm_num))
    (fun x t => ne_of_lt (hX.finiteOnBounded (ball x t) isBounded_ball))
    hsmooth hzero hone hcore hsupport
    (fun x _ y hy hxy => e.heat.net_near_pair_bound (e.heat.patch_region_subset hy) hzeta i hxy)
    (by
      intro x hx y hy hfar
      refine ⟨(2 : ℝ) • T y, ?_, ?_⟩
      · have h := e.heat.net_pair_lower_bound hy hx hzeta i hfar.le
        simp only [smul_apply, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
        change (1 / 2 : ℝ) * dist x y ≤ 2 * ‖e.heat.frozenAt y i (e.heat.values x - e.heat.values y)‖
        linarith
      · have hratio : 1 ≤ dist x y / (r : ℝ) := (one_le_div hr).mpr hfar.le
        simp only [smul_apply, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
        have h := mul_le_mul_of_nonneg_right hratio
          (sq_nonneg ‖T y (e.heat.values x - e.heat.values y)‖)
        nlinarith)
  norm_num [patchLocalizationFactor] at hcover ⊢
  exact hcover

/-- Every pair of active points is close enough for both directional
pinching and the reverse central mass-ball containment. -/
theorem regular_net_diameter_le {R : ℝ} (hR : 0 < R) (shift i : ℕ) :
    2 * 144 * regularNetRadius R shift i ≤ (R / (2 : ℝ) ^ (shift + i + 15)) / 12 := by
  have hr : 0 < regularNetRadius R shift i := div_pos hR (by positivity)
  have heq : R / (2 : ℝ) ^ (shift + i + 15) = 8192 * regularNetRadius R shift i := by
    unfold regularNetRadius
    rw [show shift + i + 28 = (shift + i + 15) + 13 by omega, pow_add]
    norm_num
    ring
  rw [heq]
  linarith

end RegularPointCoordinates

end

end OAI
