import OAI.Geometry.RCD.Coordinates.RegularActualPatches
import OAI.Geometry.RCD.Coordinates.RegularNearbyFrozen
import OAI.Geometry.RCD.Coordinates.NormalizedUpdate

namespace OAI

/-! # Uniform Gevrey jets of the actual heat-coordinate cutoffs -/

open Set Metric MeasureTheory
open scoped InnerProductSpace ContDiff

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- The support localization places its net center within the radius
where the frozen heat frames can be compared. -/
theorem regular_active_patch_distance {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular]
    {base : X} {a κ B J C A Cχ enlargement zeta eta : ℝ}
    {ker : ℝ → X → X → ℝ}
    {hk : IsContinuousHeatKernel (hausdorff n X) hX.quadratic ker}
    (e : RegularProjectionEnvironment hX base hk a κ B J C A Cχ enlargement zeta eta)
    (hzeta : zeta ≤ 1 / 64) (psi : EuclideanGevreyCutoff n) (i : ℕ)
    {q y : X} (hq : q ∈ e.heat.patchRegion) (hy : y ∈ e.heat.patchNet i)
    (hactive : e.heat.values q ∈ tsupport (e.heat.patchCutoff psi.value i y)) :
    dist y q ≤ e.heat.radius / 2 ^ (e.heat.shift + i + 17) := by
  have h := (regular_actual_patch_cover hX e hzeta psi i).active_localized q hq y hy hactive
  have hr : 0 < regularNetRadius e.heat.radius e.heat.shift i := div_pos e.heat.radius_pos (by positivity)
  have heq : e.heat.radius / 2 ^ (e.heat.shift + i + 17) =
      2048 * regularNetRadius e.heat.radius e.heat.shift i := by
    unfold regularNetRadius
    rw [show e.heat.shift + i + 28 = (e.heat.shift + i + 17) + 11 by omega, pow_add]
    norm_num
    ring
  rw [dist_comm, heq]
  change dist q y ≤ 144 * regularNetRadius e.heat.radius e.heat.shift i at h
  linarith

/-- The affine input of the actual cutoff has uniformly bounded norm
after normalization at the testing point. The scale ratio is exactly
2^27; the numerical bound also absorbs the nearby-frame comparison. -/
theorem regular_cutoff_normalized_jet {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular]
    {base : X} {a κ B J C A Cχ enlargement zeta eta : ℝ}
    {ker : ℝ → X → X → ℝ}
    {hk : IsContinuousHeatKernel (hausdorff n X) hX.quadratic ker}
    (e : RegularProjectionEnvironment hX base hk a κ B J C A Cχ enlargement zeta eta)
    (hzeta0 : 0 ≤ zeta) (hzeta : zeta ≤ 1 / 64)
    (hsmall : (n : ℝ) ^ 2 * (((5 / 3 : ℝ) * ((1 / 2 : ℝ) ^ n)⁻¹) * zeta) ≤ 1 / 4)
    (psi : EuclideanGevreyCutoff n) (i : ℕ)
    {q y : X} (hq : q ∈ e.heat.patchRegion) (hy : y ∈ e.heat.patchNet i)
    (hactive : e.heat.values q ∈ tsupport (e.heat.patchCutoff psi.value i y)) (m : ℕ) :
    ‖iteratedFDeriv ℝ m (fun z => e.heat.patchCutoff psi.value i y
      (frozenSource (distanceSourceRadius e.heat.radius (e.heat.shift + i))
        (e.heat.frozenAt q i) (e.heat.values q) z)) 0‖ ≤
      (psi.constant * 536870912) ^ (m + 1) * (m.factorial : ℝ) ^ 2 := by
  let s := distanceSourceRadius e.heat.radius (e.heat.shift + i)
  let r : ℝ := e.heat.patchRadius i
  let P := e.heat.frozenAt q i
  let Q := e.heat.frozenAt y i
  let D : Euclidean n →L[ℝ] Euclidean n := Q.toContinuousLinearMap.comp P.symm.toContinuousLinearMap
  let L : Euclidean n →L[ℝ] Euclidean n := (s / r) • D
  let b := r⁻¹ • Q (e.heat.values q - e.heat.values y)
  have hr : 0 < r := div_pos e.heat.radius_pos (by positivity)
  have hs : 0 < s := distanceSourceRadius_pos e.heat.radius_pos _
  have hratio : s / r = 134217728 := by
    change distanceSourceRadius e.heat.radius (e.heat.shift + i) /
      regularNetRadius e.heat.radius e.heat.shift i = _
    unfold distanceSourceRadius regularNetRadius
    rw [show e.heat.shift + i + 28 = (e.heat.shift + i + 1) + 27 by omega, pow_add]
    norm_num
    field_simp [e.heat.radius_pos.ne']
    ring
  have hD : ‖D‖ ≤ 3 := by
    have hq' := e.heat.patch_region_subset hq
    have hy' := e.heat.patch_region_subset ((regular_actual_patch_cover hX e hzeta psi i).center_mem hy)
    exact regular_nearby_frozen_operator hX e hq' hy' hzeta0 hsmall i
      (regular_active_patch_distance hX e hzeta psi i hq hy hactive)
  have hL : ‖L‖ ≤ 536870912 := by
    dsimp only [L]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos hs hr), hratio]
    nlinarith
  have heq : (fun z => e.heat.patchCutoff psi.value i y
      (frozenSource s P (e.heat.values q) z)) = fun z => psi.value (b + L z) := by
    funext z
    change psi.value (r⁻¹ • Q (e.heat.values q + s • P.symm z - e.heat.values y)) = _
    congr 1
    have hv : e.heat.values q + s • P.symm z - e.heat.values y =
        (e.heat.values q - e.heat.values y) + s • P.symm z := by abel
    rw [hv, map_add, map_smul, smul_add]
    simp only [b, L, D, smul_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe, div_eq_mul_inv, smul_smul, mul_comm]
  rw [heq]
  exact psi.affine_jet_le L b 0 m (by norm_num) hL

end RegularPointCoordinates

end

end OAI
