import OAI.Geometry.RCD.Coordinates.RegularFinitePatchCover
import OAI.Geometry.RCD.Coordinates.RegularPatchCenters
import OAI.Geometry.RCD.Coordinates.EuclideanGevreyCutoff

namespace OAI

/-! # Fixed actual patches and energy centers at every scale -/

open Set Metric MeasureTheory
open scoped InnerProductSpace NNReal ContDiff BigOperators

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

namespace RegularBilinearData

variable {K : ℝ} {n : ℕ} {hX : NoncollapsedRCD K n X} [(hausdorff n X).Regular]
  {base : X} {ker : ℝ → X → X → ℝ}
  {hk : IsContinuousHeatKernel (hausdorff n X) hX.quadratic ker} {enlargement zeta : ℝ}
  (d : RegularBilinearData hX base hk enlargement zeta)

def patchRadius (i : ℕ) : ℝ≥0 :=
  ⟨regularNetRadius d.radius d.shift i, (div_pos d.radius_pos (by positivity)).le⟩

def patchRegion : Set X := regularPatchRegion base d.radius d.shift

def patchNet (i : ℕ) : Finset X := maximalPatchNet (d.patchRadius i) d.patchRegion

def patchCutoff (psi : Euclidean n → ℝ) (i : ℕ) : X → Euclidean n → ℝ :=
  normalizedPatchCutoff (d.patchRadius i) d.values
    (fun q => (d.frozenAt q i).toContinuousLinearMap) psi

def patchDomain (psi : Euclidean n → ℝ) (i : ℕ) (y : X) : Set X :=
  {x | x ∈ d.patchRegion ∧ d.values x ∈ tsupport (d.patchCutoff psi i y)}

end RegularBilinearData

/-- The net is much finer than the directional pinching radius. -/
theorem regular_net_pinching_diameter_le {R : ℝ} (hR : 0 < R) (shift i : ℕ) :
    2 * 144 * regularNetRadius R shift i ≤ distanceSourceRadius R (shift + i) / 512 := by
  have hr : 0 < regularNetRadius R shift i := div_pos hR (by positivity)
  have heq : distanceSourceRadius R (shift + i) =
      134217728 * regularNetRadius R shift i := by
    unfold distanceSourceRadius regularNetRadius
    rw [show shift + i + 28 = (shift + i + 1) + 27 by omega, pow_add]
    norm_num
    ring
  rw [heq]
  linarith

theorem regular_actual_patch_cover {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular]
    {base : X} {a κ B J C A Cχ enlargement zeta eta : ℝ}
    {ker : ℝ → X → X → ℝ}
    {hk : IsContinuousHeatKernel (hausdorff n X) hX.quadratic ker}
    (e : RegularProjectionEnvironment hX base hk a κ B J C A Cχ enlargement zeta eta)
    (hzeta : zeta ≤ 1 / 64) (psi : EuclideanGevreyCutoff n) (i : ℕ) :
    IsLocalizedPatchCover e.heat.patchRegion (e.heat.patchRadius i) e.heat.values
      (e.heat.patchNet i) (e.heat.patchCutoff psi.value i)
      (patchOverlapBound n (1 / 2) 2 3) 144 3 :=
  regular_finite_patch_cover hX e hzeta i psi.value psi.smooth psi.nonneg psi.le_one
    psi.core psi.support

/-- Each operator center is fixed once for the entire active patch. The
same center satisfies both the pinching estimate and the mass comparison
distance bound; it is independent of the subsequently tested vector. -/
theorem exists_regular_actual_patch_centers {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular]
    {base : X} {a κ B J C A Cχ enlargement zeta eta Cpin budget : ℝ}
    {ker : ℝ → X → X → ℝ}
    {hk : IsContinuousHeatKernel (hausdorff n X) hX.quadratic ker}
    (e : RegularProjectionEnvironment hX base hk a κ B J C A Cχ enlargement zeta eta)
    (hzeta : zeta ≤ 1 / 64) (psi : EuclideanGevreyCutoff n)
    (f : RegularPinchingField e.heat Cpin budget) (hCpin : 0 ≤ Cpin) :
    ∃ center : ∀ i, {y : X // y ∈ e.heat.patchNet i} →
        {q : X // q ∈ ball base (e.heat.radius / 32)},
      ∀ i y,
        (center i y).val ∈ e.heat.patchDomain psi.value i y.val ∧
        ∀ x : {q : X // q ∈ ball base (e.heat.radius / 32)},
          x.val ∈ e.heat.patchDomain psi.value i y.val →
          dist (center i y).val x.val ≤ (e.heat.radius / 2 ^ (e.heat.shift + i + 15)) / 12 ∧
          ⟪e.heat.values x.val - e.heat.values (center i y).val,
            e.heat.pinchingMassMatrix (center i y).val (center i y).property (e.heat.shift + i)
              (e.heat.values x.val - e.heat.values (center i y).val)⟫_ℝ ≤
              (3 * Cpin) * (distanceSourceRadius e.heat.radius (e.heat.shift + i)) ^ 2 *
                f.energy x (e.heat.shift + i) := by
  classical
  have hcenters (i : ℕ) := f.exists_normalized_centers hCpin (e.heat.shift + i)
    e.heat.patchRegion (e.heat.patchRadius i)
    (fun q => (e.heat.frozenAt q i).toContinuousLinearMap) psi.value
    (e.heat.patchNet i) (regular_actual_patch_cover hX e hzeta psi i)
    (psi.core 0 (by simp)) (fun _ hx => e.heat.patch_region_subset hx)
    (regular_net_pinching_diameter_le e.heat.radius_pos e.heat.shift i)
  choose center hc using hcenters
  refine ⟨center, fun i y => ⟨(hc i y).1, ?_⟩⟩
  intro x hx
  refine ⟨?_, (hc i y).2 x hx⟩
  have hcover := regular_actual_patch_cover hX e hzeta psi i
  have h1 := hcover.active_localized x.val hx.1 y.val y.property hx.2
  have h2 := hcover.active_localized (center i y).val (hc i y).1.1
    y.val y.property (hc i y).1.2
  have ht := dist_triangle (center i y).val y.val x.val
  rw [dist_comm y.val x.val] at ht
  have hdiam := regular_net_diameter_le e.heat.radius_pos e.heat.shift i
  change dist x.val y.val ≤ 144 * regularNetRadius e.heat.radius e.heat.shift i at h1
  change dist (center i y).val y.val ≤ 144 * regularNetRadius e.heat.radius e.heat.shift i at h2
  linarith

namespace RegularPinchingField

variable {K : ℝ} {n : ℕ} {hX : NoncollapsedRCD K n X} [(hausdorff n X).Regular]
  {base : X} {ker : ℝ → X → X → ℝ}
  {hk : IsContinuousHeatKernel (hausdorff n X) hX.quadratic ker} {enlargement zeta C budget : ℝ}
  {d : RegularBilinearData hX base hk enlargement zeta}

/-- Starting the iteration at the heat shift preserves the total budget. -/
theorem shifted_energy_sum_le (f : RegularPinchingField d C budget)
    (q : {q : X // q ∈ ball base (d.radius / 32)}) (shift k : ℕ) :
    (∑ i ∈ Finset.range k, f.energy q (shift + i)) ≤ budget := by
  have hp (i) : 0 ≤ f.energy q i := (f.floor_pos i).le.trans (f.energy_floor q i)
  exact (nonnegative_shifted_sum_le (f.energy q) hp shift k).trans
    (((f.summable q).sum_le_tsum (Finset.range (shift + k)) (fun i _ => hp i)).trans (f.total q))

end RegularPinchingField
end RegularPointCoordinates

end

end OAI
