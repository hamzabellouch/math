import OAI.Geometry.RCD.Coordinates.RegularActualPatches

namespace OAI

/-! # A single total family of actual patch operators -/

open Set Metric MeasureTheory
open scoped InnerProductSpace

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- Extending the selected net centers outside the net makes the
operator family total without changing any active patch. -/
structure RegularPatchSelection {K : ℝ} {n : ℕ} {hX : NoncollapsedRCD K n X}
    [(hausdorff n X).Regular] {base : X} {ker : ℝ → X → X → ℝ}
    {hk : IsContinuousHeatKernel (hausdorff n X) hX.quadratic ker}
    {enlargement zeta : ℝ} (d : RegularBilinearData hX base hk enlargement zeta)
    (psi : Euclidean n → ℝ) {Cpin budget : ℝ} (f : RegularPinchingField d Cpin budget) where
  center : ℕ → X → {q : X // q ∈ ball base (d.radius / 32)}
  active : ∀ i y, y ∈ d.patchNet i → (center i y).val ∈ d.patchDomain psi i y
  near : ∀ i y, y ∈ d.patchNet i → ∀ q, q ∈ d.patchDomain psi i y →
    dist (center i y).val q ≤ (d.radius / 2 ^ (d.shift + i + 15)) / 12
  energy : ∀ i y, y ∈ d.patchNet i →
    ∀ q : {q : X // q ∈ ball base (d.radius / 32)}, q.val ∈ d.patchDomain psi i y →
    ⟪d.values q.val - d.values (center i y).val,
      d.pinchingMassMatrix (center i y).val (center i y).property (d.shift + i)
        (d.values q.val - d.values (center i y).val)⟫_ℝ ≤
        (3 * Cpin) * (distanceSourceRadius d.radius (d.shift + i)) ^ 2 * f.energy q (d.shift + i)

/-- The selector is constructed from the already proved finite covers
and positive energy floors. -/
def regularPatchSelection {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular]
    {base : X} {a κ B J C A Cχ enlargement zeta eta Cpin budget : ℝ}
    {ker : ℝ → X → X → ℝ}
    {hk : IsContinuousHeatKernel (hausdorff n X) hX.quadratic ker}
    (e : RegularProjectionEnvironment hX base hk a κ B J C A Cχ enlargement zeta eta)
    (hzeta : zeta ≤ 1 / 64) (psi : EuclideanGevreyCutoff n)
    (f : RegularPinchingField e.heat Cpin budget) (hCpin : 0 ≤ Cpin) :
    RegularPatchSelection e.heat psi.value f := by
  classical
  let c := Classical.choose (exists_regular_actual_patch_centers hX e hzeta psi f hCpin)
  have hc := Classical.choose_spec (exists_regular_actual_patch_centers hX e hzeta psi f hCpin)
  let fallback : {q : X // q ∈ ball base (e.heat.radius / 32)} :=
    ⟨base, mem_ball_self (div_pos e.heat.radius_pos (by norm_num))⟩
  let center := fun i y => if hy : y ∈ e.heat.patchNet i then c i ⟨y, hy⟩ else fallback
  refine { center := center, active := ?_, near := ?_, energy := ?_ }
  · intro i y hy
    simpa only [center, dite_eq_left hy] using (hc i ⟨y, hy⟩).1
  · intro i y hy q hq
    have hq' := e.heat.patch_region_subset hq.1
    simpa only [center, dite_eq_left hy] using ((hc i ⟨y, hy⟩).2 ⟨q, hq'⟩ hq).1
  · intro i y hy q hq
    simpa only [center, dite_eq_left hy] using ((hc i ⟨y, hy⟩).2 q hq).2

end RegularPointCoordinates

end

end OAI
