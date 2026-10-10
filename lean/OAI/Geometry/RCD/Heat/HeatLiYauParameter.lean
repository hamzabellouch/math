import OAI.Geometry.RCD.Coordinates.HeatLiYauParameterRegularized

namespace OAI

/-! # The actual heat gradient satisfies Li--Yau for every parameter above one -/

open Set Filter MeasureTheory TopologicalSpace
open scoped NNReal ENNReal Topology
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  (hn : 2 ≤ n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

include hn p in
theorem heat_liYau_parameter (hK : K ≤ 0) (α : ℝ) (hα : 1 < α)
    (f : Lp ℝ 2 (hausdorff n X)) (hf0 : 0 ≤ f) (A : ℝ≥0)
    (hf : ∀ᵐ x ∂hausdorff n X, |f x| ≤ A) {T : ℝ} (hT : 0 < T) :
    ∀ᵐ x ∂hausdorff n X,
      localGamma (hausdorff n X) hX.quadratic
        (heatSobolev (hausdorff n X) hX.quadratic T hT f)
        (heatSobolev (hausdorff n X) hX.quadratic T hT f) x ≤
      α*heatAt (hausdorff n X) hX.quadratic T f x*
        (-heatGeneratorAt (hausdorff n X) hX.quadratic T f) x+
      (((n:ℝ)*α^2/2)*(|K|/(α-1)+1/T))*(heatAt (hausdorff n X) hX.quadratic T f x)^2 := by
  let m := hausdorff n X
  let Q := hX.quadratic
  let e : ℕ → ℝ := fun i => 1/(i+1:ℝ)
  have he (i : ℕ) : 0 < e i := by dsimp only [e]; positivity
  have he0 : Tendsto e atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hb := ae_all_iff.mpr (fun i : ℕ =>
    hX.heat_liYau_parameter_regularized hn p hK α hα f hf0 A hf hT (he i))
  filter_upwards [hb] with x hx
  have hv := he0.add_const (heatAt m Q T f x)
  simp only [zero_add] at hv
  have hlim := ((hv.const_mul α).mul
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (-heatGeneratorAt m Q T f) x) atTop
      (𝓝 ((-heatGeneratorAt m Q T f) x)))).add
    ((hv.pow 2).const_mul (((n:ℝ)*α^2/2)*(|K|/(α-1)+1/T)))
  exact ge_of_tendsto hlim (.of_forall hx)

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
