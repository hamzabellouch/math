import OAI.Geometry.RCD.Coordinates.HeatHamiltonRegularized

namespace OAI

/-! # Removing the logarithmic regularization on the positive heat locus

A single countable full-measure set retains the Hamilton bounds as the
positive regularization decreases to zero.
-/

open Set Filter MeasureTheory TopologicalSpace
open scoped NNReal ENNReal Topology
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  (hn : 2≤n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

include hn p

theorem heat_hamilton_positive
    (f : Lp ℝ 2 (hausdorff n X)) (hf0 : 0≤f) (A : ℝ≥0)
    (hf : ∀ᵐ x ∂hausdorff n X, |f x|≤A) {T : ℝ} (hT : 0<T) :
    ∀ᵐ x ∂hausdorff n X, 0<heatAt (hausdorff n X) hX.quadratic T f x →
      T*Real.exp (-2*|K| * T)*
        (SobolevSpace.minimalSlope (hausdorff n X) hX.quadratic
          (heatSobolev (hausdorff n X) hX.quadratic T hT f) x)^2 ≤
      (heatAt (hausdorff n X) hX.quadratic T f x)^2*
        (Real.log A-Real.log (heatAt (hausdorff n X) hX.quadratic T f x)) := by
  let μ := hausdorff n X
  let Q := hX.quadratic
  let e : ℕ → ℝ := fun i => 1/(i+1:ℝ)
  have he (i : ℕ) : 0<e i := by dsimp [e]; positivity
  have he0 : Tendsto e atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hb := ae_all_iff.mpr (fun i : ℕ => hX.heat_hamilton_regularized hn p f hf0 A hf hT (he i))
  filter_upwards [hb,heatAt_abs_le_const μ Q T A f hf,
    localGamma_self μ Q (heatSobolev μ Q T hT f)] with x hx ha hg
  intro hp
  have hA : 0<(A:ℝ) := hp.trans_le ((le_abs_self _).trans ha)
  have hden := he0.add_const (heatAt μ Q T f x)
  have hnum := he0.add_const (A:ℝ)
  simp only [zero_add] at hden hnum
  have hl := ((Real.continuousAt_log hA.ne').tendsto.comp hnum).sub
    ((Real.continuousAt_log hp.ne').tendsto.comp hden)
  have hlim := (hden.pow 2).mul hl
  dsimp only [μ,Q] at hg
  apply ge_of_tendsto (x:=atTop) hlim
  exact .of_forall fun i => by simpa only [Function.comp_apply,hg] using hx i

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
