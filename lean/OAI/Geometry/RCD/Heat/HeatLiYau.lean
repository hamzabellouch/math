import OAI.Geometry.RCD.Coordinates.HeatLiYauRegularized

namespace OAI

/-! # The parameter-two Li--Yau bound for the actual heat generator

A countable positive regularization gives one full-measure set. The
polynomial estimate also holds where the heat value vanishes.
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

theorem heat_liYau (hK : K≤0)
    (f : Lp ℝ 2 (hausdorff n X)) (hf0 : 0≤f) (A : ℝ≥0)
    (hf : ∀ᵐ x ∂hausdorff n X, |f x|≤A) {T : ℝ} (hT : 0<T) :
    ∀ᵐ x ∂hausdorff n X,
      (SobolevSpace.minimalSlope (hausdorff n X) hX.quadratic
        (heatSobolev (hausdorff n X) hX.quadratic T hT f) x)^2 ≤
      2*heatAt (hausdorff n X) hX.quadratic T f x*
        (-heatGeneratorAt (hausdorff n X) hX.quadratic T f) x+
      (2*(n:ℝ)*(|K|+1/T))*(heatAt (hausdorff n X) hX.quadratic T f x)^2 := by
  let μ := hausdorff n X
  let Q := hX.quadratic
  let e : ℕ → ℝ := fun i => 1/(i+1:ℝ)
  have he (i : ℕ) : 0<e i := by dsimp only [e]; positivity
  have he0 : Tendsto e atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hb := ae_all_iff.mpr (fun i : ℕ => hX.heat_liYau_regularized hn p hK f hf0 A hf hT (he i))
  filter_upwards [hb,localGamma_self μ Q (heatSobolev μ Q T hT f)] with x hx hg
  dsimp only [μ,Q] at hg
  have hv := he0.add_const (heatAt μ Q T f x)
  simp only [zero_add] at hv
  have hlim := ((hv.const_mul 2).mul
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (-heatGeneratorAt μ Q T f) x) atTop
      (𝓝 ((-heatGeneratorAt μ Q T f) x)))).add
    ((hv.pow 2).const_mul (2*(n:ℝ)*(|K|+1/T)))
  apply ge_of_tendsto (x:=atTop) hlim
  exact .of_forall fun i => by simpa only [hg] using hx i

theorem heat_source_lower (hK : K≤0)
    (f : Lp ℝ 2 (hausdorff n X)) (hf0 : 0≤f) (A : ℝ≥0)
    (hf : ∀ᵐ x ∂hausdorff n X, |f x|≤A) {T : ℝ} (hT : 0<T) :
    ∀ᵐ x ∂hausdorff n X,
      -(n:ℝ)*(|K|+1/T)*heatAt (hausdorff n X) hX.quadratic T f x ≤
        (-heatGeneratorAt (hausdorff n X) hX.quadratic T f) x := by
  let μ := hausdorff n X
  let Q := hX.quadratic
  let e : ℕ → ℝ := fun i => 1/(i+1:ℝ)
  have he (i : ℕ) : 0<e i := by dsimp only [e]; positivity
  have he0 : Tendsto e atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hb := ae_all_iff.mpr (fun i : ℕ => hX.heat_liYau_regularized hn p hK f hf0 A hf hT (he i))
  filter_upwards [hb,(Lp.coeFn_nonneg _).mpr (heatAt_nonneg μ Q T f hf0),
    localGamma_self μ Q (heatSobolev μ Q T hT f)] with x hx hv hg
  dsimp only [μ,Q] at hg
  have hbound (i : ℕ) : -(n:ℝ)*(|K|+1/T)*(e i+heatAt μ Q T f x)≤
      (-heatGeneratorAt μ Q T f) x := by
    have hp : 0<2*(e i+heatAt μ Q T f x) :=
      mul_pos (by norm_num) (add_pos_of_pos_of_nonneg (he i) hv)
    have hh := hx i
    rw [hg] at hh
    have hz : 0≤2*(e i+heatAt μ Q T f x)*
        ((-heatGeneratorAt μ Q T f) x+(n:ℝ)*(|K|+1/T)*(e i+heatAt μ Q T f x)) := by
      nlinarith only [hh,sq_nonneg (SobolevSpace.minimalSlope μ Q (heatSobolev μ Q T hT f) x)]
    have hl := nonneg_of_mul_nonneg_right hz hp
    linarith only [hl]
  have hlim := (he0.add_const (heatAt μ Q T f x)).const_mul (-(n:ℝ)*(|K|+1/T))
  simp only [zero_add] at hlim
  exact le_of_tendsto hlim (.of_forall hbound)

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
