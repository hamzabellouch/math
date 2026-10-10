import OAI.Geometry.RCD.Heat.HeatCompactWeightedBochner

namespace OAI

/-! # Dimensional heat estimate on the actual Sobolev space

Compact recovery of the minimal relaxed gradient and continuity of the
positive-time heat generator pass both nonnegative terms to the limit.
-/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology NNReal ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.heat_weighted_generator_bochner
    (K : ℝ) (n : ℕ) [(hausdorff n X).Regular] (hn : 2 ≤ n)
    (hX : NoncollapsedRCD K n X) (hK : K ≤ 0) {N : ℝ} (hN : (n:ℝ) ≤ N)
    {ker : ℝ → X → X → ℝ} (hk : IsContinuousHeatKernel (hausdorff n X) hX.quadratic ker)
    (p : X) (f : SobolevSpace (hausdorff n X) hX.quadratic)
    (w : Lp ℝ 2 (hausdorff n X)) (hw : 0 ≤ w) (C : ℝ≥0)
    (hwC : ∀ᵐ x ∂hausdorff n X, |w x| ≤ C) :
    letI : ProperSpace X := hX.proper K n hn
    letI : SeparableSpace X := hX.separable
    letI : IsLocallyFiniteMeasure (hausdorff n X) := locallyFinite_of_finiteOnBounded _ hX.finiteOnBounded
    ∀ {t : ℝ} (ht : 0 < t),
      (∫ x, w x*(SobolevSpace.minimalSlope (hausdorff n X) hX.quadratic
        (heatSobolev (hausdorff n X) hX.quadratic t ht
          (SobolevSpace.toLp (hausdorff n X) hX.quadratic f)) x)^2 ∂hausdorff n X)+
      (2*t/N)*(∫ x, w x*((-heatGeneratorAt (hausdorff n X) hX.quadratic t
        (SobolevSpace.toLp (hausdorff n X) hX.quadratic f)) x)^2 ∂hausdorff n X) ≤
      Real.exp (-2*K*t)*(∫ x, heatAt (hausdorff n X) hX.quadratic t w x*
        (SobolevSpace.minimalSlope (hausdorff n X) hX.quadratic f x)^2 ∂hausdorff n X) := by
  let : ProperSpace X := hX.proper K n hn
  let : SeparableSpace X := hX.separable
  let μ := hausdorff n X
  let : IsLocallyFiniteMeasure μ := locallyFinite_of_finiteOnBounded μ hX.finiteOnBounded
  intro t ht
  obtain ⟨us,gs,Gs,hl,hs,ha,hm,hu,hG⟩ :=
    (SobolevSpace.minimalSlope_isRelaxed μ hX.quadratic f).compact_recovery μ p
  have hab (i : ℕ) := hX.heat_compact_weighted_generator_bochner K n hn hK hN hk
    (hl i).choose_spec (hs i) p (us i) (Gs i) w (ha i).symm (hm i) hw C hwC ht
  have hsf : Tendsto (fun i => heatSobolev μ hX.quadratic t ht (us i)) atTop
      (𝓝 (heatSobolev μ hX.quadratic t ht (SobolevSpace.toLp μ hX.quadratic f))) :=
    ((heatSobolevMap μ hX.quadratic t ht).continuous.tendsto _).comp hu
  have hsl := ((SobolevSpace.minimalSlope_lipschitz μ hX.quadratic).continuous.tendsto _).comp hsf
  have hwb : ∀ᵐ x ∂μ, ‖w x‖ ≤ (C:ℝ) := by simpa only [Real.norm_eq_abs] using hwC
  have hPwb : ∀ᵐ x ∂μ, ‖heatAt μ hX.quadratic t w x‖ ≤ (C:ℝ) := by
    simpa only [Real.norm_eq_abs] using heatAt_abs_le_const μ hX.quadratic t C w hwC
  have hleft := ((lp_weighted_square_continuous μ (Lp.aestronglyMeasurable w) hwb).tendsto _).comp hsl
  have hdL := (((heatGeneratorAt μ hX.quadratic t).continuous.neg).tendsto
    (SobolevSpace.toLp μ hX.quadratic f)).comp hu
  have hdleft := ((lp_weighted_square_continuous μ (Lp.aestronglyMeasurable w) hwb).tendsto _).comp hdL
  have hright := (((lp_weighted_square_continuous μ (Lp.aestronglyMeasurable
    (heatAt μ hX.quadratic t w)) hPwb).tendsto _).comp hG).const_mul (Real.exp (-2*K*t))
  exact le_of_tendsto_of_tendsto (hleft.add (hdleft.const_mul (2*t/N))) hright (Eventually.of_forall hab)


end RegularPointCoordinates

end

end OAI
