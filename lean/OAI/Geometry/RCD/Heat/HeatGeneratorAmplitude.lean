import OAI.Geometry.RCD.Heat.KernelHeatSourceUpper
import OAI.Geometry.RCD.Heat.CanonicalKernelConstruction
import OAI.Geometry.RCD.Heat.BoundedLpParts
import OAI.Geometry.RCD.Heat.HeatGeneratorSecondDerivative

namespace OAI

/-! # Uniform amplitudes for the first two actual heat generators

Positive and negative parts reduce the signed estimate to the conservative
complement bound. A second positive-time split controls the second source.
-/

open Set Filter MeasureTheory TopologicalSpace
open scoped NNReal ENNReal
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  (hn : 2 ≤ n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

include hn p in
theorem heatGeneratorAt_amplitude (hK : K ≤ 0)
    (f : Lp ℝ 2 (hausdorff n X)) (A : ℝ≥0)
    (hf : ∀ᵐ x ∂hausdorff n X, |f x| ≤ A) {t : ℝ} (ht : 0 < t) :
    ∀ᵐ x ∂hausdorff n X, |heatGeneratorAt (hausdorff n X) hX.quadratic t f x| ≤
      (2*(n:ℝ)*(|K|+1/t))*(A:ℝ) := by
  let μ := hausdorff n X
  let Q := hX.quadratic
  let hk := hX.canonicalHeatKernel_isContinuousHeatKernel hn p
  obtain ⟨hp0,hn0,hpA,hnA,he⟩ := bounded_lp_parts μ f A hf
  have hp := hX.kernelHeat_source_abs_bound_nonneg hn p hK hk (Lp.posPart f) hp0 A hpA ht
  have hn := hX.kernelHeat_source_abs_bound_nonneg hn p hK hk (Lp.negPart f) hn0 A hnA ht
  filter_upwards [kernelHeatGeneratorSource_represents μ Q hk ht (Lp.posPart f),
    kernelHeatGeneratorSource_represents μ Q hk ht (Lp.negPart f),
    Lp.coeFn_sub (heatGeneratorAt μ Q t (Lp.posPart f)) (heatGeneratorAt μ Q t (Lp.negPart f))]
      with x hpr hnr hs
  have hpa := hp x
  have hna := hn x
  rw [hpr,Pi.neg_apply,abs_neg] at hpa
  rw [hnr,Pi.neg_apply,abs_neg] at hna
  rw [he,map_sub,hs]
  dsimp only [Pi.sub_apply]
  calc
    _ ≤ |heatGeneratorAt μ Q t (Lp.posPart f) x|+|heatGeneratorAt μ Q t (Lp.negPart f) x| :=
      abs_sub _ _
    _ ≤ (n:ℝ)*(|K|+1/t)*(A:ℝ)+(n:ℝ)*(|K|+1/t)*(A:ℝ) := add_le_add hpa hna
    _ = _ := by ring

include hn p in
theorem heatSecondGeneratorAt_amplitude (hK : K ≤ 0)
    (f : Lp ℝ 2 (hausdorff n X)) (A : ℝ≥0)
    (hf : ∀ᵐ x ∂hausdorff n X, |f x| ≤ A) {t : ℝ} (ht : 0 < t) :
    ∀ᵐ x ∂hausdorff n X, |heatSecondGeneratorAt (hausdorff n X) hX.quadratic t f x| ≤
      (2*(n:ℝ)*(|K|+1/(t/2)))^2*(A:ℝ) := by
  let C : ℝ≥0 := ⟨2*(n:ℝ)*(|K|+1/(t/2)),by positivity⟩
  have hfirst : ∀ᵐ x ∂hausdorff n X,
      |heatGeneratorAt (hausdorff n X) hX.quadratic (t/2) f x| ≤ C*A := by
    change ∀ᵐ x ∂hausdorff n X,
      |heatGeneratorAt (hausdorff n X) hX.quadratic (t/2) f x| ≤
        (2*(n:ℝ)*(|K|+1/(t/2)))*(A:ℝ)
    exact hX.heatGeneratorAt_amplitude hn p hK f A hf (half_pos ht)
  have hsecond := hX.heatGeneratorAt_amplitude hn p hK
    (heatGeneratorAt (hausdorff n X) hX.quadratic (t/2) f) (C*A) hfirst (half_pos ht)
  filter_upwards [hsecond] with x hx
  change |heatSecondGeneratorAt (hausdorff n X) hX.quadratic t f x| ≤
    (2*(n:ℝ)*(|K|+1/(t/2)))*((2*(n:ℝ)*(|K|+1/(t/2)))*(A:ℝ)) at hx
  exact hx.trans_eq (by ring)

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
