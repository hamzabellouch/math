import OAI.Geometry.RCD.Heat.HeatGeneratorAmplitude
import OAI.Geometry.RCD.Heat.BoundedHeatSobolevData

namespace OAI

/-! # Bounded regular heat data with nonpositive curvature -/

open Set Filter MeasureTheory
open scoped NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.heat_regular_bounded_source_curved {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2 ≤ n) (hK : K≤0) (p : X)
    (f : Lp ℝ 2 (hausdorff n X)) (A : ℝ≥0)
    (hA : ∀ᵐ x ∂hausdorff n X, |f x| ≤ A) {t : ℝ} (ht : 0 < t) :
    let μ := hausdorff n X
    let Q := hX.quadratic
    let w := heatSobolev μ Q t ht f
    let d := heatSobolevMap μ Q (t/2) (half_pos ht) (-heatGeneratorAt μ Q (t-t/2) f)
    ∃ (W : X → ℝ) (L B : ℝ≥0),
      LipschitzWith L W ∧
      (SobolevSpace.toLp μ Q w =ᵐ[μ] W) ∧
      (∀ᵐ x ∂μ, |SobolevSpace.toLp μ Q w x| ≤ A) ∧
      IsWeakLaplacian μ Q w (SobolevSpace.toLp μ Q d) ∧
      (∀ᵐ x ∂μ, |SobolevSpace.toLp μ Q d x| ≤ B) := by
  let := hX.separable
  let := locallyFinite_of_finiteOnBounded (hausdorff n X) hX.finiteOnBounded
  intro μ Q w d
  let hk := hX.canonicalHeatKernel_isContinuousHeatKernel hn p
  obtain ⟨hLip,-⟩ := hX.kernelHeat_bounded_regularity hn p hk f A hA t ht
  have hwr : SobolevSpace.toLp μ Q w =ᵐ[μ] kernelHeat μ Q hk t f := by
    simpa only [w,heatSobolev_toLp] using (kernelHeat_represents_L2 μ Q hk ht f).symm
  let B : ℝ≥0 := ⟨(2*(n:ℝ)*(|K|+1/t))*(A:ℝ),by positivity⟩
  refine ⟨kernelHeat μ Q hk t f,_,B,hLip,hwr,
    (hX.bounded_heat_sobolev_data hn p f A hA ht).1,
    heatTail_weak_laplacian μ Q t ht f,?_⟩
  have hd : SobolevSpace.toLp μ Q d= -heatGeneratorAt μ Q t f :=
    heatTail_deriv_toLp μ Q (t/2) (half_pos ht) f t (by linarith)
  rw [hd]
  filter_upwards [hX.heatGeneratorAt_amplitude hn p hK f A hA ht,
    Lp.coeFn_neg (heatGeneratorAt μ Q t f)] with x hx he
  rw [he]
  change |-(heatGeneratorAt μ Q t f x)| ≤ (2*(n:ℝ)*(|K|+1/t))*(A:ℝ)
  simpa only [abs_neg] using hx

end RegularPointCoordinates

end

end OAI
