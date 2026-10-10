import OAI.Geometry.RCD.Heat.HeatBochnerForm
import OAI.Geometry.RCD.Sobolev.BochnerEnergyAbsorption

namespace OAI

/-! # A quantitative energy bound for heat energy densities

After absorbing the mixed term, the estimate uses the L² norm of the
Laplacian, with no derivatives or amplitude bound on that Laplacian.
-/

open Set Filter MeasureTheory
open scoped NNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.heat_gamma_energy_estimate {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2 ≤ n) (p : X)
    (f : Lp ℝ 2 (hausdorff n X)) {t : ℝ} (ht : 0 < t)
    (G : SobolevSpace (hausdorff n X) hX.quadratic) (C L : ℝ≥0)
    (hG : SobolevSpace.toLp (hausdorff n X) hX.quadratic G =ᵐ[hausdorff n X]
      fun x => (SobolevSpace.minimalSlope (hausdorff n X) hX.quadratic
        (heatSobolev (hausdorff n X) hX.quadratic t ht f) x) ^ 2)
    (hGb : ∀ᵐ x ∂hausdorff n X, |SobolevSpace.toLp (hausdorff n X) hX.quadratic G x| ≤ C)
    (hF : ∀ᵐ x ∂hausdorff n X, SobolevSpace.minimalSlope (hausdorff n X) hX.quadratic
      (heatSobolev (hausdorff n X) hX.quadratic t ht f) x ≤ L) :
    let D := heatSobolevMap (hausdorff n X) hX.quadratic (t / 2) (half_pos ht)
      (-heatGeneratorAt (hausdorff n X) hX.quadratic (t - t / 2) f)
    energyForm (hausdorff n X) hX.quadratic G G ≤
      4 * |K| * ‖SobolevSpace.toLp (hausdorff n X) hX.quadratic G‖ ^ 2 +
        4 * ((C : ℝ) + (L : ℝ) ^ 2) * ‖SobolevSpace.toLp (hausdorff n X) hX.quadratic D‖ ^ 2 := by
  let := hX.separable
  let := locallyFinite_of_finiteOnBounded (hausdorff n X) hX.finiteOnBounded
  let μ := hausdorff n X
  let F := heatSobolev μ hX.quadratic t ht f
  let D := heatSobolevMap μ hX.quadratic (t / 2) (half_pos ht)
    (-heatGeneratorAt μ hX.quadratic (t - t / 2) f)
  have hG0 : 0 ≤ SobolevSpace.toLp μ hX.quadratic G := by
    apply (Lp.coeFn_nonneg _).mp
    filter_upwards [hG] with x hx
    rw [hx]
    positivity
  have hb := hX.heat_bochner_sobolev_test hn p f ht G L hG hF G C hG0 hGb
  rw [real_inner_self_eq_norm_sq] at hb
  exact bochner_energy_absorption μ hX.quadratic F D G C L K hGb hF
    (heatTail_weak_laplacian μ hX.quadratic t ht f) hb

end RegularPointCoordinates

end

end OAI
