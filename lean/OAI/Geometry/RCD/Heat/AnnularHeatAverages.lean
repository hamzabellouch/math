import OAI.Geometry.RCD.Coordinates.CoordinateHeatInput
import OAI.Geometry.RCD.Heat.AnnularHeatLipschitz
import OAI.Geometry.RCD.Sobolev.LocalLipschitzAverages

namespace OAI

/-! # Interior averages of heat evolutions of annular sources -/

open Set Metric MeasureTheory
open scoped NNReal ENNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.annular_heat_average_difference {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2 ≤ n)
    {ker : ℝ → X → X → ℝ}
    (hk : IsContinuousHeatKernel (hausdorff n X) hX.quadratic ker)
    (hg : HasCoordinateHeatBounds (hausdorff n X) ker) :
    ∃ J : ℝ, 0 < J ∧ ∀ (p : X) (R t : ℝ), 0 < R → -1 ≤ K*R^2 →
      0 < t → t ≤ 1 → t ≤ R^2 →
      ∀ q : Lp ℝ 2 (hausdorff n X), Integrable q (hausdorff n X) →
      (∀ᵐ z ∂hausdorff n X, q z ≠ 0 → R ≤ dist z p ∧ dist z p ≤ 2*R) →
      ∀ (x y : X) (r : ℝ), 0 < r →
      (closedBall x r ⊆ closedBall p (R/8)) →
      (closedBall y r ⊆ closedBall p (R/8)) →
      |(⨍ z in closedBall x r, heatAt (hausdorff n X) hX.quadratic t q z ∂hausdorff n X)-
        (⨍ z in closedBall y r, heatAt (hausdorff n X) hX.quadratic t q z ∂hausdorff n X)| ≤
        (J/(R*(hausdorff n X).real (ball p R))*(∫ z, |q z| ∂hausdorff n X))*
          (dist x y+2*r) := by
  obtain ⟨J,hJ,he⟩ := hX.annular_heat_difference hn hk hg
  refine ⟨J,hJ,?_⟩
  intro p R t hR hcurv ht ht1 htR q hqi hqs x y r hr hx hy
  let μ := hausdorff n X
  let : IsLocallyFiniteMeasure μ := locallyFinite_of_finiteOnBounded μ hX.finiteOnBounded
  let L : ℝ≥0 := ⟨J/(R*μ.real (ball p R))*(∫ z, |q z| ∂μ),by positivity⟩
  have hLip : LipschitzOnWith L (kernelHeat μ hX.quadratic hk t q) (closedBall p (R/8)) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro a ha b hb
    simpa only [Real.dist_eq,L,NNReal.coe_mk,μ] using! he p R t hR hcurv ht ht1 htR q hqi hqs a b ha hb
  have hrep := kernelHeat_represents μ hX.quadratic hk ht q hqi
  have havg (a : X) :
      (⨍ z in closedBall a r, heatAt μ hX.quadratic t q z ∂μ) =
        ⨍ z in closedBall a r, kernelHeat μ hX.quadratic hk t q z ∂μ :=
    average_congr (ae_restrict_of_ae hrep.symm)
  rw [havg x,havg y]
  exact local_lipschitz_ball_average_bound μ hLip x y hr.le
    ((hX.fullSupport x r hr).trans_le (measure_mono ball_subset_closedBall)).ne'
    ((hX.fullSupport y r hr).trans_le (measure_mono ball_subset_closedBall)).ne' hx hy

end RegularPointCoordinates

end

end OAI
