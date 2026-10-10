import OAI.Geometry.RCD.Coordinates.CoordinateHeatInput
import OAI.Geometry.RCD.Sobolev.LocalizedPoissonAverages
import OAI.Geometry.RCD.Sobolev.LocalAverageRepresentative

namespace OAI

/-! # Lipschitz representatives from bounded and annular Poisson data -/

open Set Filter Metric MeasureTheory TopologicalSpace
open scoped NNReal ENNReal Topology

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.localized_poisson_representative {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2 ≤ n)
    {ker : ℝ → X → X → ℝ}
    (hk : IsContinuousHeatKernel (hausdorff n X) hX.quadratic ker)
    (hg : HasCoordinateHeatBounds (hausdorff n X) ker) :
    ∃ J : ℝ, 0 < J ∧ ∀ (p : X) (R T : ℝ), 0 < R → -1 ≤ K*R^2 →
      0 < T → T ≤ 1 → T ≤ R^2 →
      ∀ (u : SobolevSpace (hausdorff n X) hX.quadratic)
        (b e : Lp ℝ 2 (hausdorff n X)),
      IsWeakLaplacian (hausdorff n X) hX.quadratic u (b+e) →
      ∀ (C D : ℝ≥0),
      (∀ᵐ x ∂hausdorff n X, |SobolevSpace.toLp _ _ u x| ≤ C) →
      (∀ᵐ x ∂hausdorff n X, |b x| ≤ D) →
      Integrable e (hausdorff n X) →
      (∀ᵐ z ∂hausdorff n X, e z ≠ 0 → R ≤ dist z p ∧ dist z p ≤ 2*R) →
      ∃ v : X → ℝ,
        LipschitzWith (Real.exp (|K| *T)*(C/Real.sqrt T+2*D*Real.sqrt T)+
          (J/(R*(hausdorff n X).real (ball p R))*(∫ z, |e z| ∂hausdorff n X))*T).toNNReal v ∧
        SobolevSpace.toLp _ _ u =ᵐ[(hausdorff n X).restrict (ball p (R/8))] v := by
  obtain ⟨J,hJ,havg⟩ := hX.localized_poisson_average_bound hn hk hg
  refine ⟨J,hJ,?_⟩
  intro p R T hR hcurv hT hT1 hTR u b e hd C D hu hb hei hes
  let : SeparableSpace X := hX.separable
  let μ := hausdorff n X
  let : IsLocallyFiniteMeasure μ := locallyFinite_of_finiteOnBounded μ hX.finiteOnBounded
  let : IsUnifLocDoublingMeasure μ := hX.locDoubling K n hn
  apply exists_lipschitz_of_local_average_bound _
    ((Lp.memLp (SobolevSpace.toLp μ hX.quadratic u)).locallyIntegrable (by norm_num))
    measurableSet_ball
  intro x hx y hy
  have hx' : dist x p < R/8 := hx
  have hy' : dist y p < R/8 := hy
  have hδ : 0 < min (R/8-dist x p) (R/8-dist y p) := lt_min (by linarith) (by linarith)
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds hδ).filter_mono nhdsWithin_le_nhds] with r hr hrδ
  rw [Real.coe_toNNReal _ (by positivity)]
  apply havg p R T hR hcurv hT hT1 hTR u b e hd C D hu hb hei hes x y r hr
  · intro z hz
    have hz' : dist z x ≤ r := hz
    have hsmall := hrδ.trans_le (min_le_left _ _)
    have htri := dist_triangle z x p
    change dist z p ≤ R/8
    linarith
  · intro z hz
    have hz' : dist z y ≤ r := hz
    have hsmall := hrδ.trans_le (min_le_right _ _)
    have htri := dist_triangle z y p
    change dist z p ≤ R/8
    linarith

end RegularPointCoordinates

end

end OAI
