import OAI.Geometry.RCD.Coordinates.CoordinateHeatInput
import OAI.Geometry.RCD.Heat.AnnularHeatAverages
import OAI.Geometry.RCD.Sobolev.BoundedPoissonLipschitz

namespace OAI

/-! # Interior spatial control from the localized weak Poisson equation -/

open Set Filter Metric MeasureTheory
open scoped NNReal ENNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- The annular source contributes linearly in time, while the bounded
source contributes its integrable square-root heat singularity. -/
theorem NoncollapsedRCD.localized_poisson_average_bound {K : ℝ} {n : ℕ}
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
      ∀ (x y : X) (r : ℝ), 0 < r →
      (closedBall x r ⊆ closedBall p (R/8)) →
      (closedBall y r ⊆ closedBall p (R/8)) →
      |(⨍ z in closedBall x r, SobolevSpace.toLp _ _ u z ∂hausdorff n X)-
        (⨍ z in closedBall y r, SobolevSpace.toLp _ _ u z ∂hausdorff n X)| ≤
      (Real.exp (|K| *T)*(C/Real.sqrt T+2*D*Real.sqrt T)+
        (J/(R*(hausdorff n X).real (ball p R))*(∫ z, |e z| ∂hausdorff n X))*T)*
          (dist x y+2*r) := by
  obtain ⟨J,hJ,hann⟩ := hX.annular_heat_average_difference hn hk hg
  refine ⟨J,hJ,?_⟩
  intro p R T hR hcurv hT hT1 hTR u b e hd C D hu hb hei hes x y r hr hx hy
  let μ := hausdorff n X
  let U := SobolevSpace.toLp μ hX.quadratic u
  let A := closedBall x r
  let B := closedBall y r
  let E := J/(R*μ.real (ball p R))*(∫ z, |e z| ∂μ)
  have hAt : μ A ≠ ∞ := (hX.finiteOnBounded _ isBounded_closedBall).ne
  have hBt : μ B ≠ ∞ := (hX.finiteOnBounded _ isBounded_closedBall).ne
  let F (t : ℝ) := (⨍ z in A, heatAt μ hX.quadratic t U z ∂μ)-
    (⨍ z in B, heatAt μ hX.quadratic t U z ∂μ)
  let Q (t : ℝ) := (⨍ z in A, heatAt μ hX.quadratic t (b+e) z ∂μ)-
    (⨍ z in B, heatAt μ hX.quadratic t (b+e) z ∂μ)
  have hc : Continuous F := (heat_setAverage_continuous μ hX.quadratic A
    measurableSet_closedBall hAt U).sub
    (heat_setAverage_continuous μ hX.quadratic B measurableSet_closedBall hBt U)
  have hder (t : ℝ) (ht : t ∈ Ioo 0 T) : HasDerivAt F (Q t) t :=
    (heat_weakLaplacian_average_hasDerivAt μ hX.quadratic u (b+e) hd A
      measurableSet_closedBall hAt ht.1).sub
      (heat_weakLaplacian_average_hasDerivAt μ hX.quadratic u (b+e) hd B
        measurableSet_closedBall hBt ht.1)
  have hbound (t : ℝ) (ht : t ∈ Ioo 0 T) :
      |Q t| ≤ (D*Real.exp (|K| *T)*(dist x y+2*r))/Real.sqrt t+E*(dist x y+2*r) := by
    have hbb := hX.heat_average_difference_le K n hn b D hb t T ht.1 ht.2.le x y r hr
    have hee := hann p R t hR hcurv ht.1 (ht.2.le.trans hT1) (ht.2.le.trans hTR)
      e hei hes x y r hr hx hy
    have hsplit : Q t =
        ((⨍ z in A, heatAt μ hX.quadratic t b z ∂μ)-
          (⨍ z in B, heatAt μ hX.quadratic t b z ∂μ))+
        ((⨍ z in A, heatAt μ hX.quadratic t e z ∂μ)-
          (⨍ z in B, heatAt μ hX.quadratic t e z ∂μ)) := by
      dsimp only [Q]
      rw [heat_setAverage_add μ hX.quadratic A measurableSet_closedBall hAt,
        heat_setAverage_add μ hX.quadratic B measurableSet_closedBall hBt]
      ring
    rw [hsplit]
    refine (abs_add_le _ _).trans ?_
    convert add_le_add hbb hee using 1
    ring
  have hvar := abs_sub_le_of_sqrt_derivative_bound_add hT hc.continuousOn hder hbound
  have hFT := hX.heat_average_difference_le K n hn U C hu T T hT le_rfl x y r hr
  have hzero : F 0 = (⨍ z in A, U z ∂μ)-(⨍ z in B, U z ∂μ) := by
    simp only [F,heatAt_zero,one_apply_eq_self]
  rw [← hzero]
  change |F 0| ≤ (Real.exp (|K| *T)*(C/Real.sqrt T+2*D*Real.sqrt T)+E*T)*(dist x y+2*r)
  calc
    |F 0| = |F T-(F T-F 0)| := by congr 1; ring
    _ ≤ |F T|+|F T-F 0| := abs_sub _ _
    _ ≤ (C*Real.exp (|K| *T)/Real.sqrt T)*(dist x y+2*r)+
        (2*(D*Real.exp (|K| *T)*(dist x y+2*r))*Real.sqrt T+E*(dist x y+2*r)*T) :=
      add_le_add hFT hvar
    _ = _ := by ring

end RegularPointCoordinates

end

end OAI
