import OAI.Geometry.RCD.Heat.HeatPoissonAverage

namespace OAI

/-! # Bounded weak Laplacians give Lipschitz representatives

The proof pairs the actual heat flow with normalized ball indicators.
Its derivative is the heat flow of the weak Laplacian. Integrating the
inverse-square-root smoothing estimate and taking small-ball averages
produces the representative; no pointwise time derivative is assumed.
-/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped NNReal ENNReal Topology

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- Spatial differences of heat averages, with the outer time held fixed. -/
theorem NoncollapsedRCD.heat_average_difference_le
    (K : ℝ) (n : ℕ) (hn : 2 ≤ n) (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular]
    (f : Lp ℝ 2 (hausdorff n X)) (C : ℝ≥0)
    (hf : ∀ᵐ x ∂hausdorff n X, |f x| ≤ C)
    (t T : ℝ) (ht : 0 < t) (htT : t ≤ T) (x y : X) (r : ℝ) (hr : 0 < r) :
    |(⨍ z in closedBall x r, heatAt (hausdorff n X) hX.quadratic t f z ∂hausdorff n X)-
      (⨍ z in closedBall y r, heatAt (hausdorff n X) hX.quadratic t f z ∂hausdorff n X)| ≤
      (C*Real.exp (|K| *T)/Real.sqrt t)*(dist x y+2*r) := by
  let : ProperSpace X := hX.proper K n hn
  let : SeparableSpace X := hX.separable
  let μ := hausdorff n X
  let : IsLocallyFiniteMeasure μ := locallyFinite_of_finiteOnBounded μ hX.finiteOnBounded
  let L : ℝ≥0 := ⟨C*Real.exp (|K| *T)/Real.sqrt t,by positivity⟩
  exact hX.average_bound_of_gradient K n hn
    (SobolevSpace.minimalSlope_isRelaxed μ hX.quadratic (heatSobolev μ hX.quadratic t ht f))
    L (hX.heat_bounded_gradient_scale K n hn x f C hf t T ht htT) x y r hr

omit [ProperSpace X] in
/-- A global bounded Poisson solution has a quantitative Lipschitz
representative at every chosen positive time scale. -/
theorem NoncollapsedRCD.bounded_weakLaplacian_lipschitz
    (K : ℝ) (n : ℕ) (hn : 2 ≤ n) (hX : NoncollapsedRCD K n X)
    (u : SobolevSpace (hausdorff n X) hX.quadratic) (d : Lp ℝ 2 (hausdorff n X))
    (hd : IsWeakLaplacian (hausdorff n X) hX.quadratic u d)
    (C D : ℝ≥0) (hu : ∀ᵐ x ∂hausdorff n X, |SobolevSpace.toLp _ _ u x| ≤ C)
    (hdB : ∀ᵐ x ∂hausdorff n X, |d x| ≤ D) (T : ℝ) (hT : 0 < T) :
    ∃ v : X → ℝ,
      LipschitzWith ⟨Real.exp (|K| *T)*(C/Real.sqrt T+2*D*Real.sqrt T),by positivity⟩ v ∧
      SobolevSpace.toLp (hausdorff n X) hX.quadratic u =ᵐ[hausdorff n X] v := by
  let : ProperSpace X := hX.proper K n hn
  let : SeparableSpace X := hX.separable
  let μ := hausdorff n X
  let : IsLocallyFiniteMeasure μ := locallyFinite_of_finiteOnBounded μ hX.finiteOnBounded
  let : μ.Regular := inferInstance
  let : IsUnifLocDoublingMeasure μ := hX.locDoubling K n hn
  let U := SobolevSpace.toLp μ hX.quadratic u
  apply exists_lipschitz_of_average_bound U ((Lp.memLp U).locallyIntegrable (by norm_num))
  intro x y r hr
  let A := closedBall x r
  let B := closedBall y r
  have hAt : μ A ≠ ∞ := (hX.finiteOnBounded _ isBounded_closedBall).ne
  have hBt : μ B ≠ ∞ := (hX.finiteOnBounded _ isBounded_closedBall).ne
  let F (t : ℝ) := (⨍ z in A, heatAt μ hX.quadratic t U z ∂μ)-
    (⨍ z in B, heatAt μ hX.quadratic t U z ∂μ)
  let Q (t : ℝ) := (⨍ z in A, heatAt μ hX.quadratic t d z ∂μ)-
    (⨍ z in B, heatAt μ hX.quadratic t d z ∂μ)
  have hc : Continuous F := (heat_setAverage_continuous μ hX.quadratic A
    measurableSet_closedBall hAt U).sub
    (heat_setAverage_continuous μ hX.quadratic B measurableSet_closedBall hBt U)
  have hder (t : ℝ) (ht : t ∈ Ioo 0 T) : HasDerivAt F (Q t) t :=
    (heat_weakLaplacian_average_hasDerivAt μ hX.quadratic u d hd A
      measurableSet_closedBall hAt ht.1).sub
      (heat_weakLaplacian_average_hasDerivAt μ hX.quadratic u d hd B
        measurableSet_closedBall hBt ht.1)
  have hb (t : ℝ) (ht : t ∈ Ioo 0 T) :
      |Q t| ≤ (D*Real.exp (|K| *T)*(dist x y+2*r))/Real.sqrt t := by
    have hh := hX.heat_average_difference_le K n hn d D hdB t T ht.1 ht.2.le x y r hr
    change |Q t| ≤ _ at hh
    convert hh using 1; ring
  have hvar := abs_sub_le_of_sqrt_derivative_bound hT hc.continuousOn hder hb
  have hFT := hX.heat_average_difference_le K n hn U C hu T T hT le_rfl x y r hr
  have hzero : F 0 = (⨍ z in A, U z ∂μ)-(⨍ z in B, U z ∂μ) := by
    simp only [F,heatAt_zero,one_apply_eq_self]
  have htri : |F 0| ≤ |F T|+|F T-F 0| := by
    calc
      |F 0| = |F T-(F T-F 0)| := by congr 1; ring
      _ ≤ |F T|+|F T-F 0| := abs_sub _ _
  rw [← hzero]
  change |F 0| ≤ (Real.exp (|K| *T)*(C/Real.sqrt T+2*D*Real.sqrt T))*(dist x y+2*r)
  calc
    |F 0| ≤ |F T|+|F T-F 0| := htri
    _ ≤ (C*Real.exp (|K| *T)/Real.sqrt T)*(dist x y+2*r)+
        2*(D*Real.exp (|K| *T)*(dist x y+2*r))*Real.sqrt T := add_le_add hFT hvar
    _ = _ := by ring

end RegularPointCoordinates

end

end OAI
