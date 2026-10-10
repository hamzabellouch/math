import OAI.Geometry.RCD.Heat.CanonicalHeatTimeRatio

namespace OAI

/-! # A backward time comparison at a fixed spatial point

The earlier ball has smaller volume. The existing Gaussian bounds therefore
give this comparison without an additional volume-ratio input.
-/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped NNReal ENNReal Topology
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  (hn : 2≤n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

theorem canonicalHeatKernel_backward_time_ratio :
    ∃ A D : ℝ, 0<A ∧ 0<D ∧ ∀ (s t : ℝ), 0<s → s≤t → t≤1 → ∀ x y : X,
      hX.canonicalHeatKernel hn p t x y ≤ A*Real.exp (D*(dist x y)^2/s)*
        hX.canonicalHeatKernel hn p s x y := by
  obtain ⟨C,B,hC,hB,hupper⟩ := hX.canonicalHeatKernel_upper_five hn p
  obtain ⟨c,D,hc,hD,hlower⟩ := hX.canonicalHeatKernel_rough_gaussian_lower hn p
  let A := C/c*Real.exp B
  have hA : 0<A := by dsimp only [A]; positivity
  refine ⟨A,D,hA,hD,?_⟩
  intro s t hs hst ht1 x y
  have ht : 0<t := hs.trans_le hst
  let Vs := (hausdorff n X).real (ball y (Real.sqrt s))
  let Vt := (hausdorff n X).real (ball y (Real.sqrt t))
  have hVs : 0<Vs := ENNReal.toReal_pos
    (hX.fullSupport _ _ (Real.sqrt_pos.mpr hs)).ne' (hX.finiteOnBounded _ isBounded_ball).ne
  have hvol : Vs≤Vt := measureReal_mono
    (ball_subset_ball (Real.sqrt_le_sqrt hst)) (hX.finiteOnBounded _ isBounded_ball).ne
  have hu : hX.canonicalHeatKernel hn p t x y≤C/Vs*Real.exp B := by
    apply (hupper t ht x y).trans
    apply mul_le_mul (div_le_div_of_nonneg_left hC.le hVs hvol) _ (Real.exp_pos _).le
      (div_nonneg hC.le hVs.le)
    apply Real.exp_le_exp.mpr
    have hdist : 0≤(dist x y)^2/(5*t) := by positivity
    have hBt : B*t≤B := mul_le_of_le_one_right hB ht1
    rw [neg_div]
    linarith
  have hl := hlower s hs (hst.trans ht1) x y
  let q := D*(dist x y)^2/s
  have hq : -q= -D*(dist x y)^2/s := by dsimp only [q]; ring
  rw [←hq] at hl
  calc
    _ ≤ C/Vs*Real.exp B := hu
    _ = (A*Real.exp q)*(c/Vs*Real.exp (-q)) := by
      dsimp only [A]
      rw [Real.exp_neg]
      field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hl (mul_nonneg hA.le (Real.exp_pos q).le)

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
