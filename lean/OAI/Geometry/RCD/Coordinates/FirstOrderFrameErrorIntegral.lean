import OAI.Geometry.RCD.Coordinates.FrameEnergyError

namespace OAI

/-! # Quantitative frame-energy error for the actual first-order splitting -/

open Set Filter MeasureTheory Metric
open scoped NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.first_order_frame_error_integral {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular]
    (hn : 2≤n) (hK : K≤0) (p : X) {R b ε : ℝ}
    (hR : 0<R) (hb : 4*R<b) (hε : 0≤ε) (hε1 : ε≤1)
    (u : Fin n → SobolevSpace (hausdorff n X) hX.quadratic) (v : X → Euclidean n)
    (hs : FirstOrderSplittingOn (hausdorff n X) hX.quadratic p b ε u v)
    (g : compactLaplacianCore (hausdorff n X) hX.quadratic univ)
    (q : Lp ℝ 2 (hausdorff n X)) (hq : IsWeakLaplacian (hausdorff n X) hX.quadratic g.val q)
    (d : SobolevSpace (hausdorff n X) hX.quadratic) (A : ℝ≥0)
    (hd : ∀ᵐ x ∂hausdorff n X, |SobolevSpace.toLp (hausdorff n X) hX.quadratic d x|≤A)
    (hqr : q =ᵐ[(hausdorff n X).restrict (ball p (2*R))]
      SobolevSpace.toLp (hausdorff n X) hX.quadratic d)
    {L : ℝ} (hg : ∀ᵐ x ∂(hausdorff n X).restrict (ball p R),
      localGamma (hausdorff n X) hX.quadratic g.val g.val x≤L^2) :
    IntegrableOn (fun x => (frameEnergyError (hausdorff n X) hX.quadratic u g.val x)^2)
      (ball p R) (hausdorff n X) ∧
    (∫ x in ball p R, (frameEnergyError (hausdorff n X) hX.quadratic u g.val x)^2
      ∂hausdorff n X)≤frameDefectConstant n*L^4*(n:ℝ)^2*ε*
        (hausdorff n X).real (ball p b) := by
  let μ := hausdorff n X
  let hQ := hX.quadratic
  have hL (i : Fin n) : ∀ᵐ x ∂μ.restrict (ball p b), localGamma μ hQ (u i) (u i) x≤4 := by
    filter_upwards [hs.gradient i] with x hx
    nlinarith
  have hframe := hX.harmonic_global_frame_defect hn hK p u hR hb hs.harmonic hL
    g q hq d A hd hqr
  obtain ⟨hint,hintbound⟩ := frame_energy_error_sq_integral μ hQ u g.val
    (hX.finiteOnBounded _ isBounded_ball).ne hg hframe
  refine ⟨hint,hintbound.trans ?_⟩
  have hsub : ball p R⊆ball p b := ball_subset_ball (by linarith)
  have hpos : 0<μ.real (ball p b) := ENNReal.toReal_pos
    (hX.fullSupport p b (by linarith)).ne' (hX.finiteOnBounded _ isBounded_ball).ne
  have hdef := gramDefect_integral_bound μ hQ hpos
    (hX.finiteOnBounded _ isBounded_ball).ne hs
  have hsmall : (∫ x in ball p R, gramDefect μ hQ u x ∂μ)≤
      (n:ℝ)^2*ε*μ.real (ball p b) :=
    (setIntegral_mono_set (gramDefect_integrableOn μ hQ u (hX.finiteOnBounded _ isBounded_ball).ne)
      (Eventually.of_forall (fun x => gramDefect_nonneg μ hQ u x))
      (Eventually.of_forall hsub)).trans hdef
  have hC : 0≤frameDefectConstant n := by unfold frameDefectConstant; positivity
  have hh := mul_le_mul_of_nonneg_left hsmall (mul_nonneg hC (by positivity : 0≤L^4))
  convert hh using 1
  ring

end RegularPointCoordinates

end

end OAI
