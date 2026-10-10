import OAI.Geometry.RCD.Coordinates.RegularCoreWeakHessian
import OAI.Geometry.RCD.Sobolev.BochnerCurvatureDensity

namespace OAI

/-! # Shifted regular-core estimates for the prescribed full measure -/

open Set Filter Metric MeasureTheory
open scoped NNReal BoundedContinuousFunction

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- The scalar dimensional inequality controls the actual prescribed
Bochner measure, even when its curvature parameter is weakened. -/
theorem NoncollapsedRCD.regular_core_weak_hessian_on_measure {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2≤n)
    (hscalar : ScalarDimensionalBochner (hausdorff n X) hX.quadratic K n)
    {V : Set X} (f g : compactLaplacianCore (hausdorff n X) hX.quadratic V)
    (p : X) {R : ℝ} (hR : 0<R) {S : Set X} (hS : IsCompact S) (hsub : S ⊆ ball p R)
    (df : SobolevSpace (hausdorff n X) hX.quadratic)
    (qf : Lp ℝ 2 (hausdorff n X))
    (hqf : IsWeakLaplacian (hausdorff n X) hX.quadratic f.val qf)
    (A : ℝ≥0)
    (hdf : ∀ᵐ x ∂hausdorff n X, |SobolevSpace.toLp (hausdorff n X) hX.quadratic df x|≤A)
    (hsf : qf =ᵐ[(hausdorff n X).restrict (ball p R)]
      SobolevSpace.toLp (hausdorff n X) hX.quadratic df)
    {J : ℝ} (hJK : J≤K)
    (F₀ : SobolevSpace (hausdorff n X) hX.quadratic) (σ : Measure X) [IsFiniteMeasure σ]
    (hF₀ : SobolevSpace.toLp (hausdorff n X) hX.quadratic F₀
      =ᵐ[(hausdorff n X).restrict (ball p R)]
        localGamma (hausdorff n X) hX.quadratic f.val f.val)
    (hσ : IsMeasureLaplacianOn (hausdorff n X) hX.quadratic (ball p R) F₀
      (bochnerGramSource (hausdorff n X) hX.quadratic J f.val f.val df df σ.toSignedMeasure)) :
    ∃ (FG GG : SobolevSpace (hausdorff n X) hX.quadratic),
      SobolevSpace.toLp (hausdorff n X) hX.quadratic FG =ᵐ[hausdorff n X]
        localGamma (hausdorff n X) hX.quadratic f.val g.val ∧
      SobolevSpace.toLp (hausdorff n X) hX.quadratic GG =ᵐ[hausdorff n X]
        localGamma (hausdorff n X) hX.quadratic g.val g.val ∧
      (∀ᵐ x ∂(hausdorff n X).restrict S,
        (SobolevSpace.toLp (hausdorff n X) hX.quadratic df x)^2≤
          (n:ℝ)*(σ.rnDeriv (hausdorff n X) x).toReal) ∧
      ∀ b : ℝ, ∀ᵐ x ∂(hausdorff n X).restrict S,
        (localHessianAction (hausdorff n X) hX.quadratic f.val g.val g.val FG FG GG x-
          b*localGamma (hausdorff n X) hX.quadratic g.val g.val x)^2 ≤
          ((σ.rnDeriv (hausdorff n X) x).toReal-
            2*b*SobolevSpace.toLp (hausdorff n X) hX.quadratic df x+(n:ℝ)*b^2)*
            (localGamma (hausdorff n X) hX.quadratic g.val g.val x)^2 := by
  let := hX.separable
  let := locallyFinite_of_finiteOnBounded (hausdorff n X) hX.finiteOnBounded
  let μ := hausdorff n X
  let hQ := hX.quadratic
  obtain ⟨F,FG,GG,ν,hν,hFr,hFGr,hGGr,hFlap,hdim,hbound⟩ :=
    hX.regular_core_shifted_hessian_weak hn hscalar f g p hR hS hsub df qf hqf A hdf hsf
  let := hν
  obtain ⟨χ,hχΩ,hχ1⟩ := hX.exists_open_regular_cutoff hn isOpen_ball hS hsub
  let χb : X →ᵇ ℝ := ofCompactSupport χ.weight χ.lipschitz.continuous χ.compact
  have hsame : SobolevSpace.toLp μ hQ F =ᵐ[μ.restrict (ball p R)]
      SobolevSpace.toLp μ hQ F₀ := by
    filter_upwards [ae_restrict_of_ae hFr,hF₀] with x hf hg
    exact hf.trans hg.symm
  have hden := bochnerDensity_curvature_le μ hQ measurableSet_ball hS.measurableSet hJK
    f.val df F F₀ ν σ hFlap hσ hsame χb χ.lipschitz χ.compact hχΩ
    (fun x => (χ.bounds x).1) hχ1
  refine ⟨FG,GG,hFGr,hGGr,?_,?_⟩
  · filter_upwards [hdim,hden] with x hx he
    exact hx.trans (mul_le_mul_of_nonneg_left he (Nat.cast_nonneg n))
  · intro b
    filter_upwards [hbound b,hden] with x hx he
    apply hx.trans
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    linarith only [he]

end RegularPointCoordinates

end

end OAI
