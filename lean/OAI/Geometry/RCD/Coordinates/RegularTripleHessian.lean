import OAI.Geometry.RCD.Coordinates.RegularCoreMixedFullBall

namespace OAI

/-! # Three fixed regular functions in the prescribed mixed Hessian bound -/

open Set Filter Metric MeasureTheory
open scoped NNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.regular_core_triple_hessian_on_measure {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2≤n)
    (hscalar : ScalarDimensionalBochner (hausdorff n X) hX.quadratic K n)
    (f a g : compactLaplacianCore (hausdorff n X) hX.quadratic univ)
    (p : X) {R : ℝ} (hR : 0<R)
    (df : SobolevSpace (hausdorff n X) hX.quadratic) (qf : Lp ℝ 2 (hausdorff n X))
    (hqf : IsWeakLaplacian (hausdorff n X) hX.quadratic f.val qf)
    (A : ℝ≥0) (hdf : ∀ᵐ x ∂hausdorff n X, |SobolevSpace.toLp (hausdorff n X) hX.quadratic df x|≤A)
    (hsf : qf =ᵐ[(hausdorff n X).restrict (ball p R)] SobolevSpace.toLp (hausdorff n X) hX.quadratic df)
    {J : ℝ} (hJK : J≤K)
    (F₀ : SobolevSpace (hausdorff n X) hX.quadratic) (σ : Measure X) [IsFiniteMeasure σ]
    (hF₀ : SobolevSpace.toLp (hausdorff n X) hX.quadratic F₀
      =ᵐ[(hausdorff n X).restrict (ball p R)] localGamma (hausdorff n X) hX.quadratic f.val f.val)
    (hσ : IsMeasureLaplacianOn (hausdorff n X) hX.quadratic (ball p R) F₀
      (bochnerGramSource (hausdorff n X) hX.quadratic J f.val f.val df df σ.toSignedMeasure))
    : let μ := hausdorff n X
      let hQ := hX.quadratic
      ∃ Fga Fgφ Gaφ : SobolevSpace μ hQ,
      SobolevSpace.toLp μ hQ Fga =ᵐ[μ] localGamma μ hQ f.val a.val ∧
      SobolevSpace.toLp μ hQ Fgφ =ᵐ[μ] localGamma μ hQ f.val g.val ∧
      SobolevSpace.toLp μ hQ Gaφ =ᵐ[μ] localGamma μ hQ a.val g.val ∧
      (∀ᵐ x ∂μ.restrict (ball p R), (SobolevSpace.toLp μ hQ df x)^2≤(n:ℝ)*(σ.rnDeriv μ x).toReal) ∧
      ∀ b : ℝ, ∀ᵐ x ∂μ.restrict (ball p R),
        (localHessianAction μ hQ f.val a.val g.val Fga Fgφ Gaφ x-
          b*localGamma μ hQ a.val g.val x)^2≤
        ((σ.rnDeriv μ x).toReal-2*b*SobolevSpace.toLp μ hQ df x+(n:ℝ)*b^2)*
          localGamma μ hQ a.val a.val x*localGamma μ hQ g.val g.val x := by
  let μ := hausdorff n X
  let hQ := hX.quadratic
  let e (i : Fin 3) : Euclidean 3 := EuclideanSpace.single i 1
  let u : Fin 3 → compactLaplacianCore μ hQ univ := ![f,a,g]
  let U := sobolevColumnMap μ hQ (fun i => (u i).val)
  have h₀ : U (e 0)=f.val := by simpa [u,e] using sobolevColumnMap_single μ hQ (fun i => (u i).val) 0
  have h₁ : U (e 1)=a.val := by simpa [u,e] using sobolevColumnMap_single μ hQ (fun i => (u i).val) 1
  have h₂ : U (e 2)=g.val := by simpa [u,e] using sobolevColumnMap_single μ hQ (fun i => (u i).val) 2
  have hq : IsWeakLaplacian μ hQ (U (e 0)) qf := by rw [h₀]; exact hqf
  have hr : SobolevSpace.toLp μ hQ F₀ =ᵐ[μ.restrict (ball p R)]
      localGamma μ hQ (U (e 0)) (U (e 0)) := by rw [h₀]; exact hF₀
  have hs : IsMeasureLaplacianOn μ hQ (ball p R) F₀
      (bochnerGramSource μ hQ J (U (e 0)) (U (e 0)) df df σ.toSignedMeasure) := by
    rw [h₀]
    exact hσ
  obtain ⟨H,-,hH,hdim,hbound⟩ := hX.regular_core_mixed_hessian_full_ball hn hscalar u p hR
    (e 0) df qf hq A hdf hsf hJK F₀ σ hr hs
  change ∀ v w, SobolevSpace.toLp μ hQ (H v w) =ᵐ[μ] localGamma μ hQ (U v) (U w) at hH
  change ∀ b v w, ∀ᵐ x ∂μ.restrict (ball p R),
    (localHessianAction μ hQ (U (e 0)) (U v) (U w) (H (e 0) v) (H (e 0) w) (H v w) x-
      b*localGamma μ hQ (U v) (U w) x)^2≤
    ((σ.rnDeriv μ x).toReal-2*b*SobolevSpace.toLp μ hQ df x+(n:ℝ)*b^2)*
      localGamma μ hQ (U v) (U v) x*localGamma μ hQ (U w) (U w) x at hbound
  refine ⟨H (e 0) (e 1),H (e 0) (e 2),H (e 1) (e 2),?_,?_,?_,hdim,?_⟩
  · simpa only [h₀,h₁] using hH (e 0) (e 1)
  · simpa only [h₀,h₂] using hH (e 0) (e 2)
  · simpa only [h₁,h₂] using hH (e 1) (e 2)
  · intro b
    simpa only [h₀,h₁,h₂] using hbound b (e 1) (e 2)

end RegularPointCoordinates

end

end OAI
