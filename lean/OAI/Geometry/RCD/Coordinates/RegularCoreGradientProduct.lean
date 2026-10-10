import OAI.Geometry.RCD.Coordinates.RegularTripleHessian
import OAI.Geometry.RCD.Sobolev.GradientProductAction

namespace OAI

/-! # Gradient-product tests against every compact regular direction

Two mixed Hessian actions and the exact Gram derivative identity give the
factor-two gradient bound. No regularity of the Gram representative beyond
membership in the Sobolev space is imposed.
-/

open Set Filter Metric MeasureTheory
open scoped NNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.regular_core_gradient_product_test {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2≤n)
    (hscalar : ScalarDimensionalBochner (hausdorff n X) hX.quadratic K n)
    (f a g : compactLaplacianCore (hausdorff n X) hX.quadratic univ)
    (p : X) {R : ℝ} (hR : 0<R)
    (df da : SobolevSpace (hausdorff n X) hX.quadratic)
    (qf qa : Lp ℝ 2 (hausdorff n X))
    (hqf : IsWeakLaplacian (hausdorff n X) hX.quadratic f.val qf)
    (hqa : IsWeakLaplacian (hausdorff n X) hX.quadratic a.val qa)
    (A B : ℝ≥0)
    (hdf : ∀ᵐ x ∂hausdorff n X, |SobolevSpace.toLp (hausdorff n X) hX.quadratic df x|≤A)
    (hda : ∀ᵐ x ∂hausdorff n X, |SobolevSpace.toLp (hausdorff n X) hX.quadratic da x|≤B)
    (hsf : qf =ᵐ[(hausdorff n X).restrict (ball p R)] SobolevSpace.toLp (hausdorff n X) hX.quadratic df)
    (hsa : qa =ᵐ[(hausdorff n X).restrict (ball p R)] SobolevSpace.toLp (hausdorff n X) hX.quadratic da)
    (c : ℝ) (hc : SobolevSpace.toLp (hausdorff n X) hX.quadratic df
      =ᵐ[(hausdorff n X).restrict (ball p R)] fun _ => c)
    {J : ℝ} (hJK : J≤K)
    (F₀ A₀ G : SobolevSpace (hausdorff n X) hX.quadratic)
    (σ τ : Measure X) [IsFiniteMeasure σ] [IsFiniteMeasure τ]
    (hF₀ : SobolevSpace.toLp (hausdorff n X) hX.quadratic F₀
      =ᵐ[(hausdorff n X).restrict (ball p R)] localGamma (hausdorff n X) hX.quadratic f.val f.val)
    (hA₀ : SobolevSpace.toLp (hausdorff n X) hX.quadratic A₀
      =ᵐ[(hausdorff n X).restrict (ball p R)] localGamma (hausdorff n X) hX.quadratic a.val a.val)
    (hG : SobolevSpace.toLp (hausdorff n X) hX.quadratic G
      =ᵐ[(hausdorff n X).restrict (ball p R)] localGamma (hausdorff n X) hX.quadratic f.val a.val)
    (hσ : IsMeasureLaplacianOn (hausdorff n X) hX.quadratic (ball p R) F₀
      (bochnerGramSource (hausdorff n X) hX.quadratic J f.val f.val df df σ.toSignedMeasure))
    (hτ : IsMeasureLaplacianOn (hausdorff n X) hX.quadratic (ball p R) A₀
      (bochnerGramSource (hausdorff n X) hX.quadratic J a.val a.val da da τ.toSignedMeasure))
    (b : ℝ) :
    ∀ᵐ x ∂(hausdorff n X).restrict (ball p R),
      (localGamma (hausdorff n X) hX.quadratic (G-b • a.val) g.val x)^2≤
        (2*localGamma (hausdorff n X) hX.quadratic a.val a.val x*
            ((σ.rnDeriv (hausdorff n X) x).toReal-(2*b*c-(n:ℝ)*b^2))+
          2*localGamma (hausdorff n X) hX.quadratic f.val f.val x*
            (τ.rnDeriv (hausdorff n X) x).toReal)*
              localGamma (hausdorff n X) hX.quadratic g.val g.val x := by
  let μ := hausdorff n X
  let hQ := hX.quadratic
  obtain ⟨Fga,Fg,Ag,hga,hfg,hag,_,hfirst⟩ := hX.regular_core_triple_hessian_on_measure
    hn hscalar f a g p hR df qf hqf A hdf hsf hJK F₀ σ hF₀ hσ
  obtain ⟨Afa,Ag',Fg',haf,hag',hfg',_,hsecond⟩ := hX.regular_core_triple_hessian_on_measure
    hn hscalar a f g p hR da qa hqa B hda hsa hJK A₀ τ hA₀ hτ
  have hgaG : SobolevSpace.toLp μ hQ Fga =ᵐ[μ.restrict (ball p R)] SobolevSpace.toLp μ hQ G := by
    filter_upwards [ae_restrict_of_ae hga,hG] with x hx hy
    exact hx.trans hy.symm
  have hafG : SobolevSpace.toLp μ hQ Afa =ᵐ[μ.restrict (ball p R)] SobolevSpace.toLp μ hQ G := by
    filter_upwards [ae_restrict_of_ae haf,hG,ae_restrict_of_ae (localGamma_comm μ hQ a.val f.val)]
      with x hx hy he
    exact hx.trans (he.trans hy.symm)
  have hAg : SobolevSpace.toLp μ hQ Ag' =ᵐ[μ.restrict (ball p R)] SobolevSpace.toLp μ hQ Ag :=
    ae_restrict_of_ae (hag'.trans hag.symm)
  have hFg : SobolevSpace.toLp μ hQ Fg' =ᵐ[μ.restrict (ball p R)] SobolevSpace.toLp μ hQ Fg :=
    ae_restrict_of_ae (hfg'.trans hfg.symm)
  have he1 := localHessianAction_congr μ hQ (f := f.val) (f' := f.val)
    (u := a.val) (u' := a.val) (v := g.val) (v' := g.val)
    (fv := Fg) (fv' := Fg) (uv := Ag) (uv' := Ag)
    EventuallyEq.rfl EventuallyEq.rfl EventuallyEq.rfl hgaG EventuallyEq.rfl EventuallyEq.rfl
  have he2 := localHessianAction_congr μ hQ (f := a.val) (f' := a.val)
    (u := f.val) (u' := f.val) (v := g.val) (v' := g.val)
    EventuallyEq.rfl EventuallyEq.rfl EventuallyEq.rfl hafG hAg hFg
  filter_upwards [hfirst b,hsecond 0,he1,he2,hc,
    ae_restrict_of_ae (localGamma_mixed_as_hessian_actions μ hQ f.val a.val g.val G Fg Ag b)]
    with x h1 h2 he1 he2 hc hid
  rw [he1,hc] at h1
  rw [he2] at h2
  simp only [zero_mul,sub_zero,mul_zero,zero_pow (by decide : (2:ℕ)≠0),add_zero] at h2
  rw [hid]
  nlinarith only [h1,h2,sq_nonneg
    ((localHessianAction μ hQ f.val a.val g.val G Fg Ag x-b*localGamma μ hQ a.val g.val x)-
      localHessianAction μ hQ a.val f.val g.val G Ag Fg x)]

end RegularPointCoordinates

end

end OAI
