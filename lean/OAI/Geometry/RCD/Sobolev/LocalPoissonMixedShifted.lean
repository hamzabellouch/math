import OAI.Geometry.RCD.Coordinates.RegularTripleHessian
import OAI.Geometry.RCD.Coordinates.LocalPoissonRegularExtension
import OAI.Geometry.RCD.Coordinates.LocalConstantRepresentative
import OAI.Geometry.RCD.Metric.LocalDensitySource

namespace OAI

/-! # Shifted mixed Hessian bounds for three actual local Poisson functions -/

open Set Filter Metric MeasureTheory
open scoped NNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.local_poisson_mixed_shifted_bound {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2≤n)
    (hscalar : ScalarDimensionalBochner (hausdorff n X) hX.quadratic K n)
    (f a z : SobolevSpace (hausdorff n X) hX.quadratic) (c d e κ : ℝ) (hK : -κ≤K)
    {p : X} {r : ℝ} (hr : 0<r)
    (hf : IsConstantLaplacianOn (hausdorff n X) hX.quadratic (ball p (8*r)) f c)
    (ha : IsConstantLaplacianOn (hausdorff n X) hX.quadratic (ball p (8*r)) a d)
    (hz : IsConstantLaplacianOn (hausdorff n X) hX.quadratic (ball p (8*r)) z e)
    (L M N : ℝ≥0)
    (hL : ∀ᵐ x ∂(hausdorff n X).restrict (ball p (8*r)),
      localGamma (hausdorff n X) hX.quadratic f f x≤(L:ℝ)^2)
    (hM : ∀ᵐ x ∂(hausdorff n X).restrict (ball p (8*r)),
      localGamma (hausdorff n X) hX.quadratic a a x≤(M:ℝ)^2)
    (hN : ∀ᵐ x ∂(hausdorff n X).restrict (ball p (8*r)),
      localGamma (hausdorff n X) hX.quadratic z z x≤(N:ℝ)^2)
    (F₀ : SobolevSpace (hausdorff n X) hX.quadratic) (σ : Measure X) [IsFiniteMeasure σ]
    (hF₀ : SobolevSpace.toLp (hausdorff n X) hX.quadratic F₀
      =ᵐ[(hausdorff n X).restrict (ball p (2*r))] localGamma (hausdorff n X) hX.quadratic f f)
    (hσ : IsMeasureLaplacianOn (hausdorff n X) hX.quadratic (ball p (2*r)) F₀
      ((2:ℝ) • σ.toSignedMeasure-(2*κ) • (hausdorff n X).withDensityᵥ
        (localGamma (hausdorff n X) hX.quadratic f f))) :
    ∃ Fga Fgz Gaz : SobolevSpace (hausdorff n X) hX.quadratic,
      SobolevSpace.toLp (hausdorff n X) hX.quadratic Fga
        =ᵐ[(hausdorff n X).restrict (ball p (2*r))] localGamma (hausdorff n X) hX.quadratic f a ∧
      SobolevSpace.toLp (hausdorff n X) hX.quadratic Fgz
        =ᵐ[(hausdorff n X).restrict (ball p (2*r))] localGamma (hausdorff n X) hX.quadratic f z ∧
      SobolevSpace.toLp (hausdorff n X) hX.quadratic Gaz
        =ᵐ[(hausdorff n X).restrict (ball p (2*r))] localGamma (hausdorff n X) hX.quadratic a z ∧
      ∀ b : ℝ, ∀ᵐ x ∂(hausdorff n X).restrict (ball p (2*r)),
        (localHessianAction (hausdorff n X) hX.quadratic f a z Fga Fgz Gaz x-
          b*localGamma (hausdorff n X) hX.quadratic a z x)^2≤
        ((σ.rnDeriv (hausdorff n X) x).toReal-(2*b*c-(n:ℝ)*b^2))*
          localGamma (hausdorff n X) hX.quadratic a a x*
          localGamma (hausdorff n X) hX.quadratic z z x := by
  let := hX.separable
  let := locallyFinite_of_finiteOnBounded (hausdorff n X) hX.finiteOnBounded
  let μ := hausdorff n X
  let hQ := hX.quadratic
  obtain ⟨F,qf,hqf,hFr,hqc⟩ := hX.local_poisson_regular_extension hn f c
    (R := 3*r) (by positivity) (by linarith) hf L hL
  obtain ⟨A,_,_,hAr,_⟩ := hX.local_poisson_regular_extension hn a d
    (R := 3*r) (by positivity) (by linarith) ha M hM
  obtain ⟨Z,_,_,hZr,_⟩ := hX.local_poisson_regular_extension hn z e
    (R := 3*r) (by positivity) (by linarith) hz N hN
  have h23 : ball p (2*r) ⊆ ball p (3*r) := ball_subset_ball (by linarith)
  have hF : SobolevSpace.toLp μ hQ F.val =ᵐ[μ.restrict (ball p (2*r))]
      SobolevSpace.toLp μ hQ f := ae_restrict_of_ae_restrict_of_subset h23 hFr
  have hA : SobolevSpace.toLp μ hQ A.val =ᵐ[μ.restrict (ball p (2*r))]
      SobolevSpace.toLp μ hQ a := ae_restrict_of_ae_restrict_of_subset h23 hAr
  have hZ : SobolevSpace.toLp μ hQ Z.val =ᵐ[μ.restrict (ball p (2*r))]
      SobolevSpace.toLp μ hQ z := ae_restrict_of_ae_restrict_of_subset h23 hZr
  obtain ⟨df,hdf,hdfc⟩ := hX.local_constant_representative hn p (2*r) c
  have hsf : qf =ᵐ[μ.restrict (ball p (2*r))] SobolevSpace.toLp μ hQ df := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset h23 hqc,hdfc] with x hx hy
    exact hx.trans hy.symm
  have hE : SobolevSpace.toLp μ hQ F₀ =ᵐ[μ.restrict (ball p (2*r))]
      localGamma μ hQ F.val F.val :=
    hF₀.trans (localGamma_pair_congr_ae μ hQ hF hF).symm
  have hsource := hσ.bochner_constant_source_shifted μ hQ measurableSet_ball κ F₀ f F.val df c
    σ.toSignedMeasure hF hdfc
  obtain ⟨Fga,Fgz,Gaz,hga,hgz,haz,_,hb⟩ := hX.regular_core_triple_hessian_on_measure
    hn hscalar F A Z p (by positivity : 0<2*r) df qf hqf ‖c‖₊ hdf hsf hK F₀ σ hE hsource
  refine ⟨Fga,Fgz,Gaz,?_,?_,?_,?_⟩
  · filter_upwards [ae_restrict_of_ae hga,localGamma_pair_congr_ae μ hQ hF hA] with x hx hy
    exact hx.trans hy
  · filter_upwards [ae_restrict_of_ae hgz,localGamma_pair_congr_ae μ hQ hF hZ] with x hx hy
    exact hx.trans hy
  · filter_upwards [ae_restrict_of_ae haz,localGamma_pair_congr_ae μ hQ hA hZ] with x hx hy
    exact hx.trans hy
  · intro b
    have he := localHessianAction_congr μ hQ (fu := Fga) (fu' := Fga)
      (fv := Fgz) (fv' := Fgz) (uv := Gaz) (uv' := Gaz)
      hF hA hZ EventuallyEq.rfl EventuallyEq.rfl EventuallyEq.rfl
    filter_upwards [hb b,he,hdfc,localGamma_pair_congr_ae μ hQ hA hZ,
      localGamma_pair_congr_ae μ hQ hA hA,localGamma_pair_congr_ae μ hQ hZ hZ]
      with x hx he hc haz haa hzz
    rw [he,hc,haz,haa,hzz] at hx
    convert hx using 1
    ring

end RegularPointCoordinates

end

end OAI
