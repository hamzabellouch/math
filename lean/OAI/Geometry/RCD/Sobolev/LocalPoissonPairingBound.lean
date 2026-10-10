import OAI.Geometry.RCD.Coordinates.RegularPairingChoiceBound
import OAI.Geometry.RCD.Sobolev.HessianLocality
import OAI.Geometry.RCD.Coordinates.LocalPoissonRegularExtension
import OAI.Geometry.RCD.Coordinates.LocalConstantRepresentative
import OAI.Geometry.RCD.Metric.LocalDensitySource

namespace OAI

/-! # The all-Dirichlet local Poisson Hessian bound from scalar dimensional Bochner -/

open Set Filter Metric MeasureTheory
open scoped NNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- Actual local Poisson extensions and the prescribed full measure
inherit the sharp shifted estimate. The scalar finite-dimensional
Bochner inequality is the only additional analytic premise. -/
theorem NoncollapsedRCD.local_poisson_hessian_pairing_bound_of_scalar {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2≤n)
    (hscalar : ScalarDimensionalBochner (hausdorff n X) hX.quadratic K n)
    (f a : SobolevSpace (hausdorff n X) hX.quadratic) (c d κ : ℝ) (hK : -κ≤K)
    {p : X} {r t : ℝ} (hr : 0<r) (ht : t≤2*r)
    (hf : IsConstantLaplacianOn (hausdorff n X) hX.quadratic (ball p (8*r)) f c)
    (ha : IsConstantLaplacianOn (hausdorff n X) hX.quadratic (ball p (8*r)) a d)
    (L M : ℝ≥0)
    (hL : ∀ᵐ x ∂(hausdorff n X).restrict (ball p (8*r)),
      localGamma (hausdorff n X) hX.quadratic f f x≤(L:ℝ)^2)
    (hM : ∀ᵐ x ∂(hausdorff n X).restrict (ball p (8*r)),
      localGamma (hausdorff n X) hX.quadratic a a x≤(M:ℝ)^2)
    (F₀ : SobolevSpace (hausdorff n X) hX.quadratic) (σ : Measure X) [IsFiniteMeasure σ]
    (hF₀ : SobolevSpace.toLp (hausdorff n X) hX.quadratic F₀
      =ᵐ[(hausdorff n X).restrict (ball p (2*r))] localGamma (hausdorff n X) hX.quadratic f f)
    (hσ : IsMeasureLaplacianOn (hausdorff n X) hX.quadratic (ball p (2*r)) F₀
      ((2:ℝ) • σ.toSignedMeasure-(2*κ) • (hausdorff n X).withDensityᵥ
        (localGamma (hausdorff n X) hX.quadratic f f)))
    (G : LocalHessianPairing (hausdorff n X) hX.quadratic (ball p t) f a) :
    ∀ (b : ℝ) (φ : SobolevSpace.dirichlet (hausdorff n X) hX.quadratic (ball p t)),
      (G.hessian φ-b*energyForm (hausdorff n X) hX.quadratic a φ.val)^2≤
        ((M:ℝ)^2*(σ.real (ball p t)-(2*b*c-(n:ℝ)*b^2)*(hausdorff n X).real (ball p t)))*
          energyForm (hausdorff n X) hX.quadratic φ.val φ.val := by
  let := hX.separable
  let := locallyFinite_of_finiteOnBounded (hausdorff n X) hX.finiteOnBounded
  let μ := hausdorff n X
  let hQ := hX.quadratic
  obtain ⟨F,qf,hqf,hFr,hqc⟩ := hX.local_poisson_regular_extension hn f c
    (R := 3*r) (by positivity) (by linarith) hf L hL
  obtain ⟨A,_,_,hAr,_⟩ := hX.local_poisson_regular_extension hn a d
    (R := 3*r) (by positivity) (by linarith) ha M hM
  have h23 : ball p (2*r) ⊆ ball p (3*r) := ball_subset_ball (by linarith)
  have hF := ae_restrict_of_ae_restrict_of_subset h23 hFr
  have hA := ae_restrict_of_ae_restrict_of_subset h23 hAr
  obtain ⟨df,hdf,hdfc⟩ := hX.local_constant_representative hn p (2*r) c
  have hsf : qf =ᵐ[μ.restrict (ball p (2*r))] SobolevSpace.toLp μ hQ df := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset h23 hqc,hdfc] with x hx hy
    exact hx.trans hy.symm
  have hE : SobolevSpace.toLp μ hQ F₀ =ᵐ[μ.restrict (ball p (2*r))]
      localGamma μ hQ F.val F.val :=
    hF₀.trans (localGamma_pair_congr_ae μ hQ hF hF).symm
  have hsource := hσ.bochner_constant_source_shifted μ hQ measurableSet_ball κ F₀ f F.val df c
    σ.toSignedMeasure hF hdfc
  have hS : ball p t ⊆ ball p (2*r) := ball_subset_ball ht
  have hFt : SobolevSpace.toLp μ hQ F.val =ᵐ[μ.restrict (ball p t)]
      SobolevSpace.toLp μ hQ f := ae_restrict_of_ae_restrict_of_subset hS hF
  have hAt : SobolevSpace.toLp μ hQ A.val =ᵐ[μ.restrict (ball p t)]
      SobolevSpace.toLp μ hQ a := ae_restrict_of_ae_restrict_of_subset hS hA
  let P := G.congr μ hQ measurableSet_ball hFt.symm hAt.symm
  have hbig : ball p t ⊆ ball p (8*r) := hS.trans (ball_subset_ball (by linarith))
  have hFc : IsConstantLaplacianOn μ hQ (ball p t) F.val c :=
    (hf.mono _ _ measurableSet_ball hbig).congr_ae μ hQ measurableSet_ball hFt.symm
  have hAc : IsConstantLaplacianOn μ hQ (ball p t) A.val d :=
    (ha.mono _ _ measurableSet_ball hbig).congr_ae μ hQ measurableSet_ball hAt.symm
  have hgrad : ∀ᵐ x ∂μ.restrict (ball p t), localGamma μ hQ A.val A.val x≤(M:ℝ)^2 := by
    filter_upwards [localGamma_pair_congr_ae μ hQ hAt hAt,
      ae_restrict_of_ae_restrict_of_subset hbig hM] with x he hb
    rw [he]
    exact hb
  have hh := hX.regular_pairing_shifted_bound_any_core hn hscalar F A p
    (by positivity : 0<2*r) df qf hqf ‖c‖₊ hdf hsf c hdfc hK F₀ σ hE hsource
    ht d hFc hAc P ((M:ℝ)^2) (sq_nonneg _) hgrad
  intro b φ
  have hb := hh b φ
  change (G.hessian φ-b*energyForm μ hQ A.val φ.val)^2≤_ at hb
  rw [energyForm_eq_of_dirichlet μ hQ measurableSet_ball hAt φ] at hb
  exact hb

end RegularPointCoordinates

end

end OAI
