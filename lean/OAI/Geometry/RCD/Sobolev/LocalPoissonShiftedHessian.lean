import OAI.Geometry.RCD.Coordinates.RegularCoreShiftedMeasure
import OAI.Geometry.RCD.Metric.ShiftedRadonBounds
import OAI.Geometry.RCD.Coordinates.LocalPoissonRegularExtension
import OAI.Geometry.RCD.Coordinates.LocalConstantRepresentative
import OAI.Geometry.RCD.Metric.LocalDensitySource

namespace OAI

/-! # Shifted local Poisson estimates from the scalar dimensional Bochner inequality -/

open Set Filter Metric MeasureTheory
open scoped NNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- Actual local Poisson extensions and the prescribed full measure
inherit the sharp shifted estimate. The scalar finite-dimensional
Bochner inequality is the only additional analytic premise. -/
theorem NoncollapsedRCD.local_poisson_shifted_hessian_of_scalar {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2≤n)
    (hscalar : ScalarDimensionalBochner (hausdorff n X) hX.quadratic K n)
    (f a : SobolevSpace (hausdorff n X) hX.quadratic) (c d κ : ℝ) (hK : -κ≤K)
    {p : X} {r t : ℝ} (hr : 0<r) (ht : t<2*r)
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
        (localGamma (hausdorff n X) hX.quadratic f f))) :
    ∃ (FG GG : SobolevSpace (hausdorff n X) hX.quadratic),
      SobolevSpace.toLp (hausdorff n X) hX.quadratic FG
        =ᵐ[(hausdorff n X).restrict (ball p (2*r))] localGamma (hausdorff n X) hX.quadratic f a ∧
      SobolevSpace.toLp (hausdorff n X) hX.quadratic GG
        =ᵐ[(hausdorff n X).restrict (ball p (2*r))] localGamma (hausdorff n X) hX.quadratic a a ∧
      (∀ᵐ x ∂(hausdorff n X).restrict (closedBall p t),
        c^2≤(n:ℝ)*(σ.rnDeriv (hausdorff n X) x).toReal) ∧
      ∀ b : ℝ,
      let H := fun x => localHessianAction (hausdorff n X) hX.quadratic f a a FG FG GG x-
        b*localGamma (hausdorff n X) hX.quadratic a a x
      (∀ᵐ x ∂(hausdorff n X).restrict (closedBall p t),
        (H x)^2≤((σ.rnDeriv (hausdorff n X) x).toReal-(2*b*c-(n:ℝ)*b^2))*
          (localGamma (hausdorff n X) hX.quadratic a a x)^2) ∧
      MemLp H 2 ((hausdorff n X).restrict (closedBall p t)) ∧
      (∫ x in closedBall p t, (H x)^2 ∂hausdorff n X)≤((M:ℝ)^2)^2*
        (σ.real (closedBall p t)-(2*b*c-(n:ℝ)*b^2)*(hausdorff n X).real (closedBall p t)) := by
  let := hX.separable
  let := locallyFinite_of_finiteOnBounded (hausdorff n X) hX.finiteOnBounded
  let μ := hausdorff n X
  let hQ := hX.quadratic
  let : IsFiniteMeasure (μ.restrict (closedBall p t)) := ⟨by
    simpa only [Measure.restrict_apply_univ,μ] using
      hX.finiteOnBounded (closedBall p t) isBounded_closedBall⟩
  obtain ⟨F,qf,hqf,hFr,hqc⟩ := hX.local_poisson_regular_extension hn f c
    (R := 3*r) (by positivity) (by linarith) hf L hL
  obtain ⟨A,qa,hqa,hAr,hqd⟩ := hX.local_poisson_regular_extension hn a d
    (R := 3*r) (by positivity) (by linarith) ha M hM
  have h23 : ball p (2*r) ⊆ ball p (3*r) := ball_subset_ball (by linarith)
  have hF := ae_restrict_of_ae_restrict_of_subset h23 hFr
  have hA := ae_restrict_of_ae_restrict_of_subset h23 hAr
  obtain ⟨df,hdf,hdfc⟩ := hX.local_constant_representative hn p (2*r) c
  obtain ⟨da,hda,hdad⟩ := hX.local_constant_representative hn p (2*r) d
  have hsf : qf =ᵐ[μ.restrict (ball p (2*r))] SobolevSpace.toLp μ hQ df := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset h23 hqc,hdfc] with x hx hy
    exact hx.trans hy.symm
  have hsa : qa =ᵐ[μ.restrict (ball p (2*r))] SobolevSpace.toLp μ hQ da := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset h23 hqd,hdad] with x hx hy
    exact hx.trans hy.symm
  have hE : SobolevSpace.toLp μ hQ F₀ =ᵐ[μ.restrict (ball p (2*r))]
      localGamma μ hQ F.val F.val :=
    hF₀.trans (localGamma_pair_congr_ae μ hQ hF hF).symm
  have hsource := hσ.bochner_constant_source_shifted μ hQ measurableSet_ball κ F₀ f F.val df c
    σ.toSignedMeasure hF hdfc
  have hS : closedBall p t ⊆ ball p (2*r) := closedBall_subset_ball ht
  have hAΓ := localGamma_pair_congr_ae μ hQ hA hA
  have hgrad : ∀ᵐ x ∂μ.restrict (closedBall p t), localGamma μ hQ A.val A.val x≤(M:ℝ)^2 := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hS hAΓ,
      ae_restrict_of_ae_restrict_of_subset
        (hS.trans (ball_subset_ball (by linarith : 2*r≤8*r))) hM] with x he hb
    rw [he]
    exact hb
  obtain ⟨FG,GG,hFG,hGG,hdim,hbound⟩ := hX.regular_core_shifted_hessian_on_measure
    hn hscalar F A p (by positivity : 0<2*r) (isCompact_closedBall p t) hS df da qf qa hqf hqa
    ‖c‖₊ ‖d‖₊ hdf hda hsf hsa hK F₀ σ hE hsource
  have hFG' : SobolevSpace.toLp μ hQ FG =ᵐ[μ.restrict (ball p (2*r))] localGamma μ hQ f a := by
    filter_upwards [ae_restrict_of_ae hFG,localGamma_pair_congr_ae μ hQ hF hA] with x hx hy
    exact hx.trans hy
  have hGG' : SobolevSpace.toLp μ hQ GG =ᵐ[μ.restrict (ball p (2*r))] localGamma μ hQ a a := by
    filter_upwards [ae_restrict_of_ae hGG,hAΓ] with x hx hy
    exact hx.trans hy
  have haction := localHessianAction_congr μ hQ
    (fu := FG) (fu' := FG) (fv := FG) (fv' := FG) (uv := GG) (uv' := GG)
    (ae_restrict_of_ae_restrict_of_subset hS hF) (ae_restrict_of_ae_restrict_of_subset hS hA)
    (ae_restrict_of_ae_restrict_of_subset hS hA) EventuallyEq.rfl EventuallyEq.rfl EventuallyEq.rfl
  have hdim' : ∀ᵐ x ∂μ.restrict (closedBall p t), c^2≤(n:ℝ)*(σ.rnDeriv μ x).toReal := by
    filter_upwards [hdim,ae_restrict_of_ae_restrict_of_subset hS hdfc] with x hx hc
    rwa [hc] at hx
  refine ⟨FG,GG,hFG',hGG',hdim',?_⟩
  intro b
  let H := fun x => localHessianAction μ hQ f a a FG FG GG x-b*localGamma μ hQ a a x
  have hb : ∀ᵐ x ∂μ.restrict (closedBall p t),
      (H x)^2≤((σ.rnDeriv μ x).toReal-(2*b*c-(n:ℝ)*b^2))*(localGamma μ hQ a a x)^2 := by
    filter_upwards [hbound b,haction,ae_restrict_of_ae_restrict_of_subset hS hAΓ,
      ae_restrict_of_ae_restrict_of_subset hS hdfc] with x hb he hγ hc
    rw [he,hγ,hc] at hb
    dsimp only [H]
    convert hb using 1
    ring
  have hn0 : 0<(n:ℝ) := by exact_mod_cast (by omega : 0<n)
  have hden : ∀ᵐ x ∂μ.restrict (closedBall p t), 2*b*c-(n:ℝ)*b^2≤(σ.rnDeriv μ x).toReal := by
    filter_upwards [hdim'] with x hx
    have hp : 0≤(n:ℝ)*((σ.rnDeriv μ x).toReal-(2*b*c-(n:ℝ)*b^2)) := by
      nlinarith only [hx,sq_nonneg (c-(n:ℝ)*b)]
    exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_left hn0).mp hp)
  have hcap : ∀ᵐ x ∂μ.restrict (closedBall p t), (H x)^2≤
      ((M:ℝ)^2)^2*((σ.rnDeriv μ x).toReal-(2*b*c-(n:ℝ)*b^2)) := by
    filter_upwards [hb,hden,ae_restrict_of_ae_restrict_of_subset hS hAΓ,hgrad,
      ae_restrict_of_ae (localGamma_self μ hQ a)] with x hb hd hγ hgrad ha
    have h0 : 0≤localGamma μ hQ a a x := by rw [ha]; positivity
    rw [hγ] at hgrad
    have hs := pow_le_pow_left₀ h0 hgrad 2
    exact hb.trans (by
      rw [mul_comm (((M:ℝ)^2)^2)]
      exact mul_le_mul_of_nonneg_left hs (sub_nonneg.mpr hd))
  have hmeas : AEStronglyMeasurable H (μ.restrict (closedBall p t)) :=
    ((localHessianAction_integrable μ hQ f a a FG FG GG).sub
      ((localGamma_memL1 μ hQ a a).const_mul b)).aestronglyMeasurable.restrict
  have hL2 := memLp_two_of_sq_le_shifted_radon μ σ hmeas (2*b*c-(n:ℝ)*b^2)
    (((M:ℝ)^2)^2) (sq_nonneg _) hcap
  exact ⟨hb,hL2⟩

end RegularPointCoordinates

end

end OAI
