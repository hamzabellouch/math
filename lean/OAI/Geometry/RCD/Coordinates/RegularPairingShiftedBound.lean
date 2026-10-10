import OAI.Geometry.RCD.Coordinates.RegularTripleHessian
import OAI.Geometry.RCD.Sobolev.HessianActionCoreIntegral

namespace OAI

/-! # The shifted estimate on every Dirichlet test

The finite regular-family estimate applies to the actual dense core of a
local Hessian pairing, and continuity then gives the full Dirichlet bound.
-/

open Set Filter Metric MeasureTheory
open scoped NNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.regular_pairing_shifted_bound {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2≤n)
    (hscalar : ScalarDimensionalBochner (hausdorff n X) hX.quadratic K n)
    (f a : compactLaplacianCore (hausdorff n X) hX.quadratic univ)
    (p : X) {R : ℝ} (hR : 0<R)
    (df : SobolevSpace (hausdorff n X) hX.quadratic) (qf : Lp ℝ 2 (hausdorff n X))
    (hqf : IsWeakLaplacian (hausdorff n X) hX.quadratic f.val qf)
    (A : ℝ≥0) (hdf : ∀ᵐ x ∂hausdorff n X, |SobolevSpace.toLp (hausdorff n X) hX.quadratic df x|≤A)
    (hsf : qf =ᵐ[(hausdorff n X).restrict (ball p R)] SobolevSpace.toLp (hausdorff n X) hX.quadratic df)
    (c : ℝ) (hc : SobolevSpace.toLp (hausdorff n X) hX.quadratic df
      =ᵐ[(hausdorff n X).restrict (ball p R)] fun _ => c)
    {J : ℝ} (hJK : J≤K)
    (F₀ : SobolevSpace (hausdorff n X) hX.quadratic) (σ : Measure X) [IsFiniteMeasure σ]
    (hF₀ : SobolevSpace.toLp (hausdorff n X) hX.quadratic F₀
      =ᵐ[(hausdorff n X).restrict (ball p R)] localGamma (hausdorff n X) hX.quadratic f.val f.val)
    (hσ : IsMeasureLaplacianOn (hausdorff n X) hX.quadratic (ball p R) F₀
      (bochnerGramSource (hausdorff n X) hX.quadratic J f.val f.val df df σ.toSignedMeasure))
    {t : ℝ} (ht : t≤R)
    (G : LocalHessianPairing (hausdorff n X) hX.quadratic (ball p t) f.val a.val)
    (hcore : ∀ φ : G.core, φ.val.val∈compactLaplacianCore (hausdorff n X) hX.quadratic univ)
    (B : ℝ) (hB : 0≤B)
    (hgrad : ∀ᵐ x ∂(hausdorff n X).restrict (ball p t), localGamma (hausdorff n X) hX.quadratic a.val a.val x≤B) :
    ∀ (b : ℝ) (φ : SobolevSpace.dirichlet (hausdorff n X) hX.quadratic (ball p t)),
      (G.hessian φ-b*energyForm (hausdorff n X) hX.quadratic a.val φ.val)^2≤
        (B*(σ.real (ball p t)-(2*b*c-(n:ℝ)*b^2)*(hausdorff n X).real (ball p t)))*
          energyForm (hausdorff n X) hX.quadratic φ.val φ.val := by
  let := hX.separable
  let := locallyFinite_of_finiteOnBounded (hausdorff n X) hX.finiteOnBounded
  let μ := hausdorff n X
  let hQ := hX.quadratic
  let : IsFiniteMeasure (μ.restrict (ball p t)) := ⟨by
    simpa only [Measure.restrict_apply_univ,μ] using hX.finiteOnBounded (ball p t) isBounded_ball⟩
  have hsub : ball p t ⊆ ball p R := ball_subset_ball ht
  have hget (φ : G.core) : ∃ Fga Fgφ Gaφ : SobolevSpace μ hQ,
      SobolevSpace.toLp μ hQ Fga =ᵐ[μ] localGamma μ hQ f.val a.val ∧
      SobolevSpace.toLp μ hQ Fgφ =ᵐ[μ] localGamma μ hQ f.val φ.val.val ∧
      SobolevSpace.toLp μ hQ Gaφ =ᵐ[μ] localGamma μ hQ a.val φ.val.val ∧
      (∀ᵐ x ∂μ.restrict (ball p R), (SobolevSpace.toLp μ hQ df x)^2≤(n:ℝ)*(σ.rnDeriv μ x).toReal) ∧
      ∀ b : ℝ, ∀ᵐ x ∂μ.restrict (ball p R),
        (localHessianAction μ hQ f.val a.val φ.val.val Fga Fgφ Gaφ x-
          b*localGamma μ hQ a.val φ.val.val x)^2≤
        ((σ.rnDeriv μ x).toReal-2*b*SobolevSpace.toLp μ hQ df x+(n:ℝ)*b^2)*
          localGamma μ hQ a.val a.val x*localGamma μ hQ φ.val.val φ.val.val x := by
    exact hX.regular_core_triple_hessian_on_measure hn hscalar f a ⟨φ.val.val,hcore φ⟩
      p hR df qf hqf A hdf hsf hJK F₀ σ hF₀ hσ
  intro b
  obtain ⟨_,_,_,_,_,_,hdim,_⟩ := hget 0
  have hn0 : 0<(n:ℝ) := by exact_mod_cast (by omega : 0<n)
  have hden : ∀ᵐ x ∂μ.restrict (ball p t), 2*b*c-(n:ℝ)*b^2≤(σ.rnDeriv μ x).toReal := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub hdim,
      ae_restrict_of_ae_restrict_of_subset hsub hc] with x hx hc
    rw [hc] at hx
    have hp : 0≤(n:ℝ)*((σ.rnDeriv μ x).toReal-(2*b*c-(n:ℝ)*b^2)) := by
      nlinarith only [hx,sq_nonneg (c-(n:ℝ)*b)]
    exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_left hn0).mp hp)
  apply G.bound_of_core_action μ hQ measurableSet_ball σ b (2*b*c-(n:ℝ)*b^2) B hB hden
  intro φ
  obtain ⟨Fga,Fgφ,Gaφ,hga,hgφ,haφ,_,hb⟩ := hget φ
  have hga' : SobolevSpace.toLp μ hQ Fga =ᵐ[μ.restrict (ball p t)]
      SobolevSpace.toLp μ hQ G.mixed :=
    by
      have hgaR : SobolevSpace.toLp μ hQ Fga =ᵐ[μ.restrict (ball p t)]
          localGamma μ hQ f.val a.val := ae_restrict_of_ae hga
      exact hgaR.trans G.mixed_rep.symm
  have hgφ' : SobolevSpace.toLp μ hQ Fgφ =ᵐ[μ.restrict (ball p t)]
      SobolevSpace.toLp μ hQ (G.gammaF φ).val :=
    ae_restrict_of_ae (hgφ.trans (G.gammaF_rep φ).symm)
  have haφ' : SobolevSpace.toLp μ hQ Gaφ =ᵐ[μ.restrict (ball p t)]
      SobolevSpace.toLp μ hQ (G.gammaA φ).val :=
    ae_restrict_of_ae (haφ.trans (G.gammaA_rep φ).symm)
  have hact : localHessianAction μ hQ f.val a.val φ.val.val Fga Fgφ Gaφ
      =ᵐ[μ.restrict (ball p t)] localHessianAction μ hQ f.val a.val φ.val.val
        G.mixed (G.gammaF φ).val (G.gammaA φ).val :=
    localHessianAction_congr μ hQ EventuallyEq.rfl EventuallyEq.rfl EventuallyEq.rfl hga' hgφ' haφ'
  filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub (hb b),hact,hden,hgrad,
    ae_restrict_of_ae_restrict_of_subset hsub hc,
    ae_restrict_of_ae (localGamma_self μ hQ φ.val.val)] with x hx he hd hgrad hc hself
  rw [he,hc] at hx
  have h0 : 0≤localGamma μ hQ φ.val.val φ.val.val x := by rw [hself]; positivity
  apply hx.trans
  calc
    _ ≤ ((σ.rnDeriv μ x).toReal-2*b*c+(n:ℝ)*b^2)*B*localGamma μ hQ φ.val.val φ.val.val x :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hgrad (by linarith only [hd])) h0
    _ = _ := by ring

end RegularPointCoordinates

end

end OAI
