import OAI.Geometry.RCD.Coordinates.RegularBochnerDirectional
import OAI.Geometry.RCD.Coordinates.RegularCoreBochner
import OAI.Geometry.RCD.Coordinates.RegularTestAlgebra

namespace OAI

/-! # Directional Hessian bounds for actual compact regular functions -/

open Set Filter Metric MeasureTheory
open scoped NNReal BoundedContinuousFunction

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- A regular function and one regular direction have a full positive
Bochner measure controlling their diagonal Hessian action. The measure
and all Gram representatives are constructed from the RCD structure. -/
theorem NoncollapsedRCD.regular_core_directional_hessian {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2≤n)
    {V : Set X} (f g : compactLaplacianCore (hausdorff n X) hX.quadratic V)
    (p : X) {R : ℝ} (hR : 0<R) {S : Set X} (hS : IsCompact S) (hsub : S ⊆ ball p R)
    (df dg : SobolevSpace (hausdorff n X) hX.quadratic)
    (qf qg : Lp ℝ 2 (hausdorff n X))
    (hqf : IsWeakLaplacian (hausdorff n X) hX.quadratic f.val qf)
    (hqg : IsWeakLaplacian (hausdorff n X) hX.quadratic g.val qg)
    (A B : ℝ≥0)
    (hdf : ∀ᵐ x ∂hausdorff n X, |SobolevSpace.toLp (hausdorff n X) hX.quadratic df x|≤A)
    (hdg : ∀ᵐ x ∂hausdorff n X, |SobolevSpace.toLp (hausdorff n X) hX.quadratic dg x|≤B)
    (hsf : qf =ᵐ[(hausdorff n X).restrict (ball p R)]
      SobolevSpace.toLp (hausdorff n X) hX.quadratic df)
    (hsg : qg =ᵐ[(hausdorff n X).restrict (ball p R)]
      SobolevSpace.toLp (hausdorff n X) hX.quadratic dg) :
    ∃ (F FG GG : SobolevSpace (hausdorff n X) hX.quadratic)
      (σ : Measure X) (hσ : IsFiniteMeasure σ),
      letI := hσ
      SobolevSpace.toLp (hausdorff n X) hX.quadratic F =ᵐ[hausdorff n X]
        localGamma (hausdorff n X) hX.quadratic f.val f.val ∧
      SobolevSpace.toLp (hausdorff n X) hX.quadratic FG =ᵐ[hausdorff n X]
        localGamma (hausdorff n X) hX.quadratic f.val g.val ∧
      SobolevSpace.toLp (hausdorff n X) hX.quadratic GG =ᵐ[hausdorff n X]
        localGamma (hausdorff n X) hX.quadratic g.val g.val ∧
      IsMeasureLaplacianOn (hausdorff n X) hX.quadratic (ball p R) F
        (bochnerGramSource (hausdorff n X) hX.quadratic K f.val f.val df df σ.toSignedMeasure) ∧
      ∀ᵐ x ∂(hausdorff n X).restrict S,
        (localHessianAction (hausdorff n X) hX.quadratic f.val g.val g.val FG FG GG x)^2 ≤
          (σ.rnDeriv (hausdorff n X) x).toReal*
            (localGamma (hausdorff n X) hX.quadratic g.val g.val x)^2 := by
  let := hX.separable
  let := locallyFinite_of_finiteOnBounded (hausdorff n X) hX.finiteOnBounded
  let μ := hausdorff n X
  let hQ := hX.quadratic
  obtain ⟨v,Q,hv,hvc,-,hvr⟩ := g.property.1
  let W : X →ᵇ ℝ := ofCompactSupport v hv.continuous hvc
  have hw : SobolevSpace.toLp μ hQ g.val =ᵐ[μ] W := hvr
  have hgb : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ g.val x|≤‖W‖₊ := by
    filter_upwards [hw] with x hx
    rw [hx]
    exact W.norm_coe_le_norm x
  let g₂ : compactLaplacianCore μ hQ V :=
    ⟨SobolevSpace.product μ hQ g.val g.val ‖W‖₊ ‖W‖₊,
      product_mem_compactLaplacianCore μ hQ g.property g.property ‖W‖₊ ‖W‖₊ hgb hgb⟩
  let u : Fin 3 → compactLaplacianCore μ hQ V := ![f,g,g₂]
  let U := sobolevColumnMap μ hQ (fun i => (u i).val)
  let e (i : Fin 3) : Euclidean 3 := EuclideanSpace.single i 1
  have hcol (i : Fin 3) : U (e i)=(u i).val := sobolevColumnMap_single μ hQ _ i
  have hf : U (e 0)=f.val := by simpa [u] using hcol 0
  have hg : U (e 1)=g.val := by simpa [u] using hcol 1
  have hz : U (e 2)=SobolevSpace.product μ hQ (U (e 1)) (U (e 1)) ‖W‖₊ ‖W‖₊ := by
    simpa [hg,u,g₂] using hcol 2
  obtain ⟨D,H,L,hU,M,hD,hH,hsym,hM⟩ := hX.regular_core_bochner_sobolev_measure hn p u hR
  change (∀ a, IsWeakLaplacian μ hQ (U a) (D a)) at hD
  change (∀ a b, SobolevSpace.toLp μ hQ (H a b) =ᵐ[μ] localGamma μ hQ (U a) (U b)) at hH
  have hq0 : D (e 0)=qf := IsWeakLaplacian.unique μ hQ (by simpa only [hf] using hD (e 0)) hqf
  have hq1 : D (e 1)=qg := IsWeakLaplacian.unique μ hQ (by simpa only [hg] using hD (e 1)) hqg
  have hs0 : D (e 0) =ᵐ[μ.restrict (ball p R)] SobolevSpace.toLp μ hQ df := by rw [hq0]; exact hsf
  have hs1 : D (e 1) =ᵐ[μ.restrict (ball p R)] SobolevSpace.toLp μ hQ dg := by rw [hq1]; exact hsg
  have hw' : SobolevSpace.toLp μ hQ (U (e 1)) =ᵐ[μ] W := by rw [hg]; exact hw
  have hgb' : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ (U (e 1)) x|≤‖W‖₊ := by rw [hg]; exact hgb
  have hL : ∀ᵐ x ∂μ, localGamma μ hQ (U (e 1)) (U (e 1)) x≤(L (e 1):ℝ)^2 := by
    filter_upwards [localGamma_self μ hQ (U (e 1)),hU (e 1),
      (Lp.coeFn_nonneg _).mpr (SobolevSpace.minimalSlope_nonneg μ hQ (U (e 1)))] with x he hb h0
    rw [he]
    exact pow_le_pow_left₀ h0 hb 2
  let dz := SobolevSpace.product μ hQ (U (e 1)) dg ‖W‖₊ B+
    SobolevSpace.product μ hQ (U (e 1)) dg ‖W‖₊ B+(2:ℝ) • H (e 1) (e 1)
  obtain ⟨q,hq,hqr⟩ := (hD (e 1)).square_local μ hQ (U (e 1)) (H (e 1) (e 1)) dg
    (D (e 1)) ‖W‖₊ B (L (e 1)) hgb' hdg hL (ae_restrict_of_ae (hH (e 1) (e 1))) hs1
  have hq2 : D (e 2)=q := IsWeakLaplacian.unique μ hQ (by simpa only [hz] using hD (e 2)) hq
  have hs2 : D (e 2) =ᵐ[μ.restrict (ball p R)] SobolevSpace.toLp μ hQ dz := by rw [hq2]; exact hqr
  let C : ℝ≥0 := 2*‖W‖₊*B+2*(L (e 1)*L (e 1))
  have hc : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ dz x|≤C := by
    simpa only [C,NNReal.coe_add,NNReal.coe_mul,NNReal.coe_ofNat] using
      squareLaplacianSource_bound μ hQ (U (e 1)) (H (e 1) (e 1)) dg ‖W‖₊ B
        (L (e 1)*L (e 1)) hgb' hdg (regularGram_abs_le μ hQ U H L hU hH (e 1) (e 1))
  obtain ⟨χ,hχΩ,hχ1⟩ := hX.exists_open_regular_cutoff hn isOpen_ball hS hsub
  let χb : X →ᵇ ℝ := ofCompactSupport χ.weight χ.lipschitz.continuous χ.compact
  have hbound := regularBochner_directional_bound μ hQ K U D H L hU hD hH hsym
    measurableSet_ball M hM (e 0) (e 1) (e 2) W hw' hz df dg dz A B C
    hdf hdg hc hs0 hs1 hs2 hS.measurableSet hsub χb χ.lipschitz χ.compact hχΩ
    (fun x => (χ.bounds x).1) hχ1
  have hlap := regularBochner_measure_laplacian μ hQ K U D H L hU hsym measurableSet_ball M hM
    (e 0) (e 0) df df (hH (e 0) (e 0)) (hD (e 0)) (hD (e 0)) hs0 hs0 A A hdf hdf
  refine ⟨H (e 0) (e 0),H (e 0) (e 1),H (e 1) (e 1),M.measure (e 0),inferInstance,?_,?_,?_,?_,?_⟩
  · simpa only [hf] using hH (e 0) (e 0)
  · simpa only [hf,hg] using hH (e 0) (e 1)
  · simpa only [hg] using hH (e 1) (e 1)
  · rw [M.measure_toSignedMeasure]
    change IsMeasureLaplacianOn μ hQ (ball p R) (H (e 0) (e 0))
      (bochnerGramSource μ hQ K (U (e 0)) (U (e 0)) df df (M.bilinear (e 0) (e 0))) at hlap
    rw [hf] at hlap
    exact hlap
  · have hRN := signed_rnDeriv_toSignedMeasure μ (M.measure (e 0))
    rw [M.measure_toSignedMeasure] at hRN
    filter_upwards [hbound,ae_restrict_of_ae hRN,
      ae_restrict_of_ae (bochnerRadonDensity_rep μ M (e 0) (e 0))] with x hb hrn hrep
    rw [← hrep,hrn] at hb
    simpa only [hf,hg] using hb

end RegularPointCoordinates

end

end OAI
