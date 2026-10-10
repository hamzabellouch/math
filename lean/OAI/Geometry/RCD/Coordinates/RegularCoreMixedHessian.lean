import OAI.Geometry.RCD.Coordinates.RegularCoreWeakMeasure
import OAI.Geometry.RCD.Coordinates.HessianCoordinateForm
import OAI.Geometry.RCD.Sobolev.SymmetricGammaForm
import OAI.Geometry.RCD.Coordinates.FiniteBilinearAE

namespace OAI

/-! # Mixed shifted actions for arbitrary members of the regular core

The direction functions require only their actual L² weak Laplacians.
Diagonal estimates are transferred to one fixed Sobolev Gram family and
polarized outside a common null set.
-/

open Set Filter Metric MeasureTheory
open scoped NNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- Scalar dimensional Bochner gives the mixed Hessian estimate on any
finite regular family, for the prescribed full Bochner measure. -/
theorem NoncollapsedRCD.regular_core_mixed_hessian_on_measure {K : ℝ} {n m : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2≤n)
    (hscalar : ScalarDimensionalBochner (hausdorff n X) hX.quadratic K n)
    {V : Set X} (u : Fin m → compactLaplacianCore (hausdorff n X) hX.quadratic V)
    (p : X) {R : ℝ} (hR : 0<R) {S : Set X} (hS : IsCompact S) (hsub : S ⊆ ball p R)
    (a : Euclidean m) (df : SobolevSpace (hausdorff n X) hX.quadratic)
    (qf : Lp ℝ 2 (hausdorff n X))
    (hqf : IsWeakLaplacian (hausdorff n X) hX.quadratic
      (sobolevColumnMap (hausdorff n X) hX.quadratic (fun i => (u i).val) a) qf)
    (C : ℝ≥0) (hdf : ∀ᵐ x ∂hausdorff n X, |SobolevSpace.toLp (hausdorff n X) hX.quadratic df x|≤C)
    (hsf : qf =ᵐ[(hausdorff n X).restrict (ball p R)] SobolevSpace.toLp (hausdorff n X) hX.quadratic df)
    {J : ℝ} (hJK : J≤K)
    (F₀ : SobolevSpace (hausdorff n X) hX.quadratic) (σ : Measure X) [IsFiniteMeasure σ]
    (hF₀ : SobolevSpace.toLp (hausdorff n X) hX.quadratic F₀
      =ᵐ[(hausdorff n X).restrict (ball p R)]
        localGamma (hausdorff n X) hX.quadratic
          (sobolevColumnMap (hausdorff n X) hX.quadratic (fun i => (u i).val) a)
          (sobolevColumnMap (hausdorff n X) hX.quadratic (fun i => (u i).val) a))
    (hσ : IsMeasureLaplacianOn (hausdorff n X) hX.quadratic (ball p R) F₀
      (bochnerGramSource (hausdorff n X) hX.quadratic J
        (sobolevColumnMap (hausdorff n X) hX.quadratic (fun i => (u i).val) a)
        (sobolevColumnMap (hausdorff n X) hX.quadratic (fun i => (u i).val) a) df df σ.toSignedMeasure)) :
    let U := sobolevColumnMap (hausdorff n X) hX.quadratic (fun i => (u i).val)
    ∃ H : Euclidean m →ₗ[ℝ] Euclidean m →ₗ[ℝ] SobolevSpace (hausdorff n X) hX.quadratic,
      (∀ v w, H v w=H w v) ∧
      (∀ v w, SobolevSpace.toLp (hausdorff n X) hX.quadratic (H v w)
        =ᵐ[hausdorff n X] localGamma (hausdorff n X) hX.quadratic (U v) (U w)) ∧
      (∀ᵐ x ∂(hausdorff n X).restrict S,
        (SobolevSpace.toLp (hausdorff n X) hX.quadratic df x)^2≤
          (n:ℝ)*(σ.rnDeriv (hausdorff n X) x).toReal) ∧
      ∀ (b : ℝ) v w, ∀ᵐ x ∂(hausdorff n X).restrict S,
        (localHessianAction (hausdorff n X) hX.quadratic (U a) (U v) (U w)
          (H a v) (H a w) (H v w) x-b*localGamma (hausdorff n X) hX.quadratic (U v) (U w) x)^2 ≤
        ((σ.rnDeriv (hausdorff n X) x).toReal-
          2*b*SobolevSpace.toLp (hausdorff n X) hX.quadratic df x+(n:ℝ)*b^2)*
          localGamma (hausdorff n X) hX.quadratic (U v) (U v) x*
          localGamma (hausdorff n X) hX.quadratic (U w) (U w) x := by
  classical
  let := hX.separable
  let := locallyFinite_of_finiteOnBounded (hausdorff n X) hX.finiteOnBounded
  let μ := hausdorff n X
  let hQ := hX.quadratic
  let U := sobolevColumnMap μ hQ (fun i => (u i).val)
  have hmem (v : Euclidean m) : U v ∈ compactLaplacianCore μ hQ V := by
    rw [sobolevColumnMap_apply]
    exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (u i).property)
  let core (v : Euclidean m) : compactLaplacianCore μ hQ V := ⟨U v,hmem v⟩
  obtain ⟨_D,H,_L,_hU,_hc,_hD,hH,hsym⟩ := hX.regular_finite_span hn p u
  have hget (v : Euclidean m) := hX.regular_core_weak_hessian_on_measure hn hscalar
    (core a) (core v) p hR hS hsub df qf hqf C hdf hsf hJK F₀ σ hF₀ hσ
  choose FG GG hFG hGG hdim hbound using hget
  have hFG' (v : Euclidean m) : FG v=H a v := by
    apply Subtype.ext
    apply Lp.ext
    exact (hFG v).trans (hH a v).symm
  have hGG' (v : Euclidean m) : GG v=H v v := by
    apply Subtype.ext
    apply Lp.ext
    exact (hGG v).trans (hH v v).symm
  refine ⟨H,hsym,hH,hdim 0,?_⟩
  intro b
  let A := (H a).toContinuousLinearMap
  let P := symmetricGammaForm μ hQ U
  let B := fun x => hessianCoordinateForm μ hQ (U a) U A H x-b • P x
  let c := fun x => (σ.rnDeriv μ x).toReal-2*b*SobolevSpace.toLp μ hQ df x+(n:ℝ)*b^2
  have hn0 : 0<(n:ℝ) := by exact_mod_cast (by omega : 0<n)
  have hc : ∀ᵐ x ∂μ.restrict S, 0≤c x := by
    filter_upwards [hdim 0] with x hx
    have hp : 0≤(n:ℝ)*c x := by
      dsimp only [c]
      nlinarith only [hx,sq_nonneg (SobolevSpace.toLp μ hQ df x-(n:ℝ)*b)]
    exact (mul_nonneg_iff_of_pos_left hn0).mp hp
  have hb (v : Euclidean m) : ∀ᵐ x ∂μ.restrict S, (B x v v)^2≤c x*(P x v v)^2 := by
    have h := hbound v b
    rw [hFG' v,hGG' v] at h
    filter_upwards [h,ae_restrict_of_ae (hessianCoordinateForm_rep μ hQ (U a) U A H v v),
      ae_restrict_of_ae (symmetricGammaForm_rep μ hQ U v v)] with x hx hH hP
    change localHessianAction μ hQ (U a) (U v) (U v) (H a v) (H a v) (H v v) x=_ at hH
    change (hessianCoordinateForm μ hQ (U a) U A H x v v-b*P x v v)^2≤_
    rw [← hH,← hP]
    exact hx
  have hBs (x : X) (v w : Euclidean m) : B x v w=B x w v := by
    change _-b*P x v w=_-b*P x w v
    rw [hessianCoordinateForm_symmetric μ hQ (U a) U A H hsym,
      symmetricGammaForm_symmetric μ hQ U]
  have hall := ae_bilinear_mixed_bound_of_diagonal (μ.restrict S) P B c
    (symmetricGammaForm_symmetric μ hQ U) hBs
    (fun v => ae_restrict_of_ae (symmetricGammaForm_nonneg μ hQ U v)) hc hb
  intro v w
  filter_upwards [hall,ae_restrict_of_ae (hessianCoordinateForm_rep μ hQ (U a) U A H v w),
    ae_restrict_of_ae (symmetricGammaForm_rep μ hQ U v w),
    ae_restrict_of_ae (symmetricGammaForm_rep μ hQ U v v),
    ae_restrict_of_ae (symmetricGammaForm_rep μ hQ U w w)] with x hx hH hP hv hw
  have he := hx v w
  change (hessianCoordinateForm μ hQ (U a) U A H x v w-b*P x v w)^2≤c x*P x v v*P x w w at he
  rw [← hH,← hP,← hv,← hw] at he
  exact he

end RegularPointCoordinates

end

end OAI
