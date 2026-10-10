import OAI.Geometry.RCD.Coordinates.RegularCoreMixedHessian
import OAI.Geometry.RCD.Metric.RationalInteriorBalls
import OAI.Geometry.RCD.Coordinates.HessianCoordinateForm
import OAI.Geometry.RCD.Sobolev.SymmetricGammaForm
import OAI.Geometry.RCD.Coordinates.FiniteBilinearAE

namespace OAI

/-! # A common mixed Hessian estimate on the full working ball

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
theorem NoncollapsedRCD.regular_core_mixed_hessian_full_ball {K : ℝ} {n m : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2≤n)
    (hscalar : ScalarDimensionalBochner (hausdorff n X) hX.quadratic K n)
    {V : Set X} (u : Fin m → compactLaplacianCore (hausdorff n X) hX.quadratic V)
    (p : X) {R : ℝ} (hR : 0<R)
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
      (∀ᵐ x ∂(hausdorff n X).restrict (ball p R),
        (SobolevSpace.toLp (hausdorff n X) hX.quadratic df x)^2≤
          (n:ℝ)*(σ.rnDeriv (hausdorff n X) x).toReal) ∧
      ∀ (b : ℝ) v w, ∀ᵐ x ∂(hausdorff n X).restrict (ball p R),
        (localHessianAction (hausdorff n X) hX.quadratic (U a) (U v) (U w)
          (H a v) (H a w) (H v w) x-b*localGamma (hausdorff n X) hX.quadratic (U v) (U w) x)^2 ≤
        ((σ.rnDeriv (hausdorff n X) x).toReal-
          2*b*SobolevSpace.toLp (hausdorff n X) hX.quadratic df x+(n:ℝ)*b^2)*
          localGamma (hausdorff n X) hX.quadratic (U v) (U v) x*
          localGamma (hausdorff n X) hX.quadratic (U w) (U w) x := by
  let μ := hausdorff n X
  let hQ := hX.quadratic
  let U := sobolevColumnMap μ hQ (fun i => (u i).val)
  obtain ⟨H,hsym,hH,-,-⟩ := hX.regular_core_mixed_hessian_on_measure hn hscalar u p hR
    (S := ∅) isCompact_empty (empty_subset _) a df qf hqf C hdf hsf hJK F₀ σ hF₀ hσ
  have hclosed (t : ℝ) (ht : t<R) :
      (∀ᵐ x ∂μ.restrict (closedBall p t),
        (SobolevSpace.toLp μ hQ df x)^2≤(n:ℝ)*(σ.rnDeriv μ x).toReal) ∧
      ∀ (b : ℝ) v w, ∀ᵐ x ∂μ.restrict (closedBall p t),
        (localHessianAction μ hQ (U a) (U v) (U w) (H a v) (H a w) (H v w) x-
          b*localGamma μ hQ (U v) (U w) x)^2 ≤
        ((σ.rnDeriv μ x).toReal-2*b*SobolevSpace.toLp μ hQ df x+(n:ℝ)*b^2)*
          localGamma μ hQ (U v) (U v) x*localGamma μ hQ (U w) (U w) x := by
    obtain ⟨H',-,hH',hdim,hb⟩ := hX.regular_core_mixed_hessian_on_measure hn hscalar u p hR
      (isCompact_closedBall p t) (closedBall_subset_ball ht) a df qf hqf C hdf hsf hJK F₀ σ hF₀ hσ
    have he : H'=H := by
      ext v w
      apply Subtype.ext
      apply Lp.ext
      exact (hH' v w).trans (hH v w).symm
    rw [he] at hb
    exact ⟨hdim,hb⟩
  refine ⟨H,hsym,hH,?_,?_⟩
  · rw [ball_eq_iUnion_rational_closedBall p R]
    apply (ae_restrict_iUnion_iff _ _).mpr
    intro q
    exact (hclosed q.val q.property).1
  · intro b v w
    rw [ball_eq_iUnion_rational_closedBall p R]
    apply (ae_restrict_iUnion_iff _ _).mpr
    intro q
    exact (hclosed q.val q.property).2 b v w

end RegularPointCoordinates

end

end OAI
