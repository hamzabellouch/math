import OAI.Geometry.RCD.Coordinates.RegularFiniteSpan

namespace OAI

/-! # Full Bochner measures constructed for the regular test algebra -/

open Set Metric MeasureTheory
open scoped NNReal BoundedContinuousFunction

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- A finite collection of actual regular tests determines a single
positive bilinear Bochner measure, with the exact weak test identity. -/
theorem NoncollapsedRCD.regular_core_bochner_sobolev_measure {K : ℝ} {n m : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2≤n) (p : X)
    {Ω : Set X} (u : Fin m → compactLaplacianCore (hausdorff n X) hX.quadratic Ω)
    {r : ℝ} (hr : 0<r) :
    let U := sobolevColumnMap (hausdorff n X) hX.quadratic (fun i => (u i).val)
    ∃ (D : Euclidean m →L[ℝ] Lp ℝ 2 (hausdorff n X))
      (H : Euclidean m →ₗ[ℝ] Euclidean m →ₗ[ℝ] SobolevSpace (hausdorff n X) hX.quadratic)
      (L : Euclidean m → ℝ≥0)
      (hU : ∀ a, ∀ᵐ x ∂hausdorff n X, SobolevSpace.minimalSlope (hausdorff n X) hX.quadratic (U a) x≤L a)
      (M : PositiveBilinearMeasure X (Euclidean m)),
      (∀ a, IsWeakLaplacian (hausdorff n X) hX.quadratic (U a) (D a)) ∧
      (∀ a b, SobolevSpace.toLp (hausdorff n X) hX.quadratic (H a b) =ᵐ[hausdorff n X]
        localGamma (hausdorff n X) hX.quadratic (U a) (U b)) ∧
      (∀ a b, H a b=H b a) ∧
      (∀ (a : Euclidean m) (ψ : SobolevSpace (hausdorff n X) hX.quadratic)
        (q : X →ᵇ ℝ), HasCompactSupport (q : X → ℝ) →
        tsupport q ⊆ ball p r → SobolevSpace.toLp (hausdorff n X) hX.quadratic ψ =ᵐ[hausdorff n X] q →
        (∫ x, q x ∂M.measure a) =
          regularBochnerForm (hausdorff n X) hX.quadratic K U D H q ψ L hU a a) := by
  dsimp only
  obtain ⟨D,H,L,hU,hc,hD,hH,hsym⟩ := hX.regular_finite_span hn p u
  obtain ⟨M,hM⟩ := hX.regular_span_bochner_sobolev_measure hn p hr _ D H L hU hc hD
    (fun a => hH a a) hsym
  exact ⟨D,H,L,hU,M,hD,hH,hsym,fun a ψ q => hM a ψ q q.continuous⟩


/-- The Lipschitz test specialization, preserving the original interface. -/
theorem NoncollapsedRCD.regular_core_bochner_measure {K : ℝ} {n m : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2≤n) (p : X)
    {Ω : Set X} (u : Fin m → compactLaplacianCore (hausdorff n X) hX.quadratic Ω)
    {r : ℝ} (hr : 0<r) :
    let U := sobolevColumnMap (hausdorff n X) hX.quadratic (fun i => (u i).val)
    ∃ (D : Euclidean m →L[ℝ] Lp ℝ 2 (hausdorff n X))
      (H : Euclidean m →ₗ[ℝ] Euclidean m →ₗ[ℝ] SobolevSpace (hausdorff n X) hX.quadratic)
      (L : Euclidean m → ℝ≥0)
      (hU : ∀ a, ∀ᵐ x ∂hausdorff n X, SobolevSpace.minimalSlope (hausdorff n X) hX.quadratic (U a) x≤L a)
      (M : PositiveBilinearMeasure X (Euclidean m)),
      (∀ a, IsWeakLaplacian (hausdorff n X) hX.quadratic (U a) (D a)) ∧
      (∀ a b, SobolevSpace.toLp (hausdorff n X) hX.quadratic (H a b) =ᵐ[hausdorff n X]
        localGamma (hausdorff n X) hX.quadratic (U a) (U b)) ∧
      (∀ a b, H a b=H b a) ∧
      (∀ (a : Euclidean m) (ψ : SobolevSpace (hausdorff n X) hX.quadratic)
        (q : X →ᵇ ℝ) (C : ℝ≥0), LipschitzWith C q → HasCompactSupport (q : X → ℝ) →
        tsupport q ⊆ ball p r → SobolevSpace.toLp (hausdorff n X) hX.quadratic ψ =ᵐ[hausdorff n X] q →
        (∫ x, q x ∂M.measure a) =
          regularBochnerForm (hausdorff n X) hX.quadratic K U D H q ψ L hU a a) := by
  obtain ⟨D,H,L,hU,M,hD,hH,hsym,hM⟩ := hX.regular_core_bochner_sobolev_measure hn p u hr
  exact ⟨D,H,L,hU,M,hD,hH,hsym,fun a ψ q _ _ => hM a ψ q⟩

end RegularPointCoordinates

end

end OAI
