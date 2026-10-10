import OAI.Geometry.RCD.Coordinates.RegularBochnerForm

namespace OAI

/-! # Positivity and Cauchy--Schwarz for the full regular Bochner form -/

open Set Filter MeasureTheory
open scoped NNReal BoundedContinuousFunction

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  {m : ℕ}

theorem NoncollapsedRCD.regularBochnerForm_nonneg {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2≤n) (p : X)
    (U : Euclidean m →L[ℝ] SobolevSpace (hausdorff n X) hX.quadratic)
    (D : Euclidean m →L[ℝ] Lp ℝ 2 (hausdorff n X))
    (H : Euclidean m →ₗ[ℝ] Euclidean m →ₗ[ℝ] SobolevSpace (hausdorff n X) hX.quadratic)
    (q : X →ᵇ ℝ) (ψ : SobolevSpace (hausdorff n X) hX.quadratic) (L : Euclidean m → ℝ≥0)
    (hU : ∀ a, ∀ᵐ x ∂hausdorff n X, SobolevSpace.minimalSlope (hausdorff n X) hX.quadratic (U a) x≤L a)
    (hq : 0≤q) (hψ : SobolevSpace.toLp (hausdorff n X) hX.quadratic ψ =ᵐ[hausdorff n X] q)
    (a : Euclidean m)
    (ha : ∃ (v : X → ℝ) (Q : ℝ≥0), LipschitzWith Q v ∧ HasCompactSupport v ∧
      SobolevSpace.toLp (hausdorff n X) hX.quadratic (U a) =ᵐ[hausdorff n X] v)
    (hd : IsWeakLaplacian (hausdorff n X) hX.quadratic (U a) (D a))
    (hH : SobolevSpace.toLp (hausdorff n X) hX.quadratic (H a a) =ᵐ[hausdorff n X]
      localGamma (hausdorff n X) hX.quadratic (U a) (U a)) :
    0≤regularBochnerForm (hausdorff n X) hX.quadratic K U D H q ψ L hU a a := by
  let μ := hausdorff n X
  obtain ⟨v,Q,hv,hvc,hav⟩ := ha
  have hb := hX.compact_bochner_sobolev_test hn hv hvc p (U a) hav (D a) hd (H a a) hH
    ψ q.continuous.measurable hψ ‖q‖₊ (fun x => q.norm_coe_le_norm x) (fun x => hq x)
  change 0≤bochnerTestForm μ hX.quadratic (-K) (H a a) ψ+
    weightedLaplacianPair μ q (D a) (D a)+
    (1/2 : ℝ)*(weightedGamma μ hX.quadratic (D a) (U a) ψ+
      weightedGamma μ hX.quadratic (D a) (U a) ψ)
  rw [bochnerTestForm_apply,weightedLaplacianPair_apply]
  have heq : (∫ x, q x*D a x*D a x ∂μ) = ∫ x, q x*(D a x)^2 ∂μ := by
    congr 1
    funext x
    ring
  rw [heq]
  nlinarith only [hb]

end RegularPointCoordinates

end

end OAI
