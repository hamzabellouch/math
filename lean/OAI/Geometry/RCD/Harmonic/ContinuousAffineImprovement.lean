import OAI.Geometry.RCD.Harmonic.AffineImprovementTransfer
import OAI.Geometry.RCD.Coordinates.LocalCoordinateExtension

namespace OAI

/-! # Uniform affine improvement for continuous local harmonic coordinates -/

open Set Metric MeasureTheory
open scoped ENNReal InnerProductSpace

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- The normalized harmonic estimate in the original affine coordinate span. -/
def HasNormalizedAffineImprovement {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
    (u : Fin n → SobolevSpace (hausdorff n X) hX.quadratic)
    (p : X) (r θ : ℝ) : Prop :=
  ∀ w : SobolevSpace (hausdorff n X) hX.quadratic,
    IsSobolevHarmonicOn (hausdorff n X) hX.quadratic (ball p r) w →
    ‖normalizeLocalL2 (hausdorff n X) (ball p r)
      (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
      (SobolevSpace.restrictLp (hausdorff n X) hX.quadratic (ball p r) w)‖ ≤ 1 →
    ‖normalizeLocalL2 (hausdorff n X) (ball p (θ * r))
      (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
      (affineResidual (hausdorff n X) hX.quadratic u (ball p (θ * r))
        (ne_of_lt (hX.finiteOnBounded _ isBounded_ball))
        (SobolevSpace.restrictLp (hausdorff n X) hX.quadratic (ball p (θ * r)) w))‖ <
      (1 / 2 : ℝ) * θ * Real.sqrt θ

theorem affine_improvement_from_continuous_coordinates [ProperSpace X]
    {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X) (hn : 2 ≤ n)
    (hcompact : LocalHarmonicMomentCompactnessInput hX)
    (hgradient : LocalHarmonicL2GradientInput hX)
    (heuclidean : EuclideanHarmonicHessianInput n)
    (hmeasured : LocalMeasuredCoordinateInput hX) :
    ∃ m : ℕ, 3 ≤ m ∧ ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧
      ∀ (p : X) (r : ℝ), 0 < r → -δ ≤ K * r ^ 2 →
      ∀ (u : Fin n → SobolevSpace (hausdorff n X) hX.quadratic)
        (v : X → Euclidean n),
        (∀ i, SobolevSpace.toLp (hausdorff n X) hX.quadratic (u i) =ᵐ[
          (hausdorff n X).restrict (ball p r)] fun x => v x i) →
        ContinuousOn v (ball p (4 * r)) →
      ∀ (B : Euclidean n ≃L[ℝ] Euclidean n)
        (η : SobolevSpace (hausdorff n X) hX.quadratic),
        (SobolevSpace.toLp (hausdorff n X) hX.quadratic η =ᵐ[
          (hausdorff n X).restrict (ball p r)] fun _ => (1 : ℝ)) →
        IsPointedApproximation p 0 r 2 δ (fun x =>
          (B : Euclidean n →L[ℝ] Euclidean n).adjoint (v x) -
          (B : Euclidean n →L[ℝ] Euclidean n).adjoint (v p)) →
        HasNormalizedAffineImprovement hX u p r ((1 / 2 : ℝ) ^ m) := by
  obtain ⟨m, hm, δ, hδ, hδ1, hfit⟩ := affine_improvement_from_metric_coordinates
    hX hn hcompact hgradient heuclidean hmeasured
  refine ⟨m, hm, δ, hδ, hδ1, ?_⟩
  intro p r hr hcurv u v hrep hv B η hη happ
  obtain ⟨v', hv', heq⟩ := exists_measurable_local_extension measurableSet_ball hv
  have hp : p ∈ ball p (4 * r) := mem_ball_self (by positivity)
  have hsub : ball p r ⊆ ball p (4 * r) := ball_subset_ball (by linarith)
  have hrep' (i : Fin n) : SobolevSpace.toLp (hausdorff n X) hX.quadratic (u i) =ᵐ[
      (hausdorff n X).restrict (ball p r)] fun x => v' x i := by
    filter_upwards [hrep i, ae_restrict_mem measurableSet_ball] with x hx hxs
    rw [← heq (hsub hxs)]
    exact hx
  have hmeas : Measurable (fun x => (B : Euclidean n →L[ℝ] Euclidean n).adjoint (v' x) -
      (B : Euclidean n →L[ℝ] Euclidean n).adjoint (v' p)) :=
    ((B : Euclidean n →L[ℝ] Euclidean n).adjoint.continuous.measurable.comp hv').sub measurable_const
  have happ' : IsPointedApproximation p 0 r 2 δ (fun x =>
      (B : Euclidean n →L[ℝ] Euclidean n).adjoint (v' x) -
      (B : Euclidean n →L[ℝ] Euclidean n).adjoint (v' p)) := by
    apply happ.congr_on_ball (by positivity)
    intro x hx
    have hx' : x ∈ ball p (4 * r) := by
      change dist x p < 4 * r
      exact lt_of_le_of_lt (show dist x p ≤ 2 * r from hx) (by linarith)
    exact congrArg₂ (fun a b =>
      (B : Euclidean n →L[ℝ] Euclidean n).adjoint a -
        (B : Euclidean n →L[ℝ] Euclidean n).adjoint b) (heq hx') (heq hp)
  exact hfit p r hr hcurv u v' hrep' B η hη hmeas happ'

end RegularPointCoordinates

end

end OAI
