import OAI.Geometry.SurfaceImmersion.Atlas.SupportedCoordinateChange

namespace OAI

/-! Isometric coordinate transport on the open domains used by the local
polynomial estimates. -/
noncomputable section
open scoped ContDiff
namespace ClosedSurfaceR4.JetPolynomial
open WeightedEstimates

lemma weightedBound_comp_isometry_on {A B F : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (e : A ≃ₗᵢ[ℝ] B) {U : Set B} (hU : IsOpen U) {f : B → F}
    (hf : ContDiff ℝ ∞ f) {s C : ℝ} {m : ℕ}
    (hb : WeightedBound U s m C f) :
    WeightedBound (e ⁻¹' U) s m C (f ∘ e) := by
  intro j hj x hx
  rw [iteratedFDerivWithin_of_isOpen j (hU.preimage e.continuous) hx]
  change s ^ j * ‖iteratedFDeriv ℝ j
    (f ∘ (e.toContinuousLinearEquiv.toContinuousLinearMap : A → B)) x‖ ≤ C
  rw [e.toContinuousLinearEquiv.toContinuousLinearMap.iteratedFDeriv_comp_right hf x (by simp),
    ContinuousMultilinearMap.norm_compContinuous_linearIsometryEquiv]
  change s ^ j * ‖iteratedFDeriv ℝ j f (e x)‖ ≤ C
  have hh := hb j hj (e x) hx
  rw [iteratedFDerivWithin_of_isOpen j hU hx] at hh
  exact hh

end ClosedSurfaceR4.JetPolynomial

end

end OAI
