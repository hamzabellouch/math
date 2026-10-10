import OAI.Analysis.KadisonSimilarity.Representation.IntertwinerExtension
import Mathlib.MeasureTheory.Function.L2Space

namespace OAI

/-! # Coordinates from two isometric embeddings with the same range -/

namespace KadisonKastler

open MeasureTheory KadisonSimilarity

noncomputable section

variable {E F K : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem isometry_adjoint_self_apply (J : E →ₗᵢ[ℂ] K) (v : E) :
    J.toContinuousLinearMap.adjoint (J v) = v :=
  congrArg (fun T : E →L[ℂ] E => T v) J.adjoint_comp_self

/-- The adjoint of the second embedding gives coordinates for the first. -/
def isometryRangeCoordinates (J : E →ₗᵢ[ℂ] K) (W : F →ₗᵢ[ℂ] K)
    (h : LinearMap.range J.toLinearMap = LinearMap.range W.toLinearMap) : E ≃ₗᵢ[ℂ] F := by
  let T : E →ₗᵢ[ℂ] F := {
    toLinearMap := (W.toContinuousLinearMap.adjoint.comp J.toContinuousLinearMap).toLinearMap
    norm_map' := by
      intro v
      obtain ⟨w, hw⟩ := show J v ∈ LinearMap.range W.toLinearMap from h ▸ ⟨v, rfl⟩
      have hw' : W w = J v := hw
      change ‖W.toContinuousLinearMap.adjoint (J v)‖ = ‖v‖
      rw [← hw', isometry_adjoint_self_apply]
      exact (W.norm_map w).symm.trans ((congrArg norm hw').trans (J.norm_map v)) }
  apply LinearIsometryEquiv.ofSurjective T
  intro w
  obtain ⟨v, hv⟩ := show W w ∈ LinearMap.range J.toLinearMap from h.symm ▸ ⟨w, rfl⟩
  refine ⟨v, ?_⟩
  have hv' : J v = W w := hv
  change W.toContinuousLinearMap.adjoint (J v) = w
  rw [hv', isometry_adjoint_self_apply]

omit [CompleteSpace E] in
@[simp] theorem isometryRangeCoordinates_apply (J : E →ₗᵢ[ℂ] K) (W : F →ₗᵢ[ℂ] K)
    (h : LinearMap.range J.toLinearMap = LinearMap.range W.toLinearMap) (v : E) :
    isometryRangeCoordinates J W h v = W.toContinuousLinearMap.adjoint (J v) := rfl

omit [CompleteSpace E] in
theorem isometryRangeCoordinates_intertwines (J : E →ₗᵢ[ℂ] K) (W : F →ₗᵢ[ℂ] K)
    (h : LinearMap.range J.toLinearMap = LinearMap.range W.toLinearMap) (v : E) :
    W (isometryRangeCoordinates J W h v) = J v := by
  obtain ⟨w, hw⟩ := show J v ∈ LinearMap.range W.toLinearMap from h ▸ ⟨v, rfl⟩
  have hw' : W w = J v := hw
  rw [isometryRangeCoordinates_apply, ← hw', isometry_adjoint_self_apply]

variable {X H : Type*} [MeasurableSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (μ : Measure X) (J : E →ₗᵢ[ℂ] Lp H 2 μ) (P : X → H →L[ℂ] H)

theorem isometry_range_iff_field_fixed
    (hJ : ∀ f : Lp H 2 μ, isometricExtension J 1 f =ᵐ[μ] fun x => P x (f x))
    (f : Lp H 2 μ) :
    f ∈ LinearMap.range J.toLinearMap ↔ ∀ᵐ x ∂μ, P x (f x) = f x := by
  constructor
  · rintro ⟨v, rfl⟩
    have he : isometricExtension J 1 (J v) = J v := by
      simpa using isometricExtension_on_range J 1 v
    filter_upwards [hJ (J v)] with x hx
    rw [he] at hx
    exact hx.symm
  · intro hf
    refine ⟨J.toContinuousLinearMap.adjoint f, ?_⟩
    apply Lp.ext
    filter_upwards [hJ f, hf] with x hJx hx
    exact hJx.trans hx

end

end KadisonKastler

end OAI
