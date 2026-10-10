import OAI.Analysis.KadisonKastler.TraceHilbertActions
import Mathlib.Analysis.Normed.Operator.Extend

namespace OAI

/-! # Constructing tracial conjugation on a Hilbert completion

The adjoint operation is an isometry for a faithful trace. Its extension
to any dense trace-Hilbert realization is an involutive conjugate-linear
isometry; no standard-form conjugation is postulated.
-/

namespace KadisonKastler

noncomputable section

variable {A E : Type*} [CStarAlgebra A]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

private def starVectorMap (J : A →ₗ[ℂ] E) : A →ₗ⋆[ℂ] E :=
  J.comp (starLinearEquiv ℂ : A ≃ₗ⋆[ℂ] A).toLinearMap

/-- The adjoint map extends isometrically to the trace Hilbert space. -/
def tracialStarIsometry (τ : FaithfulTracialState A) (J : A →ₗ[ℂ] E)
    (hJ : ∀ a, ‖J a‖ = traceTwoNorm τ a) (hdense : DenseRange J) : E →ₗᵢ⋆[ℂ] E :=
  (starVectorMap J).extendOfIsometry hdense (fun a => by
    change ‖J (star a)‖ = ‖J a‖
    rw [hJ, hJ, traceTwoNorm_star])

@[simp]
theorem tracialStarIsometry_embedding (τ : FaithfulTracialState A) (J : A →ₗ[ℂ] E)
    (hJ : ∀ a, ‖J a‖ = traceTwoNorm τ a) (hdense : DenseRange J) (a : A) :
    tracialStarIsometry τ J hJ hdense (J a) = J (star a) :=
  LinearMap.extendOfIsometry_eq _ _ _ a

theorem tracialStarIsometry_involutive (τ : FaithfulTracialState A) (J : A →ₗ[ℂ] E)
    (hJ : ∀ a, ‖J a‖ = traceTwoNorm τ a) (hdense : DenseRange J) :
    Function.Involutive (tracialStarIsometry τ J hJ hdense) := by
  let T := tracialStarIsometry τ J hJ hdense
  have hT (a : A) : T (J a) = J (star a) := tracialStarIsometry_embedding τ J hJ hdense a
  have he : (fun ξ => T (T ξ)) = fun ξ => ξ :=
    hdense.equalizer (T.continuous.comp T.continuous) continuous_id (by
      funext a
      change T (T (J a)) = J a
      rw [hT, hT, star_star])
  exact fun ξ => congrFun he ξ

/-- The constructed involution, packaged as a conjugate-linear isometric
equivalence. -/
def tracialHilbertConjugation (τ : FaithfulTracialState A) (J : A →ₗ[ℂ] E)
    (hJ : ∀ a, ‖J a‖ = traceTwoNorm τ a) (hdense : DenseRange J) : E ≃ₗᵢ⋆[ℂ] E :=
  LinearIsometryEquiv.ofSurjective (tracialStarIsometry τ J hJ hdense)
    (tracialStarIsometry_involutive τ J hJ hdense).surjective

@[simp]
theorem tracialHilbertConjugation_embedding (τ : FaithfulTracialState A) (J : A →ₗ[ℂ] E)
    (hJ : ∀ a, ‖J a‖ = traceTwoNorm τ a) (hdense : DenseRange J) (a : A) :
    tracialHilbertConjugation τ J hJ hdense (J a) = J (star a) :=
  tracialStarIsometry_embedding τ J hJ hdense a

theorem tracialHilbertConjugation_involutive (τ : FaithfulTracialState A) (J : A →ₗ[ℂ] E)
    (hJ : ∀ a, ‖J a‖ = traceTwoNorm τ a) (hdense : DenseRange J) :
    Function.Involutive (tracialHilbertConjugation τ J hJ hdense) :=
  tracialStarIsometry_involutive τ J hJ hdense

end

end KadisonKastler

end OAI
