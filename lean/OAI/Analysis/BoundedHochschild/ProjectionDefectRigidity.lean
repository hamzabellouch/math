import OAI.Analysis.BoundedHochschild.MinimalProjectionNorms
import OAI.Analysis.BoundedHochschild.ProjectionNormGap
import OAI.Analysis.BoundedHochschild.PositiveProjectionGap
import OAI.Analysis.BoundedHochschild.RepresentedPositiveGap
import OAI.Analysis.BoundedHochschild.FactorizedProjectionDefects

namespace OAI

/-! In the minimal averaging family, an algebra-valued projection defect must
vanish: a nonzero defect would give a positive spectral gap contradicting
the projection-compression norm identity. -/

noncomputable section

namespace BoundedHochschild.KadisonRingrose

universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem projection_defect_eq_zero (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (π : M →⋆ₐ[ℂ] (K →L[ℂ] K)) (L W : NormalGNS e →L[ℂ] K)
    (T : M →L[ℂ] M)
    (hT : ∀ a, normalGNSRepresentation e (T a) = L.adjoint.comp ((π a).comp W))
    (hnorm : ∀ f : M, IsStarProjection f →
      ‖W.comp (normalGNSRepresentation e f)‖ =
        ‖(π f).comp (W.comp (normalGNSRepresentation e f))‖)
    (a : M) {p : M} (hp : IsStarProjection p) : T a * p - T (a * p) * p = 0 := by
  let σ := normalGNSRepresentation e
  let b := T a * p - T (a * p) * p
  by_contra hb
  have hbb : star b * b ≠ 0 := (CStarRing.star_mul_self_ne_zero_iff b).mpr hb
  obtain ⟨f, hf, hf0, δ, hδ, hgap⟩ := exists_positive_projection_gap e
    (star_mul_self_nonneg b) hbb
  have hbp : b * (1 - p) = 0 := by
    dsimp [b]
    rw [sub_mul, mul_assoc, hp.mul_one_sub_self, mul_assoc, hp.mul_one_sub_self,
      mul_zero, mul_zero, sub_self]
  have hfp : f ≤ p := projection_le_of_positive_gap hf hp hδ hgap
    (by rw [mul_assoc, hbp, mul_zero])
  have hσf0 : σ f ≠ 0 := by
    intro h
    exact hf0 ((normalGNSRepresentation_injective e) (h.trans (map_zero σ).symm))
  have hff : (W.comp (σ f)).comp (σ f) = W.comp (σ f) := by
    rw [ContinuousLinearMap.comp_assoc]
    have he : (σ f).comp (σ f) = σ f := by
      change σ f * σ f = σ f
      rw [← map_mul, hf.isIdempotentElem.eq]
    rw [he]
  have hnormp : ‖(π p).comp (W.comp (σ f))‖ = ‖W.comp (σ f)‖ := by
    apply projection_compression_norm_of_le (π p) (π f) (hp.map π) (hf.map π)
    · change π f * π p = π f
      rw [← map_mul, (hf.le_iff_mul_eq_left hp).mp hfp]
    · exact hnorm f hf
  apply no_positive_offDiagonal_gap (W.comp (σ f)) (π p) (σ f) (L.adjoint.comp (π a))
    (hp.map π) (hf.map σ) hσf0 hff hnormp hδ
  intro ξ
  have hg := represented_positive_gap σ hf hgap ξ
  have he := factorized_projection_defect π σ L W T hT a hp hf hfp
  have hv := congrArg (fun A : NormalGNS e →L[ℂ] NormalGNS e => A ξ) he
  change σ b (σ f ξ) = (L.adjoint.comp (π a))
    ((1 - π p) ((W.comp (σ f)) ξ)) at hv
  rwa [← hv]

end BoundedHochschild.KadisonRingrose

end

end OAI
