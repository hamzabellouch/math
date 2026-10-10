import OAI.Analysis.KadisonKastler.SignedCyclicFunctional

namespace OAI

/-! # Compression identities for signed vector functionals -/

namespace KadisonKastler

noncomputable section

open HochschildNormalPart
open scoped InnerProductSpace

variable {A H : Type*} [CStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem selfAdjoint_involution_norm (S : H →L[ℂ] H) (hS : IsSelfAdjoint S)
    (hSS : S * S = 1) (ξ : H) : ‖S ξ‖ = ‖ξ‖ := by
  have he : S (S ξ) = ξ := congrArg (fun T : H →L[ℂ] H => T ξ) hSS
  have hi : inner ℂ (S ξ) (S ξ) = inner ℂ ξ ξ := by
    rw [← ContinuousLinearMap.adjoint_inner_left, ← ContinuousLinearMap.star_eq_adjoint,
      hS.star_eq, he]
  have hn : ‖S ξ‖ ^ 2 = ‖ξ‖ ^ 2 := by
    calc
      ‖S ξ‖ ^ 2 = (inner ℂ (S ξ) (S ξ)).re :=
        (inner_self_eq_norm_sq (𝕜 := ℂ) _).symm
      _ = (inner ℂ ξ ξ).re := congrArg Complex.re hi
      _ = ‖ξ‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) _
  nlinarith [norm_nonneg (S ξ), norm_nonneg ξ]

def signedVectorFunctional (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (S : H →L[ℂ] H) (ξ : H) :
    A →L[ℂ] ℂ := coefficient π (S ξ) ξ

@[simp] theorem signedVectorFunctional_apply (π : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (S : H →L[ℂ] H) (ξ : H) (a : A) :
    signedVectorFunctional π S ξ a = inner ℂ (S ξ) (π a ξ) := rfl

theorem signedVectorFunctional_norm_le (π : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (S : H →L[ℂ] H) (hS : IsSelfAdjoint S) (hSS : S * S = 1) (ξ : H) :
    ‖signedVectorFunctional π S ξ‖ ≤ ‖ξ‖ ^ 2 := by
  simpa only [signedVectorFunctional, selfAdjoint_involution_norm S hS hSS ξ, pow_two]
    using coefficient_norm π (S ξ) ξ

theorem signedVectorFunctional_star (π : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (S : H →L[ℂ] H) (hS : IsSelfAdjoint S) (hcomm : ∀ a, Commute S (π a))
    (ξ : H) (a : A) :
    signedVectorFunctional π S ξ (star a) = star (signedVectorFunctional π S ξ a) := by
  have hc : S (π a ξ) = π a (S ξ) :=
    congrArg (fun T : H →L[ℂ] H => T ξ) (hcomm a).eq
  change inner ℂ (S ξ) (π (star a) ξ) = star (inner ℂ (S ξ) (π a ξ))
  calc
    inner ℂ (S ξ) (π (star a) ξ) = inner ℂ (π a (S ξ)) ξ := by
      rw [map_star, ContinuousLinearMap.star_eq_adjoint,
        ContinuousLinearMap.adjoint_inner_right]
    _ = inner ℂ (S (π a ξ)) ξ := by rw [hc]
    _ = inner ℂ (π a ξ) (S ξ) := by
      rw [← ContinuousLinearMap.adjoint_inner_left, ← ContinuousLinearMap.star_eq_adjoint,
        hS.star_eq]
    _ = star (inner ℂ (S ξ) (π a ξ)) := (inner_conj_symm _ _).symm

theorem signedVectorFunctional_projection (π : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (S p : H →L[ℂ] H) (hp : IsStarProjection p)
    (hSp : Commute p S) (hpp : ∀ a, Commute p (π a)) (ξ : H) (a : A) :
    signedVectorFunctional π S (p ξ) a = inner ℂ (S ξ) (π a (p ξ)) := by
  have hSpξ : S (p ξ) = p (S ξ) :=
    (congrArg (fun T : H →L[ℂ] H => T ξ) hSp.eq).symm
  have hppξ : p (π a (p ξ)) = π a (p ξ) := by
    have hc := congrArg (fun T : H →L[ℂ] H => T (p ξ)) (hpp a).eq
    change p (π a (p ξ)) = π a (p (p ξ)) at hc
    have he : p (p ξ) = p ξ :=
      congrArg (fun T : H →L[ℂ] H => T ξ) hp.isIdempotentElem.eq
    rwa [he] at hc
  change inner ℂ (S (p ξ)) (π a (p ξ)) = _
  have hi (u v : H) : inner ℂ (p u) v = inner ℂ u (p v) := by
    simpa only [← ContinuousLinearMap.star_eq_adjoint, hp.isSelfAdjoint.star_eq] using
      p.adjoint_inner_left v u
  rw [hSpξ, hi, hppξ]

theorem signedVectorFunctional_split_projection (π : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (S p : H →L[ℂ] H) (hp : IsStarProjection p)
    (hSp : Commute p S) (hpp : ∀ a, Commute p (π a)) (ξ : H) :
    signedVectorFunctional π S ξ = signedVectorFunctional π S (p ξ) +
      signedVectorFunctional π S ((1 - p) ξ) := by
  have hqS : Commute (1 - p) S := by
    change (1 - p) * S = S * (1 - p)
    rw [sub_mul, mul_sub, one_mul, mul_one, hSp.eq]
  have hqp (a : A) : Commute (1 - p) (π a) := by
    change (1 - p) * π a = π a * (1 - p)
    rw [sub_mul, mul_sub, one_mul, mul_one, (hpp a).eq]
  ext a
  rw [add_apply, signedVectorFunctional_projection π S p hp hSp hpp,
    signedVectorFunctional_projection π S (1 - p) hp.one_sub hqS hqp]
  change inner ℂ (S ξ) (π a ξ) = _
  rw [← inner_add_right, ← map_add]
  congr 2
  change ξ = p ξ + (ξ - p ξ)
  abel

theorem norm_sq_projection_add_complement (p : H →L[ℂ] H) (hp : IsStarProjection p)
    (ξ : H) : ‖p ξ‖ ^ 2 + ‖(1 - p) ξ‖ ^ 2 = ‖ξ‖ ^ 2 := by
  have hz : p * (1 - p) = 0 := by
    rw [mul_sub, mul_one, hp.isIdempotentElem.eq, sub_self]
  have hi : inner ℂ (p ξ) ((1 - p) ξ) = 0 := by
    calc
      inner ℂ (p ξ) ((1 - p) ξ) = inner ℂ ξ (p ((1 - p) ξ)) := by
        simpa only [← ContinuousLinearMap.star_eq_adjoint, hp.isSelfAdjoint.star_eq] using
          p.adjoint_inner_left ((1 - p) ξ) ξ
      _ = 0 := by
        have he : p ((1 - p) ξ) = 0 :=
          congrArg (fun T : H →L[ℂ] H => T ξ) hz
        rw [he, inner_zero_right]
  have he : p ξ + (1 - p) ξ = ξ := by
    change p ξ + (ξ - p ξ) = ξ
    abel
  have hn := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (p ξ) ((1 - p) ξ) hi
  rw [he] at hn
  simpa only [pow_two] using hn.symm

end

end KadisonKastler

end OAI
