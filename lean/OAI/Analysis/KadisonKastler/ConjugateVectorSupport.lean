import OAI.Analysis.KadisonKastler.VectorSupportProjection

namespace OAI

/-! # Conjugate supports of a symmetric vector

For a conjugation interchanging an algebra and its commutant, the two
support projections of a fixed vector are conjugate. This is the support
identity used when passing the central-vector construction to a full corner.
-/

namespace KadisonKastler

open Generator Generator.Tracial

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def conjugateAlgebraProjection (M N : VonNeumannAlgebra H)
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hMN : ∀ a : Algebra M, conjugationOperator J a.val ∈ N)
    (p : AlgebraProjection M) : AlgebraProjection N :=
  ⟨⟨conjugationOperator J p.val.val, hMN p.val⟩, by
    constructor
    · apply Subtype.ext
      change conjugationOperator J p.val.val * conjugationOperator J p.val.val =
        conjugationOperator J p.val.val
      rw [← conjugationOperator_mul J hJ]
      exact congrArg (fun a : Algebra M => conjugationOperator J a.val)
        p.property.isIdempotentElem.eq
    · apply Subtype.ext
      change star (conjugationOperator J p.val.val) = conjugationOperator J p.val.val
      rw [← conjugationOperator_star J hJ]
      exact congrArg (fun a : Algebra M => conjugationOperator J a.val)
        p.property.isSelfAdjoint.star_eq⟩

theorem conjugateAlgebraProjection_fixes (M N : VonNeumannAlgebra H)
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hMN : ∀ a : Algebra M, conjugationOperator J a.val ∈ N)
    (p : AlgebraProjection M) (ξ : H) (hξ : J ξ = ξ) (hp : p.val.val ξ = ξ) :
    (conjugateAlgebraProjection M N J hJ hMN p).val.val ξ = ξ := by
  change J (p.val.val (J ξ)) = ξ
  rw [hξ,hp,hξ]

theorem vectorSupportProjection_conjugate (M : VonNeumannAlgebra H)
    (J : H ≃ₗᵢ⋆[ℂ] H) (hJ : Function.Involutive J)
    (hleft : ∀ a : Algebra M, conjugationOperator J a.val ∈ M.commutant)
    (hright : ∀ a : Algebra M.commutant, conjugationOperator J a.val ∈ M)
    (ξ : H) (hξ : J ξ = ξ) :
    (vectorSupportProjection M.commutant ξ).val.val =
      conjugationOperator J (vectorSupportProjection M ξ).val.val := by
  let p := vectorSupportProjection M ξ
  let q := vectorSupportProjection M.commutant ξ
  have hqp : q.val.val * conjugationOperator J p.val.val = q.val.val :=
    vectorSupport_minimal M.commutant ξ (conjugateAlgebraProjection M M.commutant J hJ hleft p)
      (conjugateAlgebraProjection_fixes M M.commutant J hJ hleft p ξ hξ
        (vectorSupportProjection_apply M ξ))
  have hpq : p.val.val * conjugationOperator J q.val.val = p.val.val :=
    vectorSupport_minimal M ξ (conjugateAlgebraProjection M.commutant M J hJ hright q)
      (conjugateAlgebraProjection_fixes M.commutant M J hJ hright q ξ hξ
        (vectorSupportProjection_apply M.commutant ξ))
  have hqp' := congrArg star hqp
  have hs : star q.val.val = q.val.val := congrArg Subtype.val q.property.isSelfAdjoint.star_eq
  have ht : star p.val.val = p.val.val := congrArg Subtype.val p.property.isSelfAdjoint.star_eq
  rw [star_mul, ← conjugationOperator_star J hJ, ht, hs] at hqp'
  have hpq' := congrArg (conjugationOperator J) hpq
  rw [conjugationOperator_mul J hJ, conjugationOperator_twice J hJ] at hpq'
  exact hqp'.symm.trans hpq'

end

end KadisonKastler

end OAI
