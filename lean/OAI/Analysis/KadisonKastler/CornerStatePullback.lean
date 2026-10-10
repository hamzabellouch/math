import OAI.Analysis.KadisonKastler.CornerStateConjugation
import OAI.Analysis.KadisonKastler.TypeIIIProjectionComparison

namespace OAI

/-! # Isometric pullback of corner-state comparisons

An isometry onto a projection identifies its corner with the original
algebra. The two sandwich maps preserve the norm of corner-supported
functionals, so a state comparison on the original factor supplies the
same comparison in the corner without a multiplicative loss.
-/

namespace KadisonKastler

open Generator.Tracial

noncomputable section

variable {A : Type*} [CStarAlgebra A]

theorem sandwichFunctional_comp (φ : A →L[ℂ] ℂ) (u v : A) :
    sandwichFunctional (sandwichFunctional φ u) v = sandwichFunctional φ (v*u) := by
  ext a
  simp only [sandwichFunctional_apply,star_mul,mul_assoc]

theorem sandwichFunctional_sub (φ ψ : A →L[ℂ] ℂ) (u : A) :
    sandwichFunctional (φ-ψ) u = sandwichFunctional φ u-sandwichFunctional ψ u := by
  ext a
  rfl

theorem sandwichFunctional_one (φ : A →L[ℂ] ℂ) : sandwichFunctional φ 1=φ := by
  ext a
  simp only [sandwichFunctional_apply,star_one,one_mul,mul_one]

theorem sandwichFunctional_projection (φ : A →L[ℂ] ℂ) (p : A)
    (hp : IsStarProjection p) : sandwichFunctional φ p=cornerFunctional φ p := by
  ext a
  simp only [sandwichFunctional_apply,cornerFunctional_apply,hp.isSelfAdjoint.star_eq]

theorem sandwichFunctional_norm_le (φ : A →L[ℂ] ℂ) (u : A) (hu : ‖u‖ ≤ 1) :
    ‖sandwichFunctional φ u‖ ≤ ‖φ‖ := by
  apply (sandwichFunctional φ u).opNorm_le_bound (norm_nonneg φ)
  intro a
  change ‖φ (star u*a*u)‖ ≤ ‖φ‖*‖a‖
  calc
    _ ≤ ‖φ‖*‖star u*a*u‖ := φ.le_opNorm _
    _ ≤ ‖φ‖*((‖u‖*‖a‖)*‖u‖) := by
      gcongr
      exact (norm_mul_le _ _).trans
        (mul_le_mul_of_nonneg_right (by simpa only [norm_star] using norm_mul_le (star u) a)
          (norm_nonneg u))
    _ ≤ ‖φ‖*((1*‖a‖)*1) := by gcongr
    _ = _ := by ring

theorem sandwichFunctional_isometry_norm (φ : A →L[ℂ] ℂ)
    (v : A) (hv : star v*v=1) (hnorm : ‖v‖ ≤ 1) :
    ‖sandwichFunctional φ v‖=‖φ‖ := by
  apply le_antisymm (sandwichFunctional_norm_le φ v hnorm)
  have h := sandwichFunctional_norm_le (sandwichFunctional φ v) (star v)
    (by simpa only [norm_star] using hnorm)
  rwa [sandwichFunctional_comp,hv,sandwichFunctional_one] at h

theorem sandwichFunctional_supported_pullback_norm (φ : A →L[ℂ] ℂ)
    (p v : A) (hp : IsStarProjection p) (hvp : v*star v=p) (hnorm : ‖v‖ ≤ 1)
    (hφ : cornerFunctional φ p=φ) :
    ‖sandwichFunctional φ (star v)‖=‖φ‖ := by
  apply le_antisymm (sandwichFunctional_norm_le φ (star v) (by simpa only [norm_star] using hnorm))
  have h := sandwichFunctional_norm_le (sandwichFunctional φ (star v)) v hnorm
  rwa [sandwichFunctional_comp,hvp,sandwichFunctional_projection _ _ hp,hφ] at h

theorem cornerFunctional_idempotent (φ : A →L[ℂ] ℂ) (p : A) (hp : IsStarProjection p) :
    cornerFunctional (cornerFunctional φ p) p=cornerFunctional φ p := by
  ext a
  change φ (p*(p*a*p)*p)=φ (p*a*p)
  congr 1
  calc
    _ = (p*p)*a*(p*p) := by simp only [mul_assoc]
    _ = _ := by rw [hp.isIdempotentElem.eq]

theorem sandwichFunctional_corner_norm (φ : A →L[ℂ] ℂ) (p v : A)
    (hp : IsStarProjection p) (hvp : v*star v=p) (hnorm : ‖v‖ ≤ 1) :
    ‖sandwichFunctional (cornerFunctional φ p) (star v)‖ = ‖cornerFunctional φ p‖ :=
  sandwichFunctional_supported_pullback_norm _ p v hp hvp hnorm
    (cornerFunctional_idempotent φ p hp)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

theorem isometry_norm_le_one (v : Algebra M) (hv : star v*v=1) : ‖v‖ ≤ 1 := by
  let a : PartialIsometry M := ⟨⟨1,IsStarProjection.one _⟩,v,hv⟩
  exact a.norm_le_one

theorem isometry_corner_unitary (p : AlgebraProjection M) (v : Algebra M)
    (hv : star v*v=1) (hvp : v*star v=p.val) (u : unitary (Algebra M)) :
    star (v*u.val*star v)*(v*u.val*star v)=p.val ∧
      (v*u.val*star v)*star (v*u.val*star v)=p.val := by
  have hs : star (v*u.val*star v)=v*star u.val*star v := by
    simp only [star_mul,star_star,mul_assoc]
  rw [hs]
  constructor
  · calc
      _ = v*(star u.val*(star v*v)*u.val)*star v := by simp only [mul_assoc]
      _ = _ := by rw [hv,mul_one,u.property.1,mul_one,hvp]
  · calc
      _ = v*(u.val*(star v*v)*star u.val)*star v := by simp only [mul_assoc]
      _ = _ := by rw [hv,mul_one,u.property.2,mul_one,hvp]

end

end KadisonKastler

end OAI
