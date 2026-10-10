import OAI.Analysis.KadisonKastler.HermitianLinearExtension
import OAI.Analysis.KadisonKastler.BoundaryFiniteIsomorphism

namespace OAI

/-! # Complexifying the modular Radon--Nikodym equation

The real equation on self-adjoint tests determines a complex-linear
identity on all algebra elements. This is the identity used to identify
the bounded Tomita resolvent.
-/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

def rightVectorPairing (M : VonNeumannAlgebra H) (Ω ξ : H) : Algebra M →ₗ[ℂ] ℂ :=
  (innerSL ℂ Ω).toLinearMap.comp (algebraVectorMap M ξ)

def leftVectorPairing (M : VonNeumannAlgebra H) (Ω ξ : H) : Algebra M →ₗ[ℂ] ℂ :=
  (innerSL ℂ ξ).toLinearMap.comp (algebraVectorMap M Ω)

private theorem rightVectorPairing_star (Ω ξ : H) (a : Algebra M) :
    rightVectorPairing M Ω ξ (star a) = star (leftVectorPairing M Ω ξ a) := by
  change inner ℂ Ω (star a.val ξ) = star (inner ℂ ξ (a.val Ω))
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right,
    Complex.star_def, inner_conj_symm]

private theorem leftVectorPairing_star (Ω ξ : H) (a : Algebra M) :
    leftVectorPairing M Ω ξ (star a) = star (rightVectorPairing M Ω ξ a) := by
  have h := congrArg star (rightVectorPairing_star Ω ξ (star a))
  simpa only [star_star] using h.symm

private theorem rightVectorPairing_selfAdjoint (Ω ξ : H)
    (a : selfAdjoint (Algebra M)) :
    rightVectorPairing M Ω ξ a.val = inner ℂ (a.val.val Ω) ξ := by
  have ha : a.val.val.adjoint = a.val.val :=
    (show IsSelfAdjoint a.val.val from congrArg Subtype.val a.property.star_eq).star_eq
  change inner ℂ Ω (a.val.val ξ) = _
  rw [← ha, ContinuousLinearMap.adjoint_inner_right]
  rw [ha]

private theorem leftVectorPairing_commutant (Ω : H) (b : H →L[ℂ] H)
    (hb : b ∈ M.commutant) (hbs : IsSelfAdjoint b) :
    leftVectorPairing M Ω (b Ω) = rightVectorPairing M Ω (b Ω) := by
  ext a
  have hc : a.val * b = b * a.val := hb _ (Set.mem_union_left _ a.property)
  change inner ℂ (b Ω) (a.val Ω) = inner ℂ Ω (a.val (b Ω))
  rw [← ContinuousLinearMap.adjoint_inner_right]
  have hs : b.adjoint = b := hbs.star_eq
  rw [hs]
  exact congrArg (fun T : H →L[ℂ] H => inner ℂ Ω (T Ω)) hc.symm

/-- The real pairing equation determines the full complex identity. -/
theorem modular_pairing_complex (Ω : H) (b : H →L[ℂ] H)
    (hb : b ∈ M.commutant) (hbs : IsSelfAdjoint b)
    (z : ℂ) (x : Algebra M)
    (hpair : ∀ a : selfAdjoint (Algebra M),
      (inner ℂ (a.val.val Ω) (b Ω)).re =
        (z * inner ℂ (a.val.val Ω) (x.val Ω)).re) :
    ∀ a : Algebra M,
      2 * inner ℂ Ω (a.val (b Ω)) =
        z * inner ℂ Ω (a.val (x.val Ω)) +
          star z * inner ℂ (x.val Ω) (a.val Ω) := by
  let F := (2 : ℂ) • rightVectorPairing M Ω (b Ω)
  let G := z • rightVectorPairing M Ω (x.val Ω) +
    star z • leftVectorPairing M Ω (x.val Ω)
  have hF : ∀ a, F (star a) = star (F a) := by
    intro a
    dsimp only [F, LinearMap.smul_apply, smul_eq_mul]
    rw [rightVectorPairing_star, ← leftVectorPairing_commutant Ω b hb hbs]
    simp only [star_mul, star_ofNat]
    ring
  have hG : ∀ a, G (star a) = star (G a) := by
    intro a
    dsimp only [G, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
    rw [rightVectorPairing_star, leftVectorPairing_star]
    simp only [star_add, star_mul, star_star]
    ring
  have hFG : F = G := hermitianLinear_eq_of_selfAdjoint_real F G hF hG (by
    intro a
    have hb' := rightVectorPairing_selfAdjoint Ω (b Ω) a
    have hx' := rightVectorPairing_selfAdjoint Ω (x.val Ω) a
    have hl : leftVectorPairing M Ω (x.val Ω) a.val =
        star (rightVectorPairing M Ω (x.val Ω) a.val) := by
      have h := leftVectorPairing_star Ω (x.val Ω) a.val
      rwa [a.property.star_eq] at h
    change (2 * rightVectorPairing M Ω (b Ω) a.val).re =
      (z * rightVectorPairing M Ω (x.val Ω) a.val +
        star z * leftVectorPairing M Ω (x.val Ω) a.val).re
    rw [hl, hb', hx']
    have h := hpair a
    rw [Complex.mul_re] at h
    simp only [Complex.add_re, Complex.mul_re, Complex.star_def, Complex.conj_re,
      Complex.conj_im]
    norm_num
    linarith)
  intro a
  exact congrArg (fun L : Algebra M →ₗ[ℂ] ℂ => L a) hFG

end

end KadisonKastler

end OAI
