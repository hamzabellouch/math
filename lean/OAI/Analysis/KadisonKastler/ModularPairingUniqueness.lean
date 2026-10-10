import OAI.Analysis.KadisonKastler.SelfAdjointVectorSpace
import OAI.Analysis.KadisonKastler.BoundaryFiniteIsomorphism

namespace OAI

/-! # Uniqueness in the modular real pairing equation -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

theorem modular_pairing_eq_zero (Ω : H)
    (hsep : Function.Injective (algebraVectorMap M Ω))
    (z : ℂ) (hz : 0 < z.re) (x : Algebra M) (hx : IsSelfAdjoint x)
    (h : ∀ a : selfAdjoint (Algebra M), (z * inner ℂ (a.val.val Ω) (x.val Ω)).re = 0) :
    x = 0 := by
  have hh := h ⟨x, hx⟩
  change (z * inner ℂ (x.val Ω) (x.val Ω)).re = 0 at hh
  rw [Complex.mul_re] at hh
  change z.re * (inner ℂ (x.val Ω) (x.val Ω)).re -
    z.im * (inner ℂ (x.val Ω) (x.val Ω)).im = 0 at hh
  rw [show (inner ℂ (x.val Ω) (x.val Ω)).re = ‖x.val Ω‖ ^ 2 from inner_self_eq_norm_sq (𝕜 := ℂ) _,
    show (inner ℂ (x.val Ω) (x.val Ω)).im = 0 from inner_self_im (𝕜 := ℂ) _, mul_zero, sub_zero] at hh
  have hnorm : ‖x.val Ω‖ = 0 :=
    sq_eq_zero_iff.mp ((mul_eq_zero.mp hh).resolve_left hz.ne')
  apply hsep
  change x.val Ω = (0 : H →L[ℂ] H) Ω
  simpa only [zero_apply] using norm_eq_zero.mp hnorm

theorem modular_pairing_unique (Ω : H)
    (hsep : Function.Injective (algebraVectorMap M Ω))
    (z : ℂ) (hz : 0 < z.re) (x y : Algebra M)
    (hx : IsSelfAdjoint x) (hy : IsSelfAdjoint y)
    (h : ∀ a : selfAdjoint (Algebra M),
      (z * inner ℂ (a.val.val Ω) (x.val Ω)).re =
        (z * inner ℂ (a.val.val Ω) (y.val Ω)).re) : x = y := by
  apply sub_eq_zero.mp
  apply modular_pairing_eq_zero Ω hsep z hz (x - y) (hx.sub hy)
  intro a
  change (z * inner ℂ (a.val.val Ω) ((x.val - y.val) Ω)).re = 0
  rw [sub_apply, inner_sub_right, mul_sub, Complex.sub_re, h a, sub_self]

end

end KadisonKastler

end OAI
