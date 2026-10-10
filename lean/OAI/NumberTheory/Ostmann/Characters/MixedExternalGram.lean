import OAI.NumberTheory.Ostmann.Characters.MixedExternalPermutation
import OAI.NumberTheory.Ostmann.Arithmetic.SymmetrizedPairBound

namespace OAI

/-! # Positive Gram estimates in the original mixed external measure -/

namespace Ostmann
open scoped Classical BigOperators

theorem mixedExternalAverage_weighted_correlation_bound {B A : Type*}
    [Fintype B] [Fintype A] (ν : B → A → ℝ) (hν : ∀ b a, 0 ≤ ν b a)
    (N : ℕ) (u v r w center : ℝ)
    (F H : ℤ → (B → A) → ℝ → ℝ → ℂ) (W : ℤ → (B → A) → ℝ → ℝ → ℝ)
    (hW : ∀ s y x z, 0 ≤ W s y x z) (E : ℝ)
    (hF : (mixedExternalAverage ν N u v r w center
      (fun s y x z => (‖F s y x z‖ ^ 2 : ℂ) * W s y x z)).re ≤ E)
    (hH : (mixedExternalAverage ν N u v r w center
      (fun s y x z => (‖H s y x z‖ ^ 2 : ℂ) * W s y x z)).re ≤ E) :
    ‖mixedExternalAverage ν N u v r w center
      (fun s y x z => (F s y x z * star (H s y x z)) * W s y x z)‖ ≤ E := by
  let ρ := mixedExternalPrior ν N u v r w center
  let f := fun x : MixedExternalPoint B A N u v r w =>
    F x.1.val x.2.1 (Real.log x.2.2.2.val) (Real.log x.2.2.1.val)
  let h := fun x : MixedExternalPoint B A N u v r w =>
    H x.1.val x.2.1 (Real.log x.2.2.2.val) (Real.log x.2.2.1.val)
  let vW := fun x : MixedExternalPoint B A N u v r w =>
    W x.1.val x.2.1 (Real.log x.2.2.2.val) (Real.log x.2.2.1.val)
  have hρ (x) : 0 ≤ ρ x := mixedExternalPrior_nonneg ν hν N u v r w center x
  have hW' (x) : 0 ≤ vW x := hW _ _ _ _
  have hF' : (∑ x, ρ x * (‖f x‖ ^ 2 * vW x)) ≤ E := by
    simpa only [mixedExternalAverage_finite, Complex.re_sum, Complex.mul_re,
      ← Complex.ofReal_pow, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
      zero_mul, sub_zero] using hF
  have hH' : (∑ x, ρ x * (‖h x‖ ^ 2 * vW x)) ≤ E := by
    simpa only [mixedExternalAverage_finite, Complex.re_sum, Complex.mul_re,
      ← Complex.ofReal_pow, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
      zero_mul, sub_zero] using hH
  rw [mixedExternalAverage_finite]
  calc
    _ ≤ ∑ x, ρ x * (‖f x‖ * ‖h x‖ * vW x) := by
      apply (norm_sum_le _ _).trans_eq
      apply Finset.sum_congr rfl
      intro x _
      change ‖(ρ x : ℂ) * ((f x * star (h x)) * (vW x : ℂ))‖ = _
      simp only [norm_mul, norm_star, Complex.norm_real, Real.norm_of_nonneg (hρ x),
        Real.norm_of_nonneg (hW' x)]
    _ ≤ (∑ x, (ρ x * (‖f x‖ ^ 2 * vW x) +
        ρ x * (‖h x‖ ^ 2 * vW x))) / 2 := by
      rw [Finset.sum_div]
      apply Finset.sum_le_sum
      intro x _
      have ha : ‖f x‖ * ‖h x‖ ≤ (‖f x‖ ^ 2 + ‖h x‖ ^ 2) / 2 := by
        nlinarith [sq_nonneg (‖f x‖ - ‖h x‖)]
      have hb := mul_le_mul_of_nonneg_left ha (mul_nonneg (hρ x) (hW' x))
      nlinarith
    _ ≤ E := by rw [Finset.sum_add_distrib]; linarith

theorem mixedExternalAverage_family_bound {B A J : Type*}
    [Fintype B] [Fintype A] [Group J] [Fintype J]
    (ν : B → A → ℝ) (N : ℕ) (u v r w center : ℝ)
    (F : J → ℤ → (B → A) → ℝ → ℝ → ℂ)
    (W : ℤ → (B → A) → ℝ → ℝ → ℝ)
    (bad : J → Prop) (D E : ℝ) (hE : 0 ≤ E)
    (hpair : ∀ i j, ‖mixedExternalAverage ν N u v r w center
      (fun s y x z => (F i s y x z * star (F j s y x z)) * W s y x z)‖ ≤
        if bad (i⁻¹ * j) then D else E) :
    (mixedExternalAverage ν N u v r w center
      (fun s y x z => (‖finiteFamilyAverage (fun j _ => F j s y x z) ()‖ ^ 2 : ℂ) *
        W s y x z)).re ≤
      (Fintype.card {j : J // bad j} : ℝ) / Fintype.card J * D + E := by
  let ρ := fun x : MixedExternalPoint B A N u v r w =>
    mixedExternalPrior ν N u v r w center x *
      W x.1.val x.2.1 (Real.log x.2.2.2.val) (Real.log x.2.2.1.val)
  let f := fun j (x : MixedExternalPoint B A N u v r w) =>
    F j x.1.val x.2.1 (Real.log x.2.2.2.val) (Real.log x.2.2.1.val)
  have hp (i j : J) : ‖∑ x, (ρ x : ℂ) * (f i x * star (f j x))‖ ≤
      if bad (i⁻¹ * j) then D else E := by
    convert hpair i j using 1
    rw [mixedExternalAverage_finite]
    congr 1
    apply Finset.sum_congr rfl
    intro x _
    dsimp [ρ, f]
    push_cast
    ring
  have h := finiteFamilyAverage_good_bad_bound ρ f bad D E hE hp
  convert h using 1
  simp only [mixedExternalAverage_finite, Complex.re_sum, Complex.mul_re,
    ← Complex.ofReal_pow, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
    zero_mul, sub_zero]
  apply Finset.sum_congr rfl
  intro x _
  dsimp only [ρ, f, finiteFamilyAverage]
  ring

end Ostmann

end OAI
