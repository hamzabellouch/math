import Mathlib.NumberTheory.GaussSum
import OAI.NumberTheory.Ostmann.Characters.AdditiveFourier
import OAI.NumberTheory.Ostmann.Characters.SquarePullback

namespace OAI

/-!
# Additive Fourier coefficients of multiplicative characters

The Gauss identity already proved in Mathlib gives the exact normalized
squared modulus needed for the two-bad quartet estimate in Section 6.
-/

namespace Ostmann

open scoped BigOperators ComplexConjugate

theorem gaussSum_norm_sq {p : ℕ} [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (hχ : χ ≠ 1) :
    ‖gaussSum χ (ZMod.stdAddChar (N := p))‖ ^ 2 = (p : ℝ) := by
  have h := gaussSum_mul_gaussSum_eq_card hχ (ZMod.isPrimitive_stdAddChar p)
  rw [← star_gaussSum_eq] at h
  change gaussSum χ ZMod.stdAddChar * conj (gaussSum χ ZMod.stdAddChar) = _ at h
  rw [Complex.mul_conj', ZMod.card] at h
  exact_mod_cast h

theorem additiveFourier_mulChar_unit {p : ℕ} [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (a : (ZMod p)ˣ) :
    additiveFourier χ (a : ZMod p) =
      (p : ℂ)⁻¹ * χ⁻¹ (-(a : ZMod p)) * gaussSum χ (ZMod.stdAddChar (N := p)) := by
  rw [additiveFourier_apply]
  have hsum : (∑ x : ZMod p, χ x * ZMod.stdAddChar (-(x * (a : ZMod p)))) =
      gaussSum χ ((ZMod.stdAddChar (N := p)).mulShift (-a)) := by
    simp only [gaussSum, AddChar.mulShift_apply]
    congr 1
    funext x
    rw [neg_mul, mul_comm (a : ZMod p) x]
  have hshift := gaussSum_mulShift_eq χ (ZMod.stdAddChar (N := p)) (-a)
  simp only [Units.val_neg] at hshift
  rw [hsum, hshift]
  ring

/-- The nonzero additive Fourier coefficients have squared modulus `1/p`. -/
theorem additiveFourier_mulChar_norm_sq_unit {p : ℕ} [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (hχ : χ ≠ 1) (a : (ZMod p)ˣ) :
    ‖additiveFourier χ (a : ZMod p)‖ ^ 2 = (p : ℝ)⁻¹ := by
  have hp : (p : ℝ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  rw [additiveFourier_mulChar_unit, norm_mul, norm_mul, norm_inv,
    Complex.norm_natCast, show ‖χ⁻¹ (-(a : ZMod p))‖ = 1 from norm_mulChar_unit χ⁻¹ (-a),
    mul_one, mul_pow, gaussSum_norm_sq χ hχ]
  field_simp

/-- A nonprincipal character has zero additive Fourier coefficient at zero. -/
theorem additiveFourier_mulChar_zero {p : ℕ} [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (hχ : χ ≠ 1) : additiveFourier χ 0 = 0 := by
  simp [additiveFourier_apply, χ.sum_eq_zero_of_ne_one hχ]

theorem additiveFourier_mulChar {p : ℕ} [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (hχ : χ ≠ 1) (a : ZMod p) :
    additiveFourier χ a =
      (p : ℂ)⁻¹ * χ⁻¹ (-a) * gaussSum χ (ZMod.stdAddChar (N := p)) := by
  by_cases ha : a = 0
  · subst a
    simp only [additiveFourier_mulChar_zero χ hχ, neg_zero, MulChar.map_zero, mul_zero,
      zero_mul]
  · exact additiveFourier_mulChar_unit χ (Units.mk0 a ha)

/-- The Fourier transform exchanges pointwise multiplication and convolution. -/
theorem additiveFourier_pointwise_mul {p : ℕ} [NeZero p]
    (f g : ZMod p → ℂ) (a : ZMod p) :
    additiveFourier (fun x => f x * g x) a =
      ∑ b : ZMod p, additiveFourier f b * additiveFourier g (a - b) := by
  rw [additiveFourier_apply]
  conv_lhs =>
    enter [2, 2, x]
    rw [additiveFourier_inversion f x]
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  rw [additiveFourier_apply g (a - b)]
  simp only [Finset.mul_sum]
  have hphase (x : ZMod p) :
      ZMod.stdAddChar (b * x) * ZMod.stdAddChar (-(x * a)) =
        ZMod.stdAddChar (-(x * (a - b))) := by
    rw [← AddChar.map_add_eq_mul]
    congr 1
    ring
  apply Finset.sum_congr rfl
  intro x _
  calc
    _ = (p : ℂ)⁻¹ * additiveFourier f b * g x *
        (ZMod.stdAddChar (b * x) * ZMod.stdAddChar (-(x * a))) := by ring
    _ = _ := by rw [hphase]; ring

/-- Exact Gauss convolution formula, including the vanishing zero term. -/
theorem additiveFourier_mul_character {p : ℕ} [Fact p.Prime]
    (f : ZMod p → ℂ) (χ : MulChar (ZMod p) ℂ) (hχ : χ ≠ 1) (a : ZMod p) :
    additiveFourier (fun x => f x * χ x) a =
      ((p : ℂ)⁻¹ * gaussSum χ (ZMod.stdAddChar (N := p))) *
        ∑ b : ZMod p, additiveFourier f b * χ⁻¹ (-(a - b)) := by
  rw [additiveFourier_pointwise_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  rw [additiveFourier_mulChar χ hχ]
  ring

end Ostmann

end OAI
