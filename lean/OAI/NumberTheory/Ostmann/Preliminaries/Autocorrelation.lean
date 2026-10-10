import OAI.NumberTheory.Ostmann.Characters.AdditiveFourier

namespace OAI

/-!
# Additive autocorrelation

The probability-normalized Fourier transform of an autocorrelation is
the squared modulus of the original transform. This is the positivity
identity used for the bottom-pair coefficients in Section 6.
-/

namespace Ostmann

open scoped BigOperators ComplexConjugate

noncomputable def additiveConvolution {p : ℕ} [NeZero p]
    (f g : ZMod p → ℂ) (x : ZMod p) : ℂ :=
  (p : ℂ)⁻¹ * ∑ y : ZMod p, f y * g (x - y)

theorem additiveFourier_translation_sum {p : ℕ} [NeZero p]
    (g : ZMod p → ℂ) (a y : ZMod p) :
    (∑ x : ZMod p, g (x - y) * ZMod.stdAddChar (-(x * a))) =
      ZMod.stdAddChar (-(y * a)) * ∑ z : ZMod p, g z * ZMod.stdAddChar (-(z * a)) := by
  calc
    _ = ∑ z : ZMod p, g ((z + y) - y) * ZMod.stdAddChar (-((z + y) * a)) :=
      ((Equiv.addRight y).bijective.sum_comp
        (fun x : ZMod p => g (x - y) * ZMod.stdAddChar (-(x * a)))).symm
    _ = _ := by
      simp only [add_sub_cancel_right, add_mul, neg_add, AddChar.map_add_eq_mul]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z _
      ring

theorem additiveFourier_convolution {p : ℕ} [NeZero p]
    (f g : ZMod p → ℂ) (a : ZMod p) :
    additiveFourier (additiveConvolution f g) a =
      additiveFourier f a * additiveFourier g a := by
  simp only [additiveFourier_apply, additiveConvolution]
  calc
    _ = (p : ℂ)⁻¹ * (p : ℂ)⁻¹ *
        ∑ y : ZMod p, f y * ∑ x : ZMod p, g (x - y) * ZMod.stdAddChar (-(x * a)) := by
      simp only [Finset.sum_mul, Finset.mul_sum, mul_assoc]
      rw [Finset.sum_comm]
    _ = _ := by
      simp_rw [additiveFourier_translation_sum]
      simp_rw [← mul_assoc]
      rw [← Finset.sum_mul]
      ring

theorem additiveFourier_reflected_conj {p : ℕ} [NeZero p]
    (f : ZMod p → ℂ) (a : ZMod p) :
    additiveFourier (fun x => conj (f (-x))) a = conj (additiveFourier f a) := by
  rw [additiveFourier_apply, additiveFourier_apply]
  simp only [map_mul, map_inv₀, map_natCast, map_sum, stdAddChar_conj, neg_neg]
  congr 1
  calc
    _ = ∑ y : ZMod p, conj (f (-(-y))) * ZMod.stdAddChar (-((-y) * a)) :=
      ((Equiv.neg (ZMod p)).bijective.sum_comp
        (fun x : ZMod p => conj (f (-x)) * ZMod.stdAddChar (-(x * a)))).symm
    _ = _ := by simp only [neg_neg, neg_mul]

noncomputable def additiveAutocorrelation {p : ℕ} [NeZero p]
    (f : ZMod p → ℂ) (d : ZMod p) : ℂ :=
  (p : ℂ)⁻¹ * ∑ x : ZMod p, f x * conj (f (x - d))

theorem additiveAutocorrelation_eq_convolution {p : ℕ} [NeZero p]
    (f : ZMod p → ℂ) :
    additiveAutocorrelation f = additiveConvolution f (fun x => conj (f (-x))) := by
  funext d
  simp only [additiveAutocorrelation, additiveConvolution, neg_sub]

theorem additiveFourier_autocorrelation {p : ℕ} [NeZero p]
    (f : ZMod p → ℂ) (a : ZMod p) :
    additiveFourier (additiveAutocorrelation f) a = (‖additiveFourier f a‖ ^ 2 : ℝ) := by
  rw [additiveAutocorrelation_eq_convolution, additiveFourier_convolution,
    additiveFourier_reflected_conj, Complex.mul_conj']
  norm_cast

end Ostmann

end OAI
