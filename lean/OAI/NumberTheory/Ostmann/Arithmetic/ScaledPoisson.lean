import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import OAI.NumberTheory.Ostmann.Characters.TranslatedCharacterPoisson

namespace OAI

/-! # The original scale in the quadratic-character Poisson formula -/

namespace Ostmann

open scoped BigOperators FourierTransform SchwartzMap
open MeasureTheory

theorem fourier_comp_positive_mul (f : ℝ → ℂ) {a : ℝ} (ha : 0 < a) (ξ : ℝ) :
    𝓕 (fun x => f (a * x)) ξ = (a : ℂ)⁻¹ * 𝓕 f (ξ / a) := by
  rw [Real.fourier_real_eq_integral_exp_smul, Real.fourier_real_eq_integral_exp_smul]
  let g : ℝ → ℂ := fun y => Complex.exp (((-2 * Real.pi * y * (ξ / a) : ℝ) : ℂ) * Complex.I) • f y
  have hi : (∫ x : ℝ, Complex.exp (((-2 * Real.pi * x * ξ : ℝ) : ℂ) * Complex.I) • f (a * x)) =
      ∫ x : ℝ, g (a * x) := by
    apply integral_congr_ae
    filter_upwards [] with x
    dsimp [g]
    have he : (-2 * Real.pi * (a * x) * (ξ / a) : ℝ) = -2 * Real.pi * x * ξ := by
      field_simp
    rw [he]
  rw [hi, Measure.integral_comp_mul_left]
  simp only [abs_of_pos (inv_pos.mpr ha), Complex.real_smul, Complex.ofReal_inv]
  rfl

noncomputable def positiveDilate (f : 𝓢(ℝ, ℂ)) (a : ℝ) (ha : 0 < a) : 𝓢(ℝ, ℂ) :=
  SchwartzMap.compCLM ℂ (g := fun x : ℝ => a * x) (by fun_prop)
    ⟨1, a⁻¹, fun x => by
      simp only [pow_one, norm_mul, Real.norm_eq_abs, abs_of_pos ha]
      rw [mul_add, ← mul_assoc, inv_mul_cancel₀ ha.ne', one_mul]
      simpa only [mul_one] using le_add_of_nonneg_left (a := |x|) (inv_nonneg.mpr ha.le)⟩ f

theorem positiveDilate_apply (f : 𝓢(ℝ, ℂ)) (a : ℝ) (ha : 0 < a) (x : ℝ) :
    positiveDilate f a ha x = f (a * x) := rfl

theorem positiveDilate_fourier (f : 𝓢(ℝ, ℂ)) (a : ℝ) (ha : 0 < a) (ξ : ℝ) :
    𝓕 (positiveDilate f a ha) ξ = (a : ℂ)⁻¹ * 𝓕 f (ξ / a) := by
  change 𝓕 (fun x : ℝ => f (a * x)) ξ = (a : ℂ)⁻¹ * 𝓕 (f : ℝ → ℂ) (ξ / a)
  exact fourier_comp_positive_mul f ha ξ

theorem scaled_quadratic_character_poisson {d M : ℕ} [NeZero d] [NeZero M]
    (h : d.Coprime M) (f : ZMod d → ℂ) (χ : DirichletCharacter ℂ M)
    (hχ : χ.IsPrimitive) (hq : χ.IsQuadratic) (t : ZMod M) (ψ : 𝓢(ℝ, ℂ))
    (X : ℝ) (hX : 0 < X) :
    (∑' n : ℤ, f (n : ZMod d) * χ ((n : ZMod M) - t) * ψ ((n : ℝ) / X)) =
      (X : ℂ) / M * gaussSum χ ZMod.stdAddChar * ∑' n : ℤ,
        𝓕 ψ ((n : ℝ) * X / (d * M : ℕ)) *
        additiveFourier f (-((M : ZMod d)⁻¹ * (n : ZMod d))) *
        ZMod.stdAddChar (t * ((d : ZMod M)⁻¹ * (n : ZMod M))) *
        χ (d : ZMod M) * χ (n : ZMod M) := by
  have hd : (0 : ℝ) < d := by exact_mod_cast NeZero.pos d
  have hM : (0 : ℝ) < M := by exact_mod_cast NeZero.pos M
  have ha : 0 < (d * M : ℕ) / X := div_pos (by rw [Nat.cast_mul]; exact mul_pos hd hM) hX
  have hp := quadratic_character_poisson h f χ hχ hq t
    (positiveDilate ψ ((d * M : ℕ) / X) ha)
  have harg (n : ℤ) : ((d * M : ℕ) : ℝ) / X * ((n : ℝ) / (d * M : ℕ)) = n / X := by
    field_simp
  simp_rw [positiveDilate_apply, harg, positiveDilate_fourier] at hp
  have hfreq (n : ℤ) : (n : ℝ) / ((d * M : ℕ) / X) = (n : ℝ) * X / (d * M : ℕ) := by rw [div_div_eq_mul_div]
  simp_rw [hfreq] at hp
  rw [hp]
  simp_rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne d
  have hMC : (M : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne M
  push_cast
  field_simp

end Ostmann

end OAI
