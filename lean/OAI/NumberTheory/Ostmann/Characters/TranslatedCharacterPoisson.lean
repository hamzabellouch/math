import OAI.NumberTheory.Ostmann.Characters.CRTFourier
import OAI.NumberTheory.Ostmann.QuadraticCenter.IntegerPoissonTransform

namespace OAI

/-! # The translated primitive-character Poisson identity

This is the exact finite-modulus transform used before the squarefree
frequency decomposition in Section 3 of the manuscript.
-/

namespace Ostmann

open scoped BigOperators FourierTransform SchwartzMap

theorem translated_character_crt_fourier {d M : ℕ} [NeZero d] [NeZero M]
    (h : d.Coprime M) (f : ZMod d → ℂ) (χ : DirichletCharacter ℂ M)
    (hχ : χ.IsPrimitive) (t : ZMod M) (u : ZMod (d * M)) :
    additiveFourier (fun x => f ((ZMod.chineseRemainder h) x).1 *
      χ (((ZMod.chineseRemainder h) x).2 - t)) (-u) =
      additiveFourier f (-((M : ZMod d)⁻¹ * ((ZMod.chineseRemainder h) u).1)) *
      ZMod.stdAddChar (t * ((d : ZMod M)⁻¹ * ((ZMod.chineseRemainder h) u).2)) *
      (M : ℂ)⁻¹ * χ⁻¹ ((d : ZMod M)⁻¹ * ((ZMod.chineseRemainder h) u).2) *
      gaussSum χ ZMod.stdAddChar := by
  rw [additiveFourier_crt h f (fun x => χ (x - t)) (-u),
    additiveFourier_translate, primitive_character_fourier _ hχ]
  simp only [map_neg]
  change additiveFourier f ((M : ZMod d)⁻¹ * -((ZMod.chineseRemainder h) u).1) *
    (ZMod.stdAddChar (-(t * ((d : ZMod M)⁻¹ * -((ZMod.chineseRemainder h) u).2))) *
      ((M : ℂ)⁻¹ * χ⁻¹ (-((d : ZMod M)⁻¹ * -((ZMod.chineseRemainder h) u).2)) *
        gaussSum χ ZMod.stdAddChar)) = _
  simp only [mul_neg, neg_neg]
  ring

theorem quadratic_character_inverse_value {M : ℕ} (χ : DirichletCharacter ℂ M)
    (hχ : χ.IsQuadratic) (x : ZMod M) (hx : IsUnit x) : χ (x⁻¹) = χ x := by
  obtain ⟨v, rfl⟩ := hx
  rw [ZMod.inv_coe_unit]
  have hh := MulChar.inv_apply χ (v : ZMod M)
  rw [Ring.inverse_unit, hχ.inv] at hh
  exact hh.symm

/-- For a quadratic character, the inverse frequency multiplier contributes
the ordinary character value of the other coprime modulus. -/
theorem quadratic_translated_crt_fourier {d M : ℕ} [NeZero d] [NeZero M]
    (h : d.Coprime M) (f : ZMod d → ℂ) (χ : DirichletCharacter ℂ M)
    (hχ : χ.IsPrimitive) (hq : χ.IsQuadratic) (t : ZMod M) (u : ZMod (d * M)) :
    additiveFourier (fun x => f ((ZMod.chineseRemainder h) x).1 *
      χ (((ZMod.chineseRemainder h) x).2 - t)) (-u) =
      additiveFourier f (-((M : ZMod d)⁻¹ * ((ZMod.chineseRemainder h) u).1)) *
      ZMod.stdAddChar (t * ((d : ZMod M)⁻¹ * ((ZMod.chineseRemainder h) u).2)) *
      (M : ℂ)⁻¹ * χ (d : ZMod M) * χ ((ZMod.chineseRemainder h) u).2 *
      gaussSum χ ZMod.stdAddChar := by
  rw [translated_character_crt_fourier h f χ hχ, hq.inv, map_mul χ,
    quadratic_character_inverse_value χ hq _ ((ZMod.isUnit_iff_coprime d M).mpr h)]
  ring

theorem quadratic_character_poisson {d M : ℕ} [NeZero d] [NeZero M]
    (h : d.Coprime M) (f : ZMod d → ℂ) (χ : DirichletCharacter ℂ M)
    (hχ : χ.IsPrimitive) (hq : χ.IsQuadratic) (t : ZMod M) (ψ : 𝓢(ℝ, ℂ)) :
    (∑' n : ℤ, f (n : ZMod d) * χ ((n : ZMod M) - t) *
      ψ ((n : ℝ) / (d * M : ℕ))) =
      (d : ℂ) * gaussSum χ ZMod.stdAddChar * ∑' n : ℤ,
        𝓕 ψ (n : ℝ) *
        additiveFourier f (-((M : ZMod d)⁻¹ * (n : ZMod d))) *
        ZMod.stdAddChar (t * ((d : ZMod M)⁻¹ * (n : ZMod M))) *
        χ (d : ZMod M) * χ (n : ZMod M) := by
  have he (n : ℤ) : (ZMod.chineseRemainder h) (n : ZMod (d * M)) =
      ((n : ZMod d), (n : ZMod M)) := by
    exact map_intCast (ZMod.chineseRemainder h) n
  have hp := integer_poisson_transform ψ
    (fun x : ZMod (d * M) => f ((ZMod.chineseRemainder h) x).1 *
      χ (((ZMod.chineseRemainder h) x).2 - t))
  simp_rw [he] at hp
  rw [hp]
  simp_rw [quadratic_translated_crt_fourier h f χ hχ hq, he]
  simp_rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  push_cast
  have hM : (M : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne M
  field_simp

end Ostmann

end OAI
