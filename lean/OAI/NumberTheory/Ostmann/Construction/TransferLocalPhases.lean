import OAI.NumberTheory.Ostmann.Characters.TupleCharacterPoisson
import OAI.NumberTheory.Ostmann.Construction.TransferArithmetic

namespace OAI

/-! # Local additive and character substitutions in one transfer -/

namespace Ostmann

open scoped ComplexConjugate

private theorem transfer_left_division {K : Type*} [Field K]
    (P R D v s : K) (hP : P ≠ 0) (hR : R ≠ 0) (hD : D ≠ 0)
    (hrel : v * R = s * P) : v / (P * D) = s / (R * D) := by
  apply (div_eq_div_iff (mul_ne_zero hP hD) (mul_ne_zero hR hD)).mpr
  calc
    v * (R * D) = (v * R) * D := by ring
    _ = (s * P) * D := by rw [hrel]
    _ = s * (P * D) := by ring

private theorem transfer_outside_division {K : Type*} [Field K]
    (P L R D v w s : K) (hP : P ≠ 0) (hL : L ≠ 0) (hR : R ≠ 0) (hD : D ≠ 0)
    (hrel : v * R - w * L = s * P) :
    v / (P * L * D) - w / (P * R * D) = s / (L * R * D) := by
  calc
    _ = (v * R - w * L) / (P * L * R * D) := by field_simp
    _ = (s * P) / (P * L * R * D) := by rw [hrel]
    _ = _ := by field_simp

/-- At a left-slot prime the right branch survives modulo p. -/
theorem transfer_left_additive {p : ℕ} [Fact p.Prime]
    (P R D v s t : ZMod p) (hP : P ≠ 0) (hR : R ≠ 0) (hD : D ≠ 0)
    (hrel : v * R = s * P) :
    ZMod.stdAddChar (t * (v / (P * D))) =
      ZMod.stdAddChar (t * (s / (R * D))) := by
  rw [transfer_left_division P R D v s hP hR hD hrel]

/-- At a right-slot prime conjugation supplies the minus sign. -/
theorem transfer_right_additive {p : ℕ} [Fact p.Prime]
    (P L D w s t : ZMod p) (hP : P ≠ 0) (hL : L ≠ 0) (hD : D ≠ 0)
    (hrel : -w * L = s * P) :
    conj (ZMod.stdAddChar (t * (w / (P * D)))) =
      ZMod.stdAddChar (t * (s / (L * D))) := by
  have h := transfer_left_division P L D (-w) s hP hL hD hrel
  rw [← h]
  simp only [neg_div, mul_neg, AddChar.map_neg_eq_conj]

/-- Outside slots occur in both branches and their translation differences
combine at the new signed frequency. -/
theorem transfer_outside_additive {p : ℕ} [Fact p.Prime]
    (P L R D v w s t : ZMod p)
    (hP : P ≠ 0) (hL : L ≠ 0) (hR : R ≠ 0) (hD : D ≠ 0)
    (hrel : v * R - w * L = s * P) :
    ZMod.stdAddChar (t * (v / (P * L * D))) *
        conj (ZMod.stdAddChar (t * (w / (P * R * D)))) =
      ZMod.stdAddChar (t * (s / (L * R * D))) := by
  rw [← AddChar.map_neg_eq_conj, ← AddChar.map_add_eq_mul, ← sub_eq_add_neg, ← mul_sub,
    transfer_outside_division P L R D v w s hP hL hR hD hrel]

private theorem mulChar_div {K : Type*} [Field K] (χ : MulChar K ℂ) (v s : K) :
    χ (v / s) = χ v / χ s := by
  rw [div_eq_mul_inv, map_mul, ← MulChar.inv_apply', MulChar.inv_apply_eq_inv', div_eq_mul_inv]

/-- The incoming pivot column becomes a cross-branch character factor. -/
theorem transfer_left_character {p : ℕ} [Fact p.Prime]
    (χ : DirichletCharacter ℂ p) (P R v s : ZMod p) (hs : s ≠ 0)
    (hrel : v * R = s * P) : χ P = χ (v / s) * χ R := by
  have he : P = v / s * R := by
    apply (mul_left_cancel₀ hs)
    calc
      s * P = v * R := hrel.symm
      _ = s * (v / s * R) := by field_simp
  rw [he, map_mul]

/-- Frequency factors cancel in every regular outgoing row, for either sign. -/
theorem transfer_regular_unary {p : ℕ} [Fact p.Prime]
    (χ : DirichletCharacter ℂ p) (v s : ZMod p) (hv : v ≠ 0) (ε : ℤ) :
    χ v ^ (-ε) * χ (v / s) ^ ε = χ s ^ (-ε) := by
  have hχv : χ v ≠ 0 := (MulChar.apply_ne_zero_iff).mpr (isUnit_iff_ne_zero.mpr hv)
  rw [mulChar_div, div_zpow, zpow_neg, zpow_neg]
  field_simp

theorem character_product_power {I : Type*} [Fintype I] {p : ℕ}
    (χ : DirichletCharacter ℂ p) (q : I → ZMod p) (b : ℤ) :
    χ (∏ i, q i) ^ b = ∏ i, χ (q i) ^ b := by
  rw [map_prod, Finset.prod_zpow]

theorem conjugate_character_power {p : ℕ} (χ : DirichletCharacter ℂ p)
    (x : ZMod p) (b : ℤ) : conj (χ x ^ b) = χ x ^ (-b) := by
  change star (χ x ^ b) = _
  rw [star_zpow₀, MulChar.star_apply', MulChar.inv_apply_eq_inv', inv_zpow, zpow_neg]

theorem transfer_incoming_character {p : ℕ} [Fact p.Prime]
    (χ : DirichletCharacter ℂ p) (P R v s : ZMod p) (hs : s ≠ 0)
    (hrel : v * R = s * P) (b : ℤ) :
    χ P ^ b = χ (v / s) ^ b * χ R ^ b := by
  rw [transfer_left_character χ P R v s hs hrel, mul_zpow]

theorem transfer_left_regular_factor {p : ℕ} [Fact p.Prime]
    (χ : DirichletCharacter ℂ p) (P R v s : ZMod p) (hv : v ≠ 0) (hs : s ≠ 0)
    (hrel : v * R = s * P) (ε : ℤ) :
    χ v ^ (-ε) * χ P ^ ε = χ s ^ (-ε) * χ R ^ ε := by
  rw [transfer_incoming_character χ P R v s hs hrel, ← mul_assoc,
    transfer_regular_unary χ v s hv ε]

/-- The new right unary has the reversed frequency exponent; its extra
minus-one factor is independent of every frequency. -/
theorem transfer_right_regular_factor {p : ℕ} [Fact p.Prime]
    (χ : DirichletCharacter ℂ p) (P L w s : ZMod p) (hw : w ≠ 0) (hs : s ≠ 0)
    (hrel : -w * L = s * P) (ε : ℤ) :
    conj (χ w ^ (-ε) * χ P ^ ε) =
      χ (-1) ^ (-ε) * χ s ^ ε * χ L ^ (-ε) := by
  have hp : χ P = χ (-1) * χ (w / s) * χ L := by
    rw [transfer_left_character χ P L (-w) s hs hrel,
      show -w / s = (-1) * (w / s) by ring, map_mul]
  have he : χ w ^ (-ε) * χ P ^ ε =
      χ (-1) ^ ε * χ s ^ (-ε) * χ L ^ ε := by
    rw [hp, mul_zpow, mul_zpow]
    calc
      _ = χ (-1) ^ ε * (χ w ^ (-ε) * χ (w / s) ^ ε) * χ L ^ ε := by ring
      _ = _ := by rw [transfer_regular_unary χ w s hw ε]
  rw [he, map_mul, map_mul, conjugate_character_power, conjugate_character_power,
    conjugate_character_power, neg_neg]

end Ostmann

end OAI
