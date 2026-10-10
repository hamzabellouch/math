import OAI.NumberTheory.Ostmann.Construction.TransferIntegerPhases
import OAI.NumberTheory.Ostmann.Characters.PivotRowPhase

namespace OAI

/-! # Complete local rows and their product under transfer -/

namespace Ostmann

open scoped BigOperators ComplexConjugate

/-- The incoming pivot column becomes one constant exponent on every
opposite-branch constituent. The other old row factors are retained. -/
theorem transfer_left_row {I : Type*} [Fintype I] {p : ℕ} [Fact p.Prime]
    (χ : DirichletCharacter ℂ p) (P D v s t : ZMod p) (R : I → ZMod p)
    (ν S O : ℂ) (b : ℤ)
    (hP : P ≠ 0) (hD : D ≠ 0) (hR : (∏ i, R i) ≠ 0) (hs : s ≠ 0)
    (hrel : v * (∏ i, R i) = s * P) :
    ZMod.stdAddChar (t * (v / (P * D))) * ν * χ P ^ b * S * O =
      ZMod.stdAddChar (t * (s / ((∏ i, R i) * D))) *
        (ν * χ (v / s) ^ b) * S * (∏ i, χ (R i) ^ b) * O := by
  rw [transfer_left_additive P (∏ i, R i) D v s t hP hR hD hrel,
    transfer_incoming_character χ P (∏ i, R i) v s hs hrel b,
    character_product_power χ R b]
  ring

/-- The conjugated right row has the negative incoming exponent on every
left-branch constituent. This includes its new unary factor exactly. -/
theorem transfer_right_row {I : Type*} [Fintype I] {p : ℕ} [Fact p.Prime]
    (χ : DirichletCharacter ℂ p) (P D w s t : ZMod p) (L : I → ZMod p)
    (ν S O : ℂ) (b : ℤ)
    (hP : P ≠ 0) (hD : D ≠ 0) (hL : (∏ i, L i) ≠ 0) (hs : s ≠ 0)
    (hrel : -w * (∏ i, L i) = s * P) :
    conj (ZMod.stdAddChar (t * (w / (P * D))) * ν * χ P ^ b * S * O) =
      ZMod.stdAddChar (t * (s / ((∏ i, L i) * D))) *
        (conj ν * χ (-w / s) ^ (-b)) * conj S * (∏ i, χ (L i) ^ (-b)) * conj O := by
  have hc : conj (χ P ^ b) = χ (-w / s) ^ (-b) * ∏ i, χ (L i) ^ (-b) := by
    rw [transfer_incoming_character χ P (∏ i, L i) (-w) s hs hrel b, map_mul,
      conjugate_character_power, conjugate_character_power, character_product_power]
  rw [map_mul, map_mul, map_mul, map_mul, hc,
    transfer_right_additive P (∏ i, L i) D w s t hP hL hD hrel]
  ring

/-- Every common outside factor cancels at a shared slot. The remaining
incoming exponents on the copied branches have opposite signs. -/
theorem transfer_outside_row {p : ℕ} [Fact p.Prime]
    (P L R D v w s t : ZMod p) (νv νw C SL SR : ℂ)
    (hP : P ≠ 0) (hL : L ≠ 0) (hR : R ≠ 0) (hD : D ≠ 0)
    (hC : ‖C‖ = 1) (hrel : v * R - w * L = s * P) :
    (ZMod.stdAddChar (t * (v / (P * L * D))) * νv * C * SL) *
      conj (ZMod.stdAddChar (t * (w / (P * R * D))) * νw * C * SR) =
    ZMod.stdAddChar (t * (s / (L * R * D))) * (νv * conj νw) * SL * conj SR := by
  have hCC : C * conj C = 1 := by
    rw [Complex.mul_conj', hC]
    norm_num
  simp only [map_mul (starRingEnd ℂ)]
  calc
    _ = (ZMod.stdAddChar (t * (v / (P * L * D))) *
        conj (ZMod.stdAddChar (t * (w / (P * R * D))))) *
        (νv * conj νw) * (C * conj C) * SL * conj SR := by ring
    _ = _ := by
      rw [transfer_outside_additive P L R D v w s t hP hL hR hD hrel, hCC, mul_one]

/-- Products of actual unit character factors have unit modulus, for all
integer exponents. This discharges the common-row cancellation hypothesis. -/
theorem character_row_norm_one {I : Type*} [Fintype I] {p : ℕ}
    (χ : DirichletCharacter ℂ p) (q : I → ZMod p) (b : I → ℤ)
    (hq : ∀ i, IsUnit (q i)) : ‖∏ i, χ (q i) ^ b i‖ = 1 := by
  rw [norm_prod]
  apply Finset.prod_eq_one
  intro i _
  obtain ⟨u, hu⟩ := hq i
  rw [← hu, norm_zpow, χ.unit_norm_eq_one, one_zpow]

/-- Left and right rows separate, while each shared outside row is paired
before its product is taken. -/
theorem transfer_phase_product {H Y : Type*} [Fintype H] [Fintype Y]
    (left right : H → ℂ) (outLeft outRight : Y → ℂ) :
    ((∏ h, left h) * ∏ y, outLeft y) * conj ((∏ h, right h) * ∏ y, outRight y) =
      (∏ h, left h) * (∏ h, conj (right h)) * ∏ y, outLeft y * conj (outRight y) := by
  rw [map_mul, map_prod, map_prod, Finset.prod_mul_distrib]
  ring

end Ostmann

end OAI
