import Mathlib.Analysis.Complex.Basic
import OAI.NumberTheory.Ostmann.Characters.SquarePullback

namespace OAI

/-!
# Mellin coefficients of a square pullback

Character orthogonality identifies the coefficient after substituting
`K * z^2`. The factor-two estimate then follows from `SquarePullback`.
-/

namespace Ostmann

open scoped BigOperators ComplexConjugate

noncomputable local instance {p : ℕ} : DecidableEq (MulChar (ZMod p) ℂ) := Classical.decEq _

theorem sum_mulChar_units_eq_zero {p : ℕ} [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) (hχ : χ ≠ 1) :
    (∑ z : (ZMod p)ˣ, χ z) = 0 := by
  obtain ⟨b, hb⟩ := MulChar.ne_one_iff.mp hχ
  apply eq_zero_of_mul_eq_self_left hb
  calc
    χ b * ∑ z : (ZMod p)ˣ, χ z = ∑ z : (ZMod p)ˣ, χ (b * z) := by
      simp only [Finset.mul_sum, map_mul]
    _ = ∑ z : (ZMod p)ˣ, χ z :=
      (Equiv.mulLeft b).bijective.sum_comp (fun z : (ZMod p)ˣ => χ z)

theorem sum_mulChar_units_eq_ite {p : ℕ} [Fact p.Prime]
    (χ : MulChar (ZMod p) ℂ) :
    (∑ z : (ZMod p)ˣ, χ z) =
      if χ = 1 then (Fintype.card (ZMod p)ˣ : ℂ) else 0 := by
  classical
  by_cases hχ : χ = 1
  · subst χ
    simp only [MulChar.one_apply_coe, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      mul_one, ite_true]
  · simp only [hχ, ite_false, sum_mulChar_units_eq_zero χ hχ]

theorem mellin_orthogonality {p : ℕ} [Fact p.Prime]
    (χ ρ : MulChar (ZMod p) ℂ) :
    (∑ z : (ZMod p)ˣ, χ z * conj (ρ z)) =
      if χ = ρ then (Fintype.card (ZMod p)ˣ : ℂ) else 0 := by
  have hterm : ∀ z : (ZMod p)ˣ, χ z * conj (ρ z) = (χ * ρ⁻¹) z := by
    intro z
    rw [MulChar.coeToFun_mul, Pi.mul_apply, MulChar.inv_apply_eq_inv',
      Complex.inv_eq_conj (norm_mulChar_unit ρ z)]
  simp_rw [hterm]
  rw [sum_mulChar_units_eq_ite]
  simp only [mul_inv_eq_one]

/-- Probability-normalized Mellin coefficient on the nonzero field elements. -/
noncomputable def mellinCoefficient {p : ℕ} [Fact p.Prime]
    (f : (ZMod p)ˣ → ℂ) (ρ : MulChar (ZMod p) ℂ) : ℂ :=
  (Fintype.card (ZMod p)ˣ : ℂ)⁻¹ * ∑ z, f z * conj (ρ z)

/-- Character orthogonality computes the square-pullback coefficient. -/
theorem mellinCoefficient_square_pullback {p : ℕ} [Fact p.Prime]
    (s : Finset (MulChar (ZMod p) ℂ)) (c : MulChar (ZMod p) ℂ → ℂ)
    (f : (ZMod p)ˣ → ℂ) (hf : ∀ z, f z = ∑ χ ∈ s, c χ * χ z)
    (K : (ZMod p)ˣ) (ρ : MulChar (ZMod p) ℂ) :
    mellinCoefficient (fun z => f (K * z ^ 2)) ρ =
      ∑ χ ∈ s.filter (fun χ => χ ^ 2 = ρ), c χ * χ K := by
  classical
  have hcard : (Fintype.card (ZMod p)ˣ : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  unfold mellinCoefficient
  simp_rw [hf, Finset.sum_mul]
  rw [Finset.sum_comm, Finset.mul_sum]
  calc
    _ = ∑ χ ∈ s, (Fintype.card (ZMod p)ˣ : ℂ)⁻¹ *
        (c χ * χ K * ∑ z : (ZMod p)ˣ, (χ ^ 2) z * conj (ρ z)) := by
      apply Finset.sum_congr rfl
      intro χ _
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z _
      simp only [Units.val_mul, Units.val_pow_eq_pow_val, map_mul, map_pow,
        MulChar.pow_apply_coe]
      ring
    _ = _ := by
      simp_rw [mellin_orthogonality]
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro χ _
      by_cases hχ : χ ^ 2 = ρ
      · simp only [hχ, ite_true]
        field_simp
      · simp only [hχ, ite_false, mul_zero]

/-- Equation `tree-square-pullback` for a finite Mellin expansion. -/
theorem mellinCoefficient_square_pullback_bound {p : ℕ} [Fact p.Prime]
    (s : Finset (MulChar (ZMod p) ℂ)) (c : MulChar (ZMod p) ℂ → ℂ)
    (f : (ZMod p)ˣ → ℂ) (hf : ∀ z, f z = ∑ χ ∈ s, c χ * χ z)
    (K : (ZMod p)ˣ) (ρ : MulChar (ZMod p) ℂ) :
    ‖mellinCoefficient (fun z => f (K * z ^ 2)) ρ‖ ^ 2 ≤
      2 * ∑ χ ∈ s.filter (fun χ => χ ^ 2 = ρ), ‖c χ‖ ^ 2 := by
  rw [mellinCoefficient_square_pullback s c f hf K ρ]
  exact square_pullback_coefficients s c K ρ

end Ostmann

end OAI
