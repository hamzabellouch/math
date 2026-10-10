import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.Analysis.Complex.Polynomial.Basic
import OAI.NumberTheory.Ostmann.Characters.Mellin

namespace OAI

/-!
# Mellin inversion and Parseval on the nonzero residues

The coefficients use the probability normalization from `Mellin.lean`.
The only character-theoretic input is the finite duality already in Mathlib.
-/

namespace Ostmann

open scoped BigOperators ComplexConjugate

noncomputable local instance {p : ℕ} [Fact p.Prime] :
    Fintype (MulChar (ZMod p) ℂ) := Fintype.ofFinite _

noncomputable local instance {p : ℕ} : DecidableEq (MulChar (ZMod p) ℂ) :=
  Classical.decEq _

/-- There are exactly as many complex multiplicative characters as units. -/
theorem card_mulChar_eq_card_units {p : ℕ} [Fact p.Prime] :
    Fintype.card (MulChar (ZMod p) ℂ) = Fintype.card (ZMod p)ˣ := by
  simpa only [Nat.card_eq_fintype_card] using
    MulChar.card_eq_card_units_of_hasEnoughRootsOfUnity (ZMod p) ℂ

/-- Summing characters detects the identity element. -/
theorem sum_mulChar_apply_eq_ite {p : ℕ} [Fact p.Prime] (u : (ZMod p)ˣ) :
    (∑ χ : MulChar (ZMod p) ℂ, χ u) =
      if u = 1 then (Fintype.card (ZMod p)ˣ : ℂ) else 0 := by
  classical
  by_cases hu : u = 1
  · subst u
    simp only [Units.val_one, map_one, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, mul_one, ite_true, card_mulChar_eq_card_units]
  · simp only [hu, ite_false]
    have huval : (u : ZMod p) ≠ 1 := by
      intro h
      exact hu (Units.ext h)
    obtain ⟨χ₀, hχ₀⟩ :=
      MulChar.exists_apply_ne_one_of_hasEnoughRootsOfUnity (ZMod p) ℂ huval
    apply eq_zero_of_mul_eq_self_left hχ₀
    calc
      χ₀ u * ∑ χ : MulChar (ZMod p) ℂ, χ u =
          ∑ χ : MulChar (ZMod p) ℂ, (χ₀ * χ) u := by
        simp only [Finset.mul_sum, MulChar.coeToFun_mul, Pi.mul_apply]
      _ = ∑ χ : MulChar (ZMod p) ℂ, χ u :=
        (Equiv.mulLeft χ₀).bijective.sum_comp (fun χ : MulChar (ZMod p) ℂ => χ u)

/-- The dual orthogonality identity, with the sum over characters. -/
theorem mellin_dual_orthogonality {p : ℕ} [Fact p.Prime] (x z : (ZMod p)ˣ) :
    (∑ χ : MulChar (ZMod p) ℂ, χ x * conj (χ z)) =
      if x = z then (Fintype.card (ZMod p)ˣ : ℂ) else 0 := by
  have hterm : ∀ χ : MulChar (ZMod p) ℂ,
      χ x * conj (χ z) = χ ((x / z : (ZMod p)ˣ) : ZMod p) := by
    intro χ
    rw [Units.val_div_eq_div_val, div_eq_mul_inv, map_mul,
      ← MulChar.inv_apply', MulChar.inv_apply_eq_inv',
      Complex.inv_eq_conj (norm_mulChar_unit χ z)]
  simp_rw [hterm]
  rw [sum_mulChar_apply_eq_ite]
  simp only [div_eq_one]

/-- Full finite Mellin inversion for arbitrary complex functions on the units. -/
theorem mellin_inversion {p : ℕ} [Fact p.Prime]
    (f : (ZMod p)ˣ → ℂ) (x : (ZMod p)ˣ) :
    (∑ χ : MulChar (ZMod p) ℂ, mellinCoefficient f χ * χ x) = f x := by
  classical
  have hc : (Fintype.card (ZMod p)ˣ : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  unfold mellinCoefficient
  calc
    (∑ χ : MulChar (ZMod p) ℂ,
        ((Fintype.card (ZMod p)ˣ : ℂ)⁻¹ * ∑ z, f z * conj (χ z)) * χ x) =
        (Fintype.card (ZMod p)ˣ : ℂ)⁻¹ *
          ∑ z : (ZMod p)ˣ, f z * ∑ χ : MulChar (ZMod p) ℂ, χ x * conj (χ z) := by
      simp only [Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro z _
      apply Finset.sum_congr rfl
      intro χ _
      ring
    _ = f x := by
      simp_rw [mellin_dual_orthogonality]
      simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
      field_simp

/-- The exact probability-normalized Parseval identity. -/
theorem mellin_parseval {p : ℕ} [Fact p.Prime] (f : (ZMod p)ˣ → ℂ) :
    (∑ χ : MulChar (ZMod p) ℂ, ‖mellinCoefficient f χ‖ ^ 2) =
      (Fintype.card (ZMod p)ˣ : ℝ)⁻¹ * ∑ z : (ZMod p)ˣ, ‖f z‖ ^ 2 := by
  have hcomplex :
      (∑ χ : MulChar (ZMod p) ℂ, conj (mellinCoefficient f χ) * mellinCoefficient f χ) =
        (Fintype.card (ZMod p)ˣ : ℂ)⁻¹ *
          ∑ z : (ZMod p)ˣ, conj (f z) * f z := by
    calc
      _ = ∑ χ : MulChar (ZMod p) ℂ, conj (mellinCoefficient f χ) *
          ((Fintype.card (ZMod p)ˣ : ℂ)⁻¹ * ∑ z : (ZMod p)ˣ, f z * conj (χ z)) := rfl
      _ = (Fintype.card (ZMod p)ˣ : ℂ)⁻¹ * ∑ z : (ZMod p)ˣ,
          (∑ χ : MulChar (ZMod p) ℂ, conj (mellinCoefficient f χ) * conj (χ z)) * f z := by
        simp only [Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro z _
        apply Finset.sum_congr rfl
        intro χ _
        ring
      _ = _ := by
        have hsum : ∀ z : (ZMod p)ˣ,
            (∑ χ : MulChar (ZMod p) ℂ, conj (mellinCoefficient f χ) * conj (χ z)) =
              conj (f z) := by
          intro z
          calc
            _ = ∑ χ : MulChar (ZMod p) ℂ,
                conj (mellinCoefficient f χ * χ z) := by simp only [map_mul]
            _ = conj (∑ χ : MulChar (ZMod p) ℂ,
                mellinCoefficient f χ * χ z) := (map_sum (starRingEnd ℂ) _ _).symm
            _ = conj (f z) := congrArg conj (mellin_inversion f z)
        simp_rw [hsum]
  simp_rw [Complex.conj_mul', ← Complex.ofReal_pow, ← Complex.ofReal_sum] at hcomplex
  apply Complex.ofReal_injective
  push_cast
  simpa only [Complex.ofReal_sum, Complex.ofReal_pow] using hcomplex

end Ostmann

end OAI
