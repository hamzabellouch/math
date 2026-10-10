import Mathlib.Data.Nat.Totient
import OAI.NumberTheory.Ostmann.Characters.PolynomialLineFlags

namespace OAI

/-! # Actual line integrals as bounded functions of the cleared polynomial tests -/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def internalLineScalar (external : Bool) (p : ℕ) : ℝ :=
  ((if external then p else p - 1 : ℕ) : ℝ)⁻¹

theorem internalLineScalar_nonneg (external : Bool) (p : ℕ) :
    0 ≤ internalLineScalar external p := by
  unfold internalLineScalar
  positivity

theorem internalLineScalar_le_one (external : Bool) (p : ℕ) :
    internalLineScalar external p ≤ 1 := by
  let n : ℕ := if external then p else p - 1
  change (n : ℝ)⁻¹ ≤ 1
  rcases Nat.eq_zero_or_pos n with h | h
  · simp [h]
  · exact inv_le_one_of_one_le₀ (by exact_mod_cast h)

noncomputable def internalLineFlagWeight {J : Type*} (external : Bool) (p : ℕ)
    (flags : Bool ⊕ J → Bool) : ℝ :=
  if lineFeasibleFlags external flags then internalLineScalar external p else 0

theorem internalLineFlagWeight_nonneg {J : Type*} (external : Bool) (p : ℕ)
    (flags : Bool ⊕ J → Bool) : 0 ≤ internalLineFlagWeight external p flags := by
  unfold internalLineFlagWeight
  split_ifs
  · exact internalLineScalar_nonneg external p
  · rfl

theorem internalLineFlagWeight_le_one {J : Type*} (external : Bool) (p : ℕ)
    (flags : Bool ⊕ J → Bool) : internalLineFlagWeight external p flags ≤ 1 := by
  unfold internalLineFlagWeight
  split_ifs
  · exact internalLineScalar_le_one external p
  · norm_num

/-- The normalized count before the giant variables are integrated out. -/
noncomputable def internalLineProbability {J : Type*} {p : ℕ} [Fact p.Prime]
    (external : Bool) (a b : J → ZMod p) : ℝ :=
  if external then
    (Fintype.card {z : ZMod p × (ZMod p)ˣ // ∀ j, a j * z.1 + b j * z.2 = 0} : ℝ) /
      Fintype.card (ZMod p × (ZMod p)ˣ)
  else
    (Fintype.card {z : (ZMod p)ˣ × (ZMod p)ˣ // ∀ j, a j * z.1 + b j * z.2 = 0} : ℝ) /
      Fintype.card ((ZMod p)ˣ × (ZMod p)ˣ)

theorem internalLineProbability_nonneg {J : Type*} {p : ℕ} [Fact p.Prime]
    (external : Bool) (a b : J → ZMod p) : 0 ≤ internalLineProbability external a b := by
  unfold internalLineProbability
  split_ifs <;> positivity

theorem external_lineSystem_integral_eq_flags {σ J : Type*} {p : ℕ} [Fact p.Prime]
    (L : J → PolynomialGiantLine σ) (i : J) (φ : MvPolynomial σ ℤ →+* ZMod p)
    (hd : ∀ j, φ (L j).denominator ≠ 0)
    (hrow : ((L i).normalized φ).1 ≠ 0 ∨ ((L i).normalized φ).2 ≠ 0) :
    (Fintype.card {z : ZMod p × (ZMod p)ˣ //
      ∀ j, ((L j).normalized φ).1 * z.1 + ((L j).normalized φ).2 * z.2 = 0} : ℝ) /
      Fintype.card (ZMod p × (ZMod p)ˣ) =
      internalLineFlagWeight true p
        (fun s => arithmeticTestFlag (φ (lineTestPolynomials L i s) = 0)) := by
  rw [external_lineSystem_probability _ _ i hrow]
  unfold internalLineFlagWeight
  rw [external_polynomialLine_flags_iff L i φ hd]
  rfl

theorem unit_lineSystem_integral_eq_flags {σ J : Type*} {p : ℕ} [Fact p.Prime]
    (L : J → PolynomialGiantLine σ) (i : J) (φ : MvPolynomial σ ℤ →+* ZMod p)
    (hd : ∀ j, φ (L j).denominator ≠ 0)
    (hrow : ((L i).normalized φ).1 ≠ 0 ∨ ((L i).normalized φ).2 ≠ 0) :
    (Fintype.card {z : (ZMod p)ˣ × (ZMod p)ˣ //
      ∀ j, ((L j).normalized φ).1 * z.1 + ((L j).normalized φ).2 * z.2 = 0} : ℝ) /
      Fintype.card ((ZMod p)ˣ × (ZMod p)ˣ) =
      internalLineFlagWeight false p
        (fun s => arithmeticTestFlag (φ (lineTestPolynomials L i s) = 0)) := by
  rw [unit_lineSystem_probability _ _ i hrow]
  unfold internalLineFlagWeight
  rw [unit_polynomialLine_flags_iff L i φ hd]
  have hc : Fintype.card (ZMod p)ˣ = p - 1 := by
    rw [ZMod.card_units_eq_totient, Nat.totient_prime (Fact.out : p.Prime)]
  simp only [internalLineScalar, Bool.false_eq_true, ite_false, hc]

theorem internalLineProbability_eq_flags {σ J : Type*} {p : ℕ} [Fact p.Prime]
    (external : Bool) (L : J → PolynomialGiantLine σ) (i : J)
    (φ : MvPolynomial σ ℤ →+* ZMod p) (hd : ∀ j, φ (L j).denominator ≠ 0)
    (hrow : ((L i).normalized φ).1 ≠ 0 ∨ ((L i).normalized φ).2 ≠ 0) :
    internalLineProbability external (fun j => ((L j).normalized φ).1)
      (fun j => ((L j).normalized φ).2) =
      internalLineFlagWeight external p
        (fun s => arithmeticTestFlag (φ (lineTestPolynomials L i s) = 0)) := by
  cases external
  · exact unit_lineSystem_integral_eq_flags L i φ hd hrow
  · exact external_lineSystem_integral_eq_flags L i φ hd hrow

end Ostmann

end OAI
