import Mathlib.Data.Nat.Totient
import OAI.NumberTheory.Ostmann.Construction.HarmonicResidueDomination

namespace OAI

/-! # Harmonic prime residues compared with uniform unit residues -/

namespace Ostmann

open scoped BigOperators Classical

/-- The factor is the inverse harmonic normalizer times three times the
number of dyadic intervals. Boundary primes stay in the original prior. -/
theorem primeSubsetPrior_unit_residue_le (P S : Finset ℕ) (q h J : ℕ) [NeZero q]
    (hunit : ∀ p : P, (p : ℕ).Coprime q)
    (hsmall : q ≤ 2 ^ h)
    (hrange : ∀ n ∈ S, 2 ^ h ≤ n ∧ n < 2 ^ (h + J)) (a : (ZMod q)ˣ) :
    cellPrior (primeSubsetPrior P S) (fun p => ZMod.unitOfCoprime (p : ℕ) (hunit p)) a ≤
      ((∑ n ∈ S, (n : ℝ)⁻¹)⁻¹ * (3 * J)) * (Fintype.card (ZMod q)ˣ : ℝ)⁻¹ := by
  have hcell : cellPrior (primeSubsetPrior P S)
      (fun p => ZMod.unitOfCoprime (p : ℕ) (hunit p)) a =
      cellPrior (primeSubsetPrior P S) (fun p => ((p : ℕ) : ZMod q)) (a : ZMod q) := by
    unfold cellPrior
    apply Finset.sum_congr rfl
    intro p _
    have he : ZMod.unitOfCoprime (p : ℕ) (hunit p) = a ↔ ((p : ℕ) : ZMod q) = a := by
      rw [← Units.val_inj, ZMod.coe_unitOfCoprime]
    simp only [he]
    split_ifs <;> rfl
  rw [hcell]
  apply (primeSubsetPrior_residue_le P S q h J (NeZero.pos q) hsmall hrange a).trans
  have hcard : (Fintype.card (ZMod q)ˣ : ℝ) ≤ q := by
    exact_mod_cast (show Fintype.card (ZMod q)ˣ ≤ q by
      rw [ZMod.card_units_eq_totient]
      exact Nat.totient_le q)
  have hcpos : (0 : ℝ) < Fintype.card (ZMod q)ˣ := by
    exact_mod_cast Fintype.card_pos
  have hinv : (q : ℝ)⁻¹ ≤ (Fintype.card (ZMod q)ˣ : ℝ)⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le hcpos hcard
  calc
    _ = ((∑ n ∈ S, (n : ℝ)⁻¹)⁻¹ * (3 * J)) * (q : ℝ)⁻¹ := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hinv (by positivity)

/-- Nonnegative residue tests may be pulled through the exact pushforward
and bounded pointwise by the uniform unit law. -/
theorem harmonic_unit_expectation_le (P S : Finset ℕ) (q h J : ℕ) [NeZero q]
    (hunit : ∀ p : P, (p : ℕ).Coprime q)
    (hsmall : q ≤ 2 ^ h)
    (hrange : ∀ n ∈ S, 2 ^ h ≤ n ∧ n < 2 ^ (h + J))
    (F : (ZMod q)ˣ → ℝ) (hF : ∀ a, 0 ≤ F a) :
    (∑ p : P, primeSubsetPrior P S p * F (ZMod.unitOfCoprime (p : ℕ) (hunit p))) ≤
      ((∑ n ∈ S, (n : ℝ)⁻¹)⁻¹ * (3 * J)) *
        ((Fintype.card (ZMod q)ˣ : ℝ)⁻¹ * ∑ a, F a) := by
  have he : (∑ p : P, primeSubsetPrior P S p * F (ZMod.unitOfCoprime (p : ℕ) (hunit p))) =
      ∑ a : (ZMod q)ˣ, cellPrior (primeSubsetPrior P S)
        (fun p => ZMod.unitOfCoprime (p : ℕ) (hunit p)) a * F a := by
    unfold cellPrior
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro p _
    simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [he]
  calc
    _ ≤ ∑ a : (ZMod q)ˣ, (((∑ n ∈ S, (n : ℝ)⁻¹)⁻¹ * (3 * J)) *
        (Fintype.card (ZMod q)ˣ : ℝ)⁻¹) * F a := by
      apply Finset.sum_le_sum
      intro a _
      exact mul_le_mul_of_nonneg_right
        (primeSubsetPrior_unit_residue_le P S q h J hunit hsmall hrange a) (hF a)
    _ = _ := by rw [← Finset.mul_sum]; ring

end Ostmann

end OAI
