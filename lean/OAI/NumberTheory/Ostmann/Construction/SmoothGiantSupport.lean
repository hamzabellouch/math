import Mathlib.Algebra.Order.Floor.Ring
import OAI.NumberTheory.Ostmann.Construction.SmoothGiantPrior

namespace OAI

/-! # Finite support for the actual positive-integer giant extension -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def smoothGiantIntegerRange (G : ℝ) : Finset ℕ :=
  Finset.Icc 1 ⌈Real.exp (G + 1)⌉₊

noncomputable def smoothGiantPrimeRange (G : ℝ) : Finset ℕ :=
  (smoothGiantIntegerRange G).filter Nat.Prime

theorem smoothGiantPrimeRange_prime (G : ℝ) :
    ∀ p ∈ smoothGiantPrimeRange G, p.Prime := fun _ hp => (Finset.mem_filter.mp hp).2

theorem smoothGiantPrimeRange_subset (G : ℝ) :
    smoothGiantPrimeRange G ⊆ smoothGiantIntegerRange G := Finset.filter_subset _ _

theorem smoothGiantIntegerRange_pos (G : ℝ) :
    ∀ p ∈ smoothGiantIntegerRange G, 0 < p := by
  intro p hp
  exact (Finset.mem_Icc.mp hp).1

/-- No positive integer outside this range contributes to the extension.
The endpoints are retained in the finite set. -/
theorem smoothGiant_weight_zero_outside (φ : ℝ → ℝ) (G : ℝ)
    (hout : ∀ x, 1 ≤ |x| → φ x = 0) (p : ℕ) (hp : 0 < p)
    (hpI : p ∉ smoothGiantIntegerRange G) : φ (Real.log p - G) = 0 := by
  have hceil : ⌈Real.exp (G + 1)⌉₊ < p := by
    have hn : ¬(1 ≤ p ∧ p ≤ ⌈Real.exp (G + 1)⌉₊) := by
      simpa only [smoothGiantIntegerRange, Finset.mem_Icc] using hpI
    omega
  have hexp : Real.exp (G + 1) < (p : ℝ) :=
    (Nat.le_ceil (Real.exp (G + 1))).trans_lt (by exact_mod_cast hceil)
  have hlog : G + 1 < Real.log p := by
    simpa only [Real.log_exp] using Real.log_lt_log (Real.exp_pos _) hexp
  exact hout _ (le_trans (by linarith) (le_abs_self _))

/-- The smooth normalizer has the exact finite support stipulated in (7.3). -/
theorem smoothGiant_prime_support (φ : ℝ → ℝ) (G : ℝ)
    (hout : ∀ x, 1 ≤ |x| → φ x = 0) (p : ℕ) (hp : p.Prime)
    (hφp : φ (Real.log p - G) ≠ 0) : p ∈ smoothGiantPrimeRange G := by
  apply Finset.mem_filter.mpr
  refine ⟨?_, hp⟩
  by_contra hn
  exact hφp (smoothGiant_weight_zero_outside φ G hout p hp.pos hn)

/-- A lower bound on the bump in a retained central prime interval gives
an actual lower bound for its normalizer. -/
theorem smoothGiantMass_lower (P S : Finset ℕ) (hSP : S ⊆ P)
    (φ : ℝ → ℝ) (G a : ℝ) (hφ : ∀ x, 0 ≤ φ x)
    (ha : ∀ p ∈ S, a ≤ φ (Real.log p - G)) :
    a * (∑ p ∈ S, (p : ℝ)⁻¹) ≤ smoothGiantMass P φ G := by
  calc
    _ = ∑ p ∈ S, a / (p : ℝ) := by simp only [Finset.mul_sum, div_eq_mul_inv]
    _ ≤ ∑ p ∈ S, φ (Real.log p - G) / (p : ℝ) :=
      Finset.sum_le_sum fun p hp => div_le_div_of_nonneg_right (ha p hp) (Nat.cast_nonneg _)
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hSP
      (fun p _ _ => div_nonneg (hφ _) (Nat.cast_nonneg _))

end Ostmann

end OAI
