import OAI.NumberTheory.Ostmann.Construction.PrimePriorDecay

namespace OAI

/-! # Bounds on the support of the original harmonic prime priors -/

namespace Ostmann
open scoped Classical BigOperators

theorem primeSubsetPrior_log_lower (P Q : Finset ℕ) (T : ℝ)
    (hQ : ∀ p ∈ Q, T ≤ Real.log (p : ℝ)) (p : P)
    (hp : primeSubsetPrior P Q p ≠ 0) : T ≤ Real.log (p : ℝ) :=
  hQ _ (primeSubsetPrior_support P Q p hp)

/-- The ambient sample space can include smaller primes in other roles. -/
theorem primeSubsetPrior_le_exp_of_support (P Q : Finset ℕ) (H T : ℝ)
    (hmass : (∑ q ∈ Q, (q : ℝ)⁻¹)⁻¹ ≤ Real.exp H)
    (hQ : ∀ q ∈ Q, Real.exp T ≤ (q : ℝ)) (p : P) :
    primeSubsetPrior P Q p ≤ Real.exp (H - T) := by
  by_cases hp : primeSubsetPrior P Q p = 0
  · rw [hp]
    exact (Real.exp_pos _).le
  · exact primeSubsetPrior_le_exp P Q p H T hmass
      (hQ _ (primeSubsetPrior_support P Q p hp))

theorem primeSubsetPrior_le_one (P Q : Finset ℕ) (hQP : Q ⊆ P)
    (hmass : (∑ q ∈ Q, (q : ℝ)⁻¹) ≠ 0) (p : P) :
    primeSubsetPrior P Q p ≤ 1 := by
  rw [← primeSubsetPrior_mass P Q hQP hmass]
  exact Finset.single_le_sum (fun a _ => primeSubsetPrior_nonneg P Q a) (Finset.mem_univ p)

/-- The compensated internal prior pays only its original normalizer. -/
theorem prime_mul_primeSubsetPrior_le (P Q : Finset ℕ) (p : P) :
    (p : ℝ) * primeSubsetPrior P Q p ≤ (∑ q ∈ Q, (q : ℝ)⁻¹)⁻¹ := by
  by_cases hp0 : (p : ℕ) = 0
  · simp only [hp0, Nat.cast_zero, zero_mul]
    exact inv_nonneg.mpr (Finset.sum_nonneg fun q _ => inv_nonneg.mpr (Nat.cast_nonneg q))
  · have hp : (p : ℝ) ≠ 0 := by exact_mod_cast hp0
    unfold primeSubsetPrior
    split_ifs
    · rw [div_eq_mul_inv, ← mul_assoc, mul_inv_cancel₀ hp, one_mul]
    · simp only [mul_zero]
      exact inv_nonneg.mpr (Finset.sum_nonneg fun q _ => inv_nonneg.mpr (Nat.cast_nonneg q))

/-- The rich-cell lower bound has the polynomial normalizer required in the
prime comparison, at every shell scale bounded by `exp (K * L)`. -/
theorem selected_cell_mass_scale (c K L B mass : ℝ) (hc : 0 < c)
    (hK : 0 ≤ K) (hL : 1 ≤ L) (hB : 0 < B) (hBupper : B ≤ Real.exp (K * L))
    (hmass : c / B ≤ mass) :
    1 ≤ K + c⁻¹ + 1 ∧
      Real.exp (-(K + c⁻¹ + 1) * L) ≤ mass ∧
      mass⁻¹ ≤ Real.exp ((K + c⁻¹ + 1) * L) := by
  have hci : 0 < c⁻¹ := inv_pos.mpr hc
  have hL0 : 0 ≤ L := by linarith
  have hbig : c⁻¹ ≤ Real.exp ((c⁻¹ + 1) * L) := by
    have hmul := mul_le_mul_of_nonneg_left hL hci.le
    linarith [Real.add_one_le_exp ((c⁻¹ + 1) * L)]
  have hsmall : Real.exp (-((c⁻¹ + 1) * L)) ≤ c := by
    rw [Real.exp_neg]
    simpa only [inv_inv] using inv_anti₀ hci hbig
  have hBsmall : Real.exp (-(K * L)) ≤ B⁻¹ := by
    rw [Real.exp_neg]
    exact inv_anti₀ hB hBupper
  have hlo : Real.exp (-(K + c⁻¹ + 1) * L) ≤ mass := by
    calc
      _ = Real.exp (-(K * L)) * Real.exp (-((c⁻¹ + 1) * L)) := by
        rw [← Real.exp_add]
        congr 1
        ring
      _ ≤ Real.exp (-(K * L)) * c :=
        mul_le_mul_of_nonneg_left hsmall (Real.exp_nonneg _)
      _ ≤ B⁻¹ * c := mul_le_mul_of_nonneg_right hBsmall hc.le
      _ = c / B := by ring
      _ ≤ mass := hmass
  refine ⟨by linarith, hlo, ?_⟩
  have hh := inv_anti₀ (Real.exp_pos (-(K + c⁻¹ + 1) * L)) hlo
  simpa only [Real.exp_neg, inv_inv, neg_mul] using hh

end Ostmann

end OAI
