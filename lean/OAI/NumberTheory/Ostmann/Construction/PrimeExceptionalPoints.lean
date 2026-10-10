import OAI.NumberTheory.Ostmann.ZeroDensity.ComplexPrimeWeights

namespace OAI

/-! # Retaining prime atoms on the boundaries of arithmetic root cells -/

namespace Ostmann
open scoped BigOperators Classical

/-- Changing the weight at finitely many primes costs their actual atom
masses. The estimate is uniform in the residue class and keeps endpoints. -/
theorem complexPrimeInterval_exceptional_bound (q a : ℕ) (u v : ℝ)
    (w g : ℝ → ℂ) (S : Finset ℕ) (B : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ p ∈ Finset.Ioc ⌊Real.exp u⌋₊ ⌊Real.exp v⌋₊,
      p.Prime → Nat.ModEq q p a → ‖w (Real.log p) - g (Real.log p)‖ ≤ B)
    (heq : ∀ p ∈ Finset.Ioc ⌊Real.exp u⌋₊ ⌊Real.exp v⌋₊,
      p.Prime → Nat.ModEq q p a → p ∉ S → w (Real.log p) = g (Real.log p)) :
    ‖complexPrimeInterval q a u v w - complexPrimeInterval q a u v g‖ ≤
      (S.card : ℝ) * B * Real.exp (-u) := by
  let T := Finset.Ioc ⌊Real.exp u⌋₊ ⌊Real.exp v⌋₊
  have he : complexPrimeInterval q a u v w - complexPrimeInterval q a u v g =
      ∑ p ∈ T, if p.Prime ∧ Nat.ModEq q p a then
        (w (Real.log p) - g (Real.log p)) * ((p : ℝ)⁻¹ : ℂ) else 0 := by
    simp only [complexPrimeInterval, ← Finset.sum_sub_distrib, T]
    apply Finset.sum_congr rfl
    intro p _
    split_ifs <;> simp [sub_mul]
  have hC : 0 ≤ B * Real.exp (-u) := mul_nonneg hB (Real.exp_pos _).le
  have hpoint (p : ℕ) (hp : p ∈ T) :
      ‖(if p.Prime ∧ Nat.ModEq q p a then
        (w (Real.log p) - g (Real.log p)) * ((p : ℝ)⁻¹ : ℂ) else 0)‖ ≤
        if p ∈ S then B * Real.exp (-u) else 0 := by
    by_cases hs : p ∈ S
    · rw [ite_eq_left hs]
      by_cases hc : p.Prime ∧ Nat.ModEq q p a
      · rw [ite_eq_left hc, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (Nat.cast_nonneg p)]
        have hp0 : (0 : ℝ) < p := by exact_mod_cast hc.1.pos
        have hlog := log_mem_of_mem_exp_interval hp
        have hexp : Real.exp u ≤ (p : ℝ) := by
          calc
            Real.exp u ≤ Real.exp (Real.log p) := Real.exp_le_exp.mpr hlog.1.le
            _ = _ := Real.exp_log hp0
        have hinv : (p : ℝ)⁻¹ ≤ Real.exp (-u) := by
          rw [Real.exp_neg]
          exact inv_anti₀ (Real.exp_pos _) hexp
        exact mul_le_mul (hbound p hp hc.1 hc.2) hinv (inv_nonneg.mpr hp0.le) hB
      · simpa only [ite_eq_right hc, norm_zero] using hC
    · rw [ite_eq_right hs]
      by_cases hc : p.Prime ∧ Nat.ModEq q p a
      · simp only [ite_eq_left hc, heq p hp hc.1 hc.2 hs, sub_self, zero_mul, norm_zero, le_refl]
      · simp only [ite_eq_right hc, norm_zero, le_refl]
  rw [he]
  calc
    _ ≤ ∑ p ∈ T, ‖(if p.Prime ∧ Nat.ModEq q p a then
      (w (Real.log p) - g (Real.log p)) * ((p : ℝ)⁻¹ : ℂ) else 0)‖ := norm_sum_le _ _
    _ ≤ ∑ p ∈ T, if p ∈ S then B * Real.exp (-u) else 0 :=
      Finset.sum_le_sum hpoint
    _ = ((T.filter (· ∈ S)).card : ℝ) * (B * Real.exp (-u)) := by
      rw [← Finset.sum_filter]
      simp
    _ ≤ (S.card : ℝ) * (B * Real.exp (-u)) := by
      apply mul_le_mul_of_nonneg_right _ hC
      exact_mod_cast Finset.card_le_card (show T.filter (· ∈ S) ⊆ S from
        fun _ h => (Finset.mem_filter.mp h).2)
    _ = _ := by ring

/-- The exceptional primes lying on real root boundaries inject into the
boundary set, so their count never exceeds the number of cuts. -/
theorem prime_boundary_card_le (T : Finset ℕ) (S : Finset ℝ) :
    (T.filter (fun p : ℕ => (p : ℝ) ∈ S)).card ≤ S.card := by
  exact Finset.card_le_card_of_injOn (fun p : ℕ => (p : ℝ))
    (fun _ h => (Finset.mem_filter.mp h).2)
    (fun _ _ _ _ h => Nat.cast_injective h)

end Ostmann

end OAI
