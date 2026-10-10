import OAI.NumberTheory.Ostmann.Quadratic.QuadraticMainSupport

namespace OAI

/-! # The divisor bound for the actual main-term difference coefficients -/

namespace Ostmann

open scoped Classical BigOperators

private theorem abs_moebius_index_sum (S : Finset ℕ) (a e w : ℕ) (ha : 0 < a)
    (hea : e ∣ a) :
    |∑ b ∈ S, if a * b = w then ArithmeticFunction.moebius e else 0| ≤
      if e ∣ w then (1 : ℤ) else 0 := by
  by_cases hx : ∃ b ∈ S, a * b = w
  · obtain ⟨b, hb, heq⟩ := hx
    have hew : e ∣ w := heq ▸ dvd_mul_of_dvd_left hea b
    rw [ite_eq_left hew]
    have hs : (∑ c ∈ S, if a * c = w then ArithmeticFunction.moebius e else 0) =
        ArithmeticFunction.moebius e := by
      rw [Finset.sum_eq_single_of_mem b hb]
      · simp [heq]
      · intro c _ hcb
        apply ite_eq_right
        intro hc
        have hbc : c = b := by nlinarith
        exact hcb hbc
    rw [hs]
    exact ArithmeticFunction.abs_moebius_le_one
  · have hz : (∑ b ∈ S, if a * b = w then ArithmeticFunction.moebius e else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro b hb
      exact ite_eq_right (fun heq => hx ⟨b, hb, heq⟩)
    rw [hz, abs_zero]
    split_ifs <;> norm_num

private theorem common_divisor_count_le (D w : ℕ) (hw : w ≠ 0) :
    (∑ e ∈ D.divisors, if e ∣ w then (1 : ℤ) else 0) ≤ w.divisors.card := by
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
  exact_mod_cast Finset.card_le_card (show D.divisors.filter (fun e => e ∣ w) ⊆ w.divisors from by
    intro e he
    exact Nat.mem_divisors.mpr ⟨(Finset.mem_filter.mp he).2, hw⟩)

 theorem quadraticMainAlpha_abs_le (D K w : ℕ) (hw : w ≠ 0) :
    |quadraticMainAlpha D K w| ≤ w.divisors.card := by
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ e ∈ D.divisors, if e ∣ w then (1 : ℤ) else 0 := by
      apply Finset.sum_le_sum
      intro e he
      exact abs_moebius_index_sum _ e e w (Nat.pos_of_mem_divisors he) dvd_rfl
    _ ≤ _ := common_divisor_count_le D w hw

 theorem quadraticMainBeta_abs_le (D K w : ℕ) (hw : w ≠ 0) :
    |quadraticMainBeta D K w| ≤ w.divisors.card := by
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ u ∈ D.divisors, if u ∣ w then (1 : ℤ) else 0 := by
      apply Finset.sum_le_sum
      intro u hu
      exact abs_moebius_index_sum _ (u ^ 2) u w
        (pow_pos (Nat.pos_of_mem_divisors hu) 2) (dvd_pow_self u (by decide : 2 ≠ 0))
    _ ≤ _ := common_divisor_count_le D w hw

 theorem quadraticMainGamma_abs_le (D K w : ℕ) (hw : w ≠ 0) :
    |quadraticMainGamma D K w| ≤ 2 * (w.divisors.card : ℤ) := by
  have hh := (abs_sub (quadraticMainAlpha D K w) (quadraticMainBeta D K w)).trans
    (add_le_add (quadraticMainAlpha_abs_le D K w hw) (quadraticMainBeta_abs_le D K w hw))
  simpa only [quadraticMainGamma, two_mul] using hh

end Ostmann

end OAI
