import OAI.NumberTheory.Ostmann.QuadraticSieveMainCancellation

namespace OAI

namespace Ostmann.QuadraticSieve
open scoped ArithmeticFunction.Moebius

noncomputable def truncatedMainAlpha (K Δ w : ℕ) : ℤ :=
  if Odd w then ∑ e ∈ Δ.divisors,
    if e ∣ w ∧ Squarefree (w / e) ∧ w / e ≤ K then μ e else 0 else 0

noncomputable def truncatedMainBeta (K Δ w : ℕ) : ℤ :=
  if Odd w then ∑ u ∈ Δ.divisors,
    if u ^ 2 ∣ w ∧ Squarefree (w / u ^ 2) ∧ (w / u ^ 2).Coprime Δ ∧ w / u ^ 2 ≤ K
      then μ u else 0 else 0

noncomputable def mainRemainder (K Δ w : ℕ) : ℤ :=
  truncatedMainAlpha K Δ w - truncatedMainBeta K Δ w

theorem truncatedMainAlpha_eq_of_le {K w : ℕ} (hw : w ≤ K) (Δ : ℕ) :
    truncatedMainAlpha K Δ w = if Odd w then mainAlpha Δ w else 0 := by
  have hdiv (e : ℕ) : w / e ≤ K := (Nat.div_le_self w e).trans hw
  simp only [truncatedMainAlpha, mainAlpha, hdiv, and_true]

theorem truncatedMainBeta_eq_of_le {K w : ℕ} (hw : w ≤ K) (Δ : ℕ) :
    truncatedMainBeta K Δ w = if Odd w then mainBeta Δ w else 0 := by
  have hdiv (e : ℕ) : w / e ^ 2 ≤ K := (Nat.div_le_self w (e ^ 2)).trans hw
  simp only [truncatedMainBeta, mainBeta, hdiv, and_true]

theorem mainRemainder_zero_of_le {K Δ w : ℕ} (hΔ : Δ ≠ 0) (hw : w ≤ K) :
    mainRemainder K Δ w = 0 := by
  rw [mainRemainder, truncatedMainAlpha_eq_of_le hw,
    truncatedMainBeta_eq_of_le hw, mainAlpha_eq_mainBeta hΔ, sub_self]

theorem truncatedMainAlpha_zero_of_lt {K Δ w : ℕ} (hΔ : Δ ≠ 0) (hw : K * Δ < w) :
    truncatedMainAlpha K Δ w = 0 := by
  unfold truncatedMainAlpha
  split_ifs
  · apply Finset.sum_eq_zero
    intro e he
    apply ite_eq_right
    intro h
    have heΔ : e ≤ Δ := Nat.le_of_dvd (Nat.pos_of_ne_zero hΔ) (Nat.mem_divisors.mp he).1
    have hmul := Nat.mul_le_mul heΔ h.2.2
    rw [Nat.mul_div_cancel' h.1, Nat.mul_comm] at hmul
    omega
  · rfl

theorem truncatedMainBeta_zero_of_lt {K Δ w : ℕ} (hΔ : Δ ≠ 0) (hw : K * Δ ^ 2 < w) :
    truncatedMainBeta K Δ w = 0 := by
  unfold truncatedMainBeta
  split_ifs
  · apply Finset.sum_eq_zero
    intro u hu
    apply ite_eq_right
    intro h
    have huΔ : u ≤ Δ := Nat.le_of_dvd (Nat.pos_of_ne_zero hΔ) (Nat.mem_divisors.mp hu).1
    have hmul := Nat.mul_le_mul (Nat.pow_le_pow_left huΔ 2) h.2.2.2
    rw [Nat.mul_div_cancel' h.1, Nat.mul_comm] at hmul
    omega
  · rfl

theorem mainRemainder_support {K Δ w : ℕ} (hΔ : Δ ≠ 0)
    (h : mainRemainder K Δ w ≠ 0) : Odd w ∧ K < w ∧ w ≤ K * Δ ^ 2 := by
  have ho : Odd w := by
    by_contra hn
    exact h (by simp [mainRemainder, truncatedMainAlpha, truncatedMainBeta, hn])
  have hlo : K < w := by
    by_contra hn
    exact h (mainRemainder_zero_of_le hΔ (by omega))
  refine ⟨ho, hlo, ?_⟩
  by_contra hn
  have hhi : K * Δ ^ 2 < w := by omega
  have hd : Δ ≤ Δ ^ 2 := by
    have hp := Nat.pos_of_ne_zero hΔ
    nlinarith
  have hhi' : K * Δ < w := (Nat.mul_le_mul_left K hd).trans_lt hhi
  exact h (by rw [mainRemainder, truncatedMainAlpha_zero_of_lt hΔ hhi',
    truncatedMainBeta_zero_of_lt hΔ hhi, sub_self])

theorem abs_truncatedMainAlpha_le (K Δ w : ℕ) :
    |truncatedMainAlpha K Δ w| ≤ (Δ.divisors.card : ℤ) := by
  unfold truncatedMainAlpha
  split_ifs
  · apply (Finset.abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ _e ∈ Δ.divisors, (1 : ℤ) := by
        apply Finset.sum_le_sum
        intro e he
        split_ifs
        · exact ArithmeticFunction.abs_moebius_le_one
        · norm_num
      _ = _ := by simp
  · simp

theorem abs_truncatedMainBeta_le (K Δ w : ℕ) :
    |truncatedMainBeta K Δ w| ≤ (Δ.divisors.card : ℤ) := by
  unfold truncatedMainBeta
  split_ifs
  · apply (Finset.abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ _u ∈ Δ.divisors, (1 : ℤ) := by
        apply Finset.sum_le_sum
        intro u hu
        split_ifs
        · exact ArithmeticFunction.abs_moebius_le_one
        · norm_num
      _ = _ := by simp
  · simp

theorem abs_mainRemainder_le (K Δ w : ℕ) :
    |mainRemainder K Δ w| ≤ 2 * (Δ.divisors.card : ℤ) := by
  exact (abs_sub _ _).trans (by
    have ha := abs_truncatedMainAlpha_le K Δ w
    have hb := abs_truncatedMainBeta_le K Δ w
    omega)

end Ostmann.QuadraticSieve

end OAI
