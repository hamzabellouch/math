import OAI.NumberTheory.Ostmann.ZeroDensity.UnsignedPrimeMass

namespace OAI

/-! # A sufficient tail estimate from the prime mass at a smaller exponent -/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def unsignedPrimeTail (Q : ℕ) (s : ℝ) (n : ℕ) : ℝ :=
  if Q < n then unsignedPrimeTerm s n else 0

theorem unsignedPrimeTail_nonneg (Q : ℕ) (s : ℝ) (n : ℕ) :
    0 ≤ unsignedPrimeTail Q s n := by
  unfold unsignedPrimeTail
  split_ifs
  · exact unsignedPrimeTerm_nonneg s n
  · exact le_refl _

theorem unsignedPrimeTail_pointwise (Q : ℕ) (s : ℝ) (hQ : 0 < Q) (hs : 1 < s) (n : ℕ) :
    unsignedPrimeTail Q s n ≤
      (Q : ℝ) ^ (-(s - 1) / 2) * unsignedPrimeTerm ((s + 1) / 2) n := by
  by_cases hnQ : Q < n
  · rw [unsignedPrimeTail, ite_eq_left hnQ]
    by_cases hp : n.Prime
    · rw [unsignedPrimeTerm, unsignedPrimeTerm, ite_eq_left hp, ite_eq_left hp]
      have hn : (0 : ℝ) < n := by exact_mod_cast hp.pos
      have hq : (0 : ℝ) < Q := by exact_mod_cast hQ
      have hlog : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
      have ha : 0 ≤ (s - 1) / 2 := by linarith
      have hpow : (Q : ℝ) ^ ((s - 1) / 2) ≤ (n : ℝ) ^ ((s - 1) / 2) :=
        Real.rpow_le_rpow hq.le (by exact_mod_cast hnQ.le) ha
      have heq : s = (s + 1) / 2 + (s - 1) / 2 := by ring
      calc
        Real.log n / (n : ℝ) ^ s =
            (Real.log n / (n : ℝ) ^ ((s + 1) / 2)) / (n : ℝ) ^ ((s - 1) / 2) := by
          conv_lhs => rw [heq, Real.rpow_add hn]
          exact div_mul_eq_div_div _ _ _
        _ ≤ (Real.log n / (n : ℝ) ^ ((s + 1) / 2)) / (Q : ℝ) ^ ((s - 1) / 2) :=
          div_le_div_of_nonneg_left (div_nonneg hlog (Real.rpow_nonneg hn.le _))
            (Real.rpow_pos_of_pos hq _) hpow
        _ = _ := by
          rw [show -(s - 1) / 2 = -((s - 1) / 2) by ring, Real.rpow_neg hq.le]
          ring
    · simp only [unsignedPrimeTerm, ite_eq_right hp, mul_zero, le_refl]
  · rw [unsignedPrimeTail, ite_eq_right hnQ]
    exact mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg Q) _) (unsignedPrimeTerm_nonneg _ n)

theorem exists_unsignedPrimeTail_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (Q : ℕ) (s : ℝ), 0 < Q → 1 < s → s ≤ 2 →
      Summable (unsignedPrimeTail Q s) ∧
      (∑' n, unsignedPrimeTail Q s n) ≤
        (Q : ℝ) ^ (-(s - 1) / 2) * (2 / (s - 1) + C) := by
  obtain ⟨C, hC, hmass⟩ := exists_unsignedPrimeMass_error
  refine ⟨C, hC, ?_⟩
  intro Q s hQ hs hs2
  have hs0 : 1 < (s + 1) / 2 := by linarith
  have hs02 : (s + 1) / 2 ≤ 2 := by linarith
  obtain ⟨hm, hb⟩ := hmass ((s + 1) / 2) hs0 hs02
  have hmaj := hm.mul_left ((Q : ℝ) ^ (-(s - 1) / 2))
  have htail : Summable (unsignedPrimeTail Q s) :=
    Summable.of_nonneg_of_le (unsignedPrimeTail_nonneg Q s)
      (unsignedPrimeTail_pointwise Q s hQ hs) hmaj
  refine ⟨htail, ?_⟩
  have htotal : (∑' n, unsignedPrimeTerm ((s + 1) / 2) n) ≤ 2 / (s - 1) + C := by
    have hh := (abs_le.mp hb).2
    have hfrac : 1 / ((s + 1) / 2 - 1) = 2 / (s - 1) := by
      rw [show (s + 1) / 2 - 1 = (s - 1) / 2 by ring, div_div_eq_mul_div]
      norm_num
    rw [hfrac] at hh
    linarith
  have ht := htail.tsum_le_tsum (unsignedPrimeTail_pointwise Q s hQ hs) hmaj
  rw [hm.tsum_mul_left] at ht
  exact ht.trans (mul_le_mul_of_nonneg_left htotal (Real.rpow_nonneg (Nat.cast_nonneg Q) _))

end Ostmann

end OAI
