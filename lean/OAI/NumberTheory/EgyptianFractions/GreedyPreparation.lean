import OAI.NumberTheory.EgyptianFractions.GreedyStep

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337

/-- A prefix ending either at zero or at a denominator in the target window. -/
def PreparedGreedyPrefix (a b : ℕ) (T : ℝ) (N : ℕ) : Prop :=
  ∃ (l : List ℕ) (A C : ℕ),
    l.length ≤ N ∧ (∀ d ∈ l, 2 ≤ d) ∧ A ≤ a ∧ 0 < C ∧
    (l.map (fun d => (1 : ℚ) / (d : ℚ))).sum + (A : ℚ) / (C : ℚ) =
      (a : ℚ) / (b : ℚ) ∧
    (A = 0 ∨ (1 ≤ A ∧ T ≤ (C : ℝ) ∧ (C : ℝ) < T ^ 2))

/-- A greedy step decreases the numerator and squares the remaining value. -/
theorem ordinary_greedy_step_bounded (a b : ℕ) (ha : 0 < a) (hab : a < b) :
    ∃ z c : ℕ, 2 ≤ z ∧ z ≤ b ∧ c < a ∧
      (a : ℚ) / (b : ℚ) = (1 : ℚ) / (z : ℚ) +
        (c : ℚ) / ((b * z : ℕ) : ℚ) ∧
      (c : ℝ) / ((b * z : ℕ) : ℝ) ≤ ((a : ℝ) / (b : ℝ)) ^ 2 ∧
      (c : ℝ) / ((b * z : ℕ) : ℝ) < 1 / 2 := by
  have hb : 0 < b := lt_trans ha hab
  by_cases hr : b % a = 0
  · obtain ⟨hz, hsplit⟩ := greedy_terminal_data a b ha hab hr
    refine ⟨b / a, 0, hz, Nat.div_le_self b a, ha, ?_, ?_, ?_⟩
    · simpa using hsplit
    · simp only [Nat.cast_zero, zero_div]
      positivity
    · norm_num
  · obtain ⟨z, c, hz, hc, hca, hcbz, hsplit, htail⟩ :=
      greedy_step_data a b ha hab hr
    have hz0 : 0 < z := by omega
    have hbQ : (b : ℚ) ≠ 0 := by positivity
    have hzQ : (z : ℚ) ≠ 0 := by positivity
    have heqQ : (a : ℚ) * z = b + c := by
      push_cast at hsplit
      field_simp at hsplit
      nlinarith
    have heq : a * z = b + c := by exact_mod_cast heqQ
    have hzb : z ≤ b := by
      by_contra h
      have hz' : b + 1 ≤ z := by omega
      have hmul := Nat.mul_le_mul_left a hz'
      have hba : b ≤ a * b := by nlinarith
      nlinarith
    have hbR : (0 : ℝ) < b := by positivity
    have hzR : (0 : ℝ) < z := by positivity
    have hcaR : (c : ℝ) < a := by exact_mod_cast hca
    have habR : (a : ℝ) < b := by exact_mod_cast hab
    have hz2R : (2 : ℝ) ≤ z := by exact_mod_cast hz
    have heqR : (a : ℝ) * z = b + c := by exact_mod_cast heq
    have haR : (0 : ℝ) < a := by positivity
    have hcR : (0 : ℝ) < c := by positivity
    refine ⟨z, c, hz, hzb, hca, hsplit, ?_, ?_⟩
    · push_cast
      rw [div_pow]
      apply (div_le_div_iff₀ (mul_pos hbR hzR) (pow_pos hbR 2)).2
      have hh : (c : ℝ) * b ≤ (a : ℝ) ^ 2 * z := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_right hh hbR.le]
    · push_cast
      apply (div_lt_iff₀ (mul_pos hbR hzR)).2
      nlinarith

/-- The finite stopping argument needs only the squaring estimate for a greedy step. -/
theorem greedy_preparation_of_squaring
    (step : ∀ a b : ℕ, 0 < a → a < b →
      ∃ z c : ℕ, 2 ≤ z ∧ z ≤ b ∧ c < a ∧
        (a : ℚ) / (b : ℚ) = (1 : ℚ) / (z : ℚ) +
          (c : ℚ) / ((b * z : ℕ) : ℚ) ∧
        (c : ℝ) / ((b * z : ℕ) : ℝ) ≤ ((a : ℝ) / (b : ℝ)) ^ 2)
    (N : ℕ) :
    ∀ (a b : ℕ) (T u : ℝ), 0 < a → a < b → 1 < T →
      (b : ℝ) < T ^ 2 → 0 ≤ u → (a : ℝ) / (b : ℝ) ≤ u →
      T * u ^ (2 ^ N) ≤ 1 → PreparedGreedyPrefix a b T N := by
  induction N with
  | zero =>
    intro a b T u ha hab hT hbT hu hxu hcap
    have hb : (0 : ℝ) < b := by exact_mod_cast (lt_trans ha hab)
    have haR : (1 : ℝ) ≤ a := by exact_mod_cast ha
    have hmul : (a : ℝ) ≤ u * b := (div_le_iff₀ hb).1 hxu
    have hu0 : 0 < u := by nlinarith
    have hTb : T ≤ (b : ℝ) := by
      simp only [pow_zero, pow_one] at hcap
      nlinarith
    refine ⟨[], a, b, by simp, by simp, le_rfl, by omega, ?_, Or.inr ?_⟩
    · simp
    · exact ⟨ha, hTb, hbT⟩
  | succ N ih =>
    intro a b T u ha hab hT hbT hu hxu hcap
    by_cases hTb : T ≤ (b : ℝ)
    · refine ⟨[], a, b, by simp, by simp, le_rfl, by omega, ?_, Or.inr ?_⟩
      · simp
      · exact ⟨ha, hTb, hbT⟩
    have hb_lt : (b : ℝ) < T := lt_of_not_ge hTb
    obtain ⟨z, c, hz, hzb, hca, hsplit, hsq⟩ := step a b ha hab
    have hb : 0 < b := lt_trans ha hab
    have hz0 : 0 < z := by omega
    have hbz : 0 < b * z := Nat.mul_pos hb hz0
    by_cases hc : c = 0
    · refine ⟨[z], 0, 1, by simp, ?_, by omega, by omega, ?_, Or.inl rfl⟩
      · simpa using hz
      · simpa [hc] using hsplit.symm
    have hc0 : 0 < c := Nat.pos_of_ne_zero hc
    have hcbz : c < b * z := by nlinarith
    have hbzT : ((b * z : ℕ) : ℝ) < T ^ 2 := by
      have hbR : (0 : ℝ) < b := by exact_mod_cast hb
      have hzbR : (z : ℝ) ≤ b := by exact_mod_cast hzb
      push_cast
      nlinarith
    have hxu0 : 0 ≤ (a : ℝ) / (b : ℝ) := by positivity
    have hcu : (c : ℝ) / ((b * z : ℕ) : ℝ) ≤ u ^ 2 := by
      calc
        _ ≤ ((a : ℝ) / (b : ℝ)) ^ 2 := hsq
        _ ≤ u ^ 2 := pow_le_pow_left₀ hxu0 hxu 2
    have hcap' : T * (u ^ 2) ^ (2 ^ N) ≤ 1 := by
      have hex : 2 * 2 ^ N = 2 ^ (N + 1) := by simp [pow_succ, Nat.mul_comm]
      rw [← pow_mul, hex]
      exact hcap
    obtain ⟨l, A, C, hlen, hden, hAa, hC, hsum, halt⟩ :=
      ih c (b * z) T (u ^ 2) hc0 hcbz hT hbzT (sq_nonneg u) hcu hcap'
    refine ⟨z :: l, A, C, ?_, ?_, le_trans hAa (Nat.le_of_lt hca), hC, ?_, halt⟩
    · simp only [List.length_cons]
      omega
    · intro d hd
      rcases List.mem_cons.mp hd with rfl | hd
      · exact hz
      · exact hden d hd
    · change (1 : ℚ) / (z : ℚ) + (l.map (fun d => (1 : ℚ) / (d : ℚ))).sum +
        (A : ℚ) / (C : ℚ) = (a : ℚ) / (b : ℚ)
      linarith

/-- Prefixes may be prefixed by a single valid unit-fraction step. -/
theorem PreparedGreedyPrefix.prepend {a b z c N : ℕ} {T : ℝ}
    (h : PreparedGreedyPrefix c (b * z) T N) (hz : 2 ≤ z) (hca : c ≤ a)
    (hsplit : (a : ℚ) / (b : ℚ) = (1 : ℚ) / (z : ℚ) +
      (c : ℚ) / ((b * z : ℕ) : ℚ)) : PreparedGreedyPrefix a b T (N + 1) := by
  obtain ⟨l, A, C, hlen, hden, hAc, hC, hsum, halt⟩ := h
  refine ⟨z :: l, A, C, ?_, ?_, le_trans hAc hca, hC, ?_, halt⟩
  · simp only [List.length_cons]
    omega
  · intro d hd
    rcases List.mem_cons.mp hd with rfl | hd
    · exact hz
    · exact hden d hd
  · change (1 : ℚ) / (z : ℚ) + (l.map (fun d => (1 : ℚ) / (d : ℚ))).sum +
      (A : ℚ) / (C : ℚ) = (a : ℚ) / (b : ℚ)
    linarith

/-- Quantitative denominator preparation: `N+1` steps suffice as soon as
`T ≤ 2^(2^N)`. No reduction of the remaining fraction is performed. -/
theorem greedy_preparation_power (a b N : ℕ) (T : ℝ)
    (ha : 0 < a) (hab : a < b) (hbT : (b : ℝ) < T)
    (hTcap : T ≤ (2 : ℝ) ^ (2 ^ N)) : PreparedGreedyPrefix a b T (N + 1) := by
  obtain ⟨z, c, hz, hzb, hca, hsplit, hsq, hhalf⟩ := ordinary_greedy_step_bounded a b ha hab
  have hb : 0 < b := lt_trans ha hab
  have hz0 : 0 < z := by omega
  have hbz : 0 < b * z := Nat.mul_pos hb hz0
  have hT : 1 < T := by
    have hb2 : (2 : ℝ) ≤ b := by exact_mod_cast (show 2 ≤ b by omega)
    linarith
  by_cases hc : c = 0
  · refine ⟨[z], 0, 1, by simp, ?_, by omega, by omega, ?_, Or.inl rfl⟩
    · simpa using hz
    · simpa [hc] using hsplit.symm
  have hc0 : 0 < c := Nat.pos_of_ne_zero hc
  have hcbz : c < b * z := by nlinarith
  have hbzT : ((b * z : ℕ) : ℝ) < T ^ 2 := by
    have hbR : (0 : ℝ) < b := by positivity
    have hzbR : (z : ℝ) ≤ b := by exact_mod_cast hzb
    push_cast
    nlinarith
  have hcap : T * (1 / 2 : ℝ) ^ (2 ^ N) ≤ 1 := by
    rw [one_div_pow, mul_one_div]
    exact (div_le_one (by positivity)).2 hTcap
  have step : ∀ a b : ℕ, 0 < a → a < b →
      ∃ z c : ℕ, 2 ≤ z ∧ z ≤ b ∧ c < a ∧
        (a : ℚ) / (b : ℚ) = (1 : ℚ) / (z : ℚ) +
          (c : ℚ) / ((b * z : ℕ) : ℚ) ∧
        (c : ℝ) / ((b * z : ℕ) : ℝ) ≤ ((a : ℝ) / (b : ℝ)) ^ 2 := by
    intro a b ha hab
    obtain ⟨z, c, hz, hzb, hca, hsplit, hsq, _⟩ := ordinary_greedy_step_bounded a b ha hab
    exact ⟨z, c, hz, hzb, hca, hsplit, hsq⟩
  have hp := greedy_preparation_of_squaring step N c (b * z) T (1 / 2)
    hc0 hcbz hT hbzT (by norm_num) (le_of_lt hhalf) hcap
  exact hp.prepend hz (Nat.le_of_lt hca) hsplit

/-- Equivalent stopping bound in the form convenient for logarithmic budgets. -/
theorem greedy_preparation (a b N : ℕ) (T : ℝ)
    (ha : 0 < a) (hab : a < b) (hbT : (b : ℝ) < T)
    (hcap : T * (1 / 2 : ℝ) ^ (2 ^ N) ≤ 1) :
    PreparedGreedyPrefix a b T (N + 1) := by
  apply greedy_preparation_power a b N T ha hab hbT
  rw [one_div_pow, mul_one_div] at hcap
  exact (div_le_one (by positivity)).1 hcap

end Problem337

end

end OAI
