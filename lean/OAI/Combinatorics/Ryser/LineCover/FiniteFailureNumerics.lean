import OAI.Combinatorics.Ryser.LineCover.SamplingNumerics

namespace OAI

namespace RyserCoveringCounterexample.LineCover

private theorem half_sq_le_descFactorial_two (m : ℕ) (hm : 2 ≤ m) :
    (m : ℝ) ^ 2 / 2 ≤ (m.descFactorial 2 : ℝ) := by
  have hm1 : 1 ≤ m := (by decide : 1 ≤ 2).trans hm
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hhalf : (m : ℝ) / 2 ≤ (m : ℝ) - 1 := by linarith
  have hmul := mul_le_mul_of_nonneg_right hhalf (Nat.cast_nonneg m)
  have hfactor : m.descFactorial 2 = (m - 1) * m := by
    simpa only [Nat.descFactorial_one] using Nat.descFactorial_succ m 1
  rw [hfactor, Nat.cast_mul, Nat.cast_sub hm1, Nat.cast_one]
  nlinarith only [hmul]

private theorem half_le_nat_sub_cast (m j : ℕ) (h : 2 * j ≤ m) :
    (m : ℝ) / 2 ≤ ((m - j : ℕ) : ℝ) := by
  have hjm : j ≤ m := (Nat.le_mul_of_pos_left j (by decide : 0 < 2)).trans h
  have hR : (2 : ℝ) * j ≤ m := by exact_mod_cast h
  rw [Nat.cast_sub hjm]
  linarith

theorem low_sampling_failure_le_coarse (m D R t h K : ℕ) (P δ : ℝ)
    (hm : 4 ≤ m) (hδ : 0 < δ) (hlarge : 4 * h ≤ m) (hP : 0 ≤ P) :
    2 * P / (δ * (m.descFactorial 2 : ℝ)) +
      ((2 * t).descFactorial 2 : ℝ) * R / ((m - 1 : ℕ) : ℝ) +
      ((2 * t).descFactorial 3 : ℝ) * R / ((m - 2 : ℕ) : ℝ) +
      (K : ℝ) * (t : ℝ) ^ (2 * h) * ((m * D * R : ℕ) : ℝ) ^ h /
        (m.descFactorial (2 * h) : ℝ) ≤
    4 * P / (δ * (m : ℝ) ^ 2) +
      8 * (t : ℝ) ^ 2 * R / m +
      16 * (t : ℝ) ^ 3 * R / m +
      (K : ℝ) * (4 * (D : ℝ) * (t : ℝ) ^ 2 * R / m) ^ h := by
  have hmpos : 0 < m := lt_of_lt_of_le (by decide : 0 < 4) hm
  have hmR : (0 : ℝ) < m := by exact_mod_cast hmpos
  have hpairden : δ * ((m : ℝ) ^ 2 / 2) ≤ δ * (m.descFactorial 2 : ℝ) :=
    mul_le_mul_of_nonneg_left
      (half_sq_le_descFactorial_two m ((by decide : 2 ≤ 4).trans hm)) hδ.le
  have hpair : 2 * P / (δ * (m.descFactorial 2 : ℝ)) ≤
      4 * P / (δ * (m : ℝ) ^ 2) := by
    calc
      _ ≤ 2 * P / (δ * ((m : ℝ) ^ 2 / 2)) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hpairden
      _ = _ := by
        field_simp [hδ.ne', hmR.ne']
        ring
  have htwo : ((2 * t).descFactorial 2 : ℝ) ≤ 4 * (t : ℝ) ^ 2 := by
    calc
      _ ≤ ((2 * t : ℕ) : ℝ) ^ 2 := by
        exact_mod_cast Nat.descFactorial_le_pow (2 * t) 2
      _ = _ := by
        rw [Nat.cast_mul, Nat.cast_ofNat]
        ring
  have hthree : ((2 * t).descFactorial 3 : ℝ) ≤ 8 * (t : ℝ) ^ 3 := by
    calc
      _ ≤ ((2 * t : ℕ) : ℝ) ^ 3 := by
        exact_mod_cast Nat.descFactorial_le_pow (2 * t) 3
      _ = _ := by
        rw [Nat.cast_mul, Nat.cast_ofNat]
        ring
  have hsub1 : (m : ℝ) / 2 ≤ ((m - 1 : ℕ) : ℝ) :=
    half_le_nat_sub_cast m 1 ((by decide : 2 * 1 ≤ 4).trans hm)
  have hsub2 : (m : ℝ) / 2 ≤ ((m - 2 : ℕ) : ℝ) :=
    half_le_nat_sub_cast m 2 hm
  have hparallel : ((2 * t).descFactorial 2 : ℝ) * R /
      ((m - 1 : ℕ) : ℝ) ≤ 8 * (t : ℝ) ^ 2 * R / m := by
    calc
      _ ≤ (4 * (t : ℝ) ^ 2 * R) / ((m : ℝ) / 2) :=
        div_le_div₀ (by positivity)
          (mul_le_mul_of_nonneg_right htwo (Nat.cast_nonneg R)) (by positivity) hsub1
      _ = _ := by
        field_simp [hmR.ne']
        ring
  have hconcurrent : ((2 * t).descFactorial 3 : ℝ) * R /
      ((m - 2 : ℕ) : ℝ) ≤ 16 * (t : ℝ) ^ 3 * R / m := by
    calc
      _ ≤ (8 * (t : ℝ) ^ 3 * R) / ((m : ℝ) / 2) :=
        div_le_div₀ (by positivity)
          (mul_le_mul_of_nonneg_right hthree (Nat.cast_nonneg R)) (by positivity) hsub2
      _ = _ := by
        field_simp [hmR.ne']
        ring
  have hoccupancy :
      (K : ℝ) * (t : ℝ) ^ (2 * h) * ((m * D * R : ℕ) : ℝ) ^ h /
          (m.descFactorial (2 * h) : ℝ) ≤
        (K : ℝ) * (4 * (D : ℝ) * (t : ℝ) ^ 2 * R / m) ^ h := by
    simpa only [Nat.cast_mul, mul_assoc, mul_div_assoc] using
      mul_le_mul_of_nonneg_left (low_occupancy_quotient_le m D R t h hmpos hlarge)
        (Nat.cast_nonneg K)
  exact add_le_add (add_le_add (add_le_add hpair hparallel) hconcurrent) hoccupancy

theorem high_occupancy_term_le_coarse (R N D t h K : ℕ)
    (hR : 0 < R) (hN : 0 < N) (hRlarge : 2 * h ≤ R) (hNlarge : 2 * h ≤ N) :
    (K : ℝ) * (t.descFactorial h : ℝ) ^ 2 * ((D * N : ℕ) : ℝ) ^ h /
        ((R.descFactorial h : ℝ) * (N.descFactorial h : ℝ)) ≤
      (K : ℝ) * (4 * (D : ℝ) * (t : ℝ) ^ 2 / R) ^ h := by
  have hfall : (t.descFactorial h : ℝ) ≤ (t : ℝ) ^ h := by
    exact_mod_cast Nat.descFactorial_le_pow t h
  have hfall2 : (t.descFactorial h : ℝ) ^ 2 ≤ (t : ℝ) ^ (2 * h) :=
    (pow_le_pow_left₀ (Nat.cast_nonneg _) hfall 2).trans_eq
      (pow_mul' (t : ℝ) 2 h).symm
  have hnum : (t.descFactorial h : ℝ) ^ 2 * ((D : ℝ) * N) ^ h ≤
      (t : ℝ) ^ (2 * h) * ((D : ℝ) * N) ^ h :=
    mul_le_mul_of_nonneg_right hfall2 (by positivity)
  have hratio :
      (t.descFactorial h : ℝ) ^ 2 * ((D : ℝ) * N) ^ h /
          ((R.descFactorial h : ℝ) * (N.descFactorial h : ℝ)) ≤
        (4 * (D : ℝ) * (t : ℝ) ^ 2 / R) ^ h :=
    (div_le_div_of_nonneg_right hnum
      (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))).trans
        (high_occupancy_quotient_le R N D t h hR hN hRlarge hNlarge)
  simpa only [Nat.cast_mul, mul_assoc, mul_div_assoc] using
    mul_le_mul_of_nonneg_left hratio (Nat.cast_nonneg K)

end RyserCoveringCounterexample.LineCover

end OAI
