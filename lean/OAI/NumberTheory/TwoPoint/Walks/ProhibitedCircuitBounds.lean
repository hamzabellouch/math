import OAI.NumberTheory.TwoPoint.Walks.ProhibitedCircuit

namespace OAI

/-! The numerical DNF size is below the manuscript's exp(L^3) budget. -/

namespace TwoPointCorrelations

theorem prohibitedCircuit_size_quadratic (pairs : Finset (ℕ × ℕ)) (h s M : ℕ) (L : ℝ)
    (hL : 110 ≤ L) (hs : (s : ℝ) ≤ L) (hM : (M : ℝ) ≤ L ^ (2 : ℕ))
    (hpairs : (pairs.card : ℝ) ≤ Real.exp (101 * L))
    (hcap : ∀ dq ∈ pairs, (dq.2 * dq.1).primeFactors.card ≤ M) :
    ((prohibitedCircuit pairs h s).size : ℝ) ≤ Real.exp (104 * L ^ (2 : ℕ)) := by
  have hL0 : 0 ≤ L := by linarith
  have hEL : 2 ≤ Real.exp L := by linarith [Real.add_one_le_exp L]
  have hLexp : L ≤ Real.exp L := by linarith [Real.add_one_le_exp L]
  have hmax : ((max 1 (2 * pairs.card) : ℕ) : ℝ) ≤ Real.exp (102 * L) := by
    push_cast
    apply max_le
    · have he : 1 ≤ Real.exp (102 * L) := by linarith [Real.add_one_le_exp (102 * L)]
      exact he
    · calc
        2 * (pairs.card : ℝ) ≤ Real.exp L * Real.exp (101 * L) :=
          mul_le_mul hEL hpairs (Nat.cast_nonneg _) (Real.exp_pos _).le
        _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hmain : ((max 1 (2 * pairs.card) : ℕ) : ℝ) ^ s ≤ Real.exp (102 * L ^ (2 : ℕ)) := by
    calc
      _ ≤ (Real.exp (102 * L)) ^ s := pow_le_pow_left₀ (Nat.cast_nonneg _) hmax _
      _ = Real.exp (102 * L * s) := by rw [← Real.exp_nat_mul]; congr 1; ring
      _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        nlinarith [mul_le_mul_of_nonneg_left hs (show 0 ≤ 102 * L by positivity)]
  have hfirst : (s : ℝ) + 1 ≤ Real.exp L := by linarith [Real.add_one_le_exp L]
  have hlast : 1 + (s : ℝ) * M ≤ Real.exp (4 * L) := by
    have hcube : L ^ (3 : ℕ) ≤ Real.exp (3 * L) := by
      have hp := pow_le_pow_left₀ hL0 hLexp 3
      simpa only [← Real.exp_nat_mul, Nat.cast_ofNat] using hp
    have hEL3 : 1 ≤ Real.exp (3 * L) := by linarith [Real.add_one_le_exp (3 * L)]
    calc
      _ ≤ 1 + L ^ (3 : ℕ) := by
        have hm := mul_le_mul hs hM (Nat.cast_nonneg _) hL0
        nlinarith
      _ ≤ 1 + Real.exp (3 * L) := by linarith
      _ ≤ Real.exp L * Real.exp (3 * L) := by nlinarith
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hraw := prohibitedCircuit_size_le pairs h s M hcap
  have hraw' : ((prohibitedCircuit pairs h s).size : ℝ) ≤
      1 + ((s : ℝ) + 1) * ((max 1 (2 * pairs.card) : ℕ) : ℝ) ^ s * (1 + (s : ℝ) * M) := by
    exact_mod_cast hraw
  have h103 : 102 * L ^ (2 : ℕ) + 5 * L ≤ 103 * L ^ (2 : ℕ) := by nlinarith
  have hEL2 : 2 ≤ Real.exp (L ^ (2 : ℕ)) := by
    linarith [Real.add_one_le_exp (L ^ (2 : ℕ)), sq_nonneg (L - 1)]
  have hE103 : 1 ≤ Real.exp (103 * L ^ (2 : ℕ)) := by
    linarith [Real.add_one_le_exp (103 * L ^ (2 : ℕ)), sq_nonneg L]
  calc
    _ ≤ 1 + Real.exp L * Real.exp (102 * L ^ (2 : ℕ)) * Real.exp (4 * L) := by
      apply hraw'.trans
      gcongr
    _ = 1 + Real.exp (102 * L ^ (2 : ℕ) + 5 * L) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 2
      ring
    _ ≤ 1 + Real.exp (103 * L ^ (2 : ℕ)) :=
      add_le_add_right (Real.exp_le_exp.mpr h103) 1
    _ ≤ Real.exp (L ^ (2 : ℕ)) * Real.exp (103 * L ^ (2 : ℕ)) := by nlinarith
    _ = Real.exp (104 * L ^ (2 : ℕ)) := by rw [← Real.exp_add]; congr 1; ring


theorem prohibitedCircuit_size_scale (pairs : Finset (ℕ × ℕ)) (h s M : ℕ) (L : ℝ)
    (hL : 110 ≤ L) (hs : (s : ℝ) ≤ L) (hM : (M : ℝ) ≤ L ^ (2 : ℕ))
    (hpairs : (pairs.card : ℝ) ≤ Real.exp (101 * L))
    (hcap : ∀ dq ∈ pairs, (dq.2 * dq.1).primeFactors.card ≤ M) :
    ((prohibitedCircuit pairs h s).size : ℝ) ≤ Real.exp (L ^ (3 : ℕ)) := by
  apply (prohibitedCircuit_size_quadratic pairs h s M L hL hs hM hpairs hcap).trans
  apply Real.exp_le_exp.mpr
  nlinarith [mul_nonneg (show 0 ≤ L - 104 by linarith) (sq_nonneg L)]

end TwoPointCorrelations

end OAI
