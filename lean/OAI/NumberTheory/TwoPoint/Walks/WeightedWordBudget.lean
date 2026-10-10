import OAI.NumberTheory.TwoPoint.Walks.WeightedWordCircuit

namespace OAI

/-! Size and coefficient budgets for the actual finite-word expansion. -/

namespace TwoPointCorrelations

lemma weightedWord_coefficient_budget {R n t M : ℕ} (L : ℝ)
    (f : (Fin R → Finset (Fin n)) → BooleanCube t → ℝ)
    (hL : 4800 ≤ L) (hn : (n : ℝ) ≤ Real.exp L)
    (hM : (M : ℝ) ≤ 400 * Real.log L) (hR : (R : ℝ) ≤ 4 * L)
    (ht : (t : ℝ) ≤ L ^ 2)
    (hf : ∀ b : (Fin R → boundedActiveStates n M) × BooleanCube t,
      |f (fun r => (b.1 r).val) b.2| ≤ Real.exp (L ^ 4)) :
    (∑ b : (Fin R → boundedActiveStates n M) × BooleanCube t,
      |f (fun r => (b.1 r).val) b.2|) ≤ Real.exp (L ^ 5) := by
  have hLp : 0 ≤ L := by linarith
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have ht' : (2 : ℝ) ^ t ≤ Real.exp (L ^ 2) := by
    calc
      _ ≤ (Real.exp 1) ^ t := pow_le_pow_left₀ (by norm_num) htwo t
      _ = Real.exp (t : ℝ) := by rw [← Real.exp_nat_mul]; simp
      _ ≤ _ := Real.exp_le_exp.mpr ht
  apply (weightedWord_coefficient_mass f (Real.exp (L ^ 4)) (Real.exp_pos _).le hf).trans
  calc
    _ ≤ Real.exp (L ^ 4) * Real.exp (L ^ 2) * Real.exp (L ^ 4) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul (active_state_family_cost L n M R hL hn hM hR) ht'
          (by positivity) (by positivity)) (by positivity)
    _ = Real.exp (2 * L ^ 4 + L ^ 2) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      have h24 : L ^ 2 ≤ L ^ 4 := pow_le_pow_right₀ (by linarith : 1 ≤ L) (by norm_num)
      have h45 : 3 * L ^ 4 ≤ L ^ 5 := by
        calc
          _ ≤ L * L ^ 4 := mul_le_mul_of_nonneg_right (by linarith) (pow_nonneg hLp _)
          _ = _ := by ring
      linarith

lemma weightedStateCircuit_size_budget {R n t m : ℕ} (L : ℝ)
    (qindex : Fin R → Fin n → Fin m) (pindex : Fin t → Fin m)
    (S : Fin R → Finset (Fin n)) (bits : BooleanCube t) (c : AC0Circuit m)
    (hL : 8 ≤ L) (hn : (n : ℝ) ≤ Real.exp L) (hR : (R : ℝ) ≤ 4 * L)
    (ht : (t : ℝ) ≤ L ^ 2) (hc : (c.size : ℝ) ≤ Real.exp (L ^ 3)) :
    ((weightedStateCircuit qindex pindex S bits c).size : ℝ) ≤ Real.exp (L ^ 6) := by
  rw [weightedStateCircuit_size]
  push_cast
  have hLp : 0 ≤ L := by linarith
  have hL1 : 1 ≤ L := by linarith
  have hEL : L ≤ Real.exp L := by linarith [Real.add_one_le_exp L]
  have hE1 : (1 : ℝ) ≤ Real.exp L := Real.one_le_exp_iff.mpr hLp
  have hE8 : (8 : ℝ) ≤ Real.exp L := by linarith [Real.add_one_le_exp L]
  have hR' : (R : ℝ) * (1 + n) ≤ Real.exp (3 * L) := by
    calc
      _ ≤ (4 * L) * (2 * Real.exp L) :=
        mul_le_mul hR (by linarith) (by positivity) (by positivity)
      _ ≤ 8 * (Real.exp L * Real.exp L) := by nlinarith [Real.exp_pos L]
      _ ≤ Real.exp L * (Real.exp L * Real.exp L) :=
        mul_le_mul_of_nonneg_right hE8 (by positivity)
      _ = Real.exp (3 * L) := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have hL3 : 3 * L ≤ L ^ 3 := by nlinarith
  have hE3 : Real.exp (3 * L) ≤ Real.exp (L ^ 3) := Real.exp_le_exp.mpr hL3
  have ht' : (t : ℝ) ≤ Real.exp (L ^ 3) := by
    calc
      _ ≤ L ^ 2 := ht
      _ ≤ L ^ 3 := pow_le_pow_right₀ hL1 (by norm_num)
      _ ≤ Real.exp (L ^ 3) := by linarith [Real.add_one_le_exp (L ^ 3)]
  have hE4 : (4 : ℝ) ≤ Real.exp (L ^ 3) := by
    linarith [Real.add_one_le_exp (L ^ 3)]
  have h36 : 2 * L ^ 3 ≤ L ^ 6 := by
    have h3 : 2 ≤ L ^ 3 := by nlinarith
    nlinarith [sq_nonneg (L ^ 3 - 1)]
  calc
    _ ≤ 4 * Real.exp (L ^ 3) := by linarith [hR'.trans hE3]
    _ ≤ Real.exp (L ^ 3) * Real.exp (L ^ 3) :=
      mul_le_mul_of_nonneg_right hE4 (by positivity)
    _ = Real.exp (2 * L ^ 3) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ _ := Real.exp_le_exp.mpr h36

end TwoPointCorrelations

end OAI
