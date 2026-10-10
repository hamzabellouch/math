import OAI.Combinatorics.Ryser.Selection.PoolCounts

namespace OAI

namespace RyserCoveringCounterexample.Selection

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {n K : ℕ}

theorem prob_noFeasibleOutside_small_le {D : ℕ} (data : Data F n)
    (hdata : Bounded D data) (I : Finset (Fin n)) (T : Finset (Position n K))
    (hT : T ⊆ targetPositions I K) (hcard : T.card ≤ 2 * I.card)
    (hsmall : (2 * (I.card : ℝ)) * ((2 * (D : ℝ) ^ 3) / (Fintype.card F : ℝ)) ≤ 1) :
    (poolLaw F n K).prob (NoFeasibleOutside data I T) ≤
      ((2 * (I.card : ℝ)) * ((2 * (D : ℝ) ^ 3) / (Fintype.card F : ℝ))) ^
        ((K - 2) * I.card) := by
  have hnonneg : 0 ≤ (2 * (D : ℝ) ^ 3) / (Fintype.card F : ℝ) :=
    div_nonneg (mul_nonneg (by norm_num) (pow_nonneg (Nat.cast_nonneg D) _))
      (Nat.cast_nonneg _)
  have hbase : (T.card : ℝ) * ((2 * (D : ℝ) ^ 3) / (Fintype.card F : ℝ)) ≤
      (2 * (I.card : ℝ)) * ((2 * (D : ℝ) ^ 3) / (Fintype.card F : ℝ)) := by
    apply mul_le_mul_of_nonneg_right _ hnonneg
    exact_mod_cast hcard
  have htarget_nonneg : 0 ≤
      (2 * (I.card : ℝ)) * ((2 * (D : ℝ) ^ 3) / (Fintype.card F : ℝ)) :=
    mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) hnonneg
  calc
    _ ≤ ((T.card : ℝ) * ((2 * (D : ℝ) ^ 3) / (Fintype.card F : ℝ))) ^
        (freshTargets I T).card := prob_noFeasibleOutside_le data hdata I T
    _ ≤ ((2 * (I.card : ℝ)) * ((2 * (D : ℝ) ^ 3) / (Fintype.card F : ℝ))) ^
        (freshTargets I T).card :=
      pow_le_pow_left₀ (mul_nonneg (Nat.cast_nonneg _) hnonneg) hbase _
    _ ≤ _ := pow_le_pow_of_le_one htarget_nonneg hsmall
      (freshTargets_card_lower hT hcard)

end RyserCoveringCounterexample.Selection

end OAI
