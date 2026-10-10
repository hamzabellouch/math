import OAI.NumberTheory.TwoPoint.Bounds.CrudeHarmonicMass

namespace OAI

/-! Padding, mixed-difference, and external factors in the crude trace count. -/

namespace TwoPointCorrelations

open Finset

lemma crudePaddingWeight_exp_bound (q : ℕ) (L : ℝ) (hL : 1 ≤ L)
    (hq : (q.primeFactors.card : ℝ) ≤ 100 * Real.log L) :
    crudePaddingWeight q ≤ Real.exp (200 * Real.log L) := by
  have hl : 0 ≤ Real.log L := Real.log_nonneg hL
  have hlog2 : Real.log 2 ≤ 1 := by
    have ht := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hlog4 : Real.log 4 ≤ 2 := by
    have heq : Real.log 4 = 2 * Real.log 2 := by
      simpa only [Real.log_pow, Nat.cast_ofNat] using congrArg Real.log
        (show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num)
    linarith
  have hp : (q.primeFactors.card : ℝ) * Real.log 4 ≤ 200 * Real.log L := by
    calc
      _ ≤ (100 * Real.log L) * Real.log 4 :=
        mul_le_mul_of_nonneg_right hq (Real.log_nonneg (by norm_num))
      _ ≤ (100 * Real.log L) * 2 :=
        mul_le_mul_of_nonneg_left hlog4 (by positivity)
      _ = _ := by ring
  unfold crudePaddingWeight
  rw [← Real.exp_log (by norm_num : (0 : ℝ) < 4), ← Real.exp_nat_mul]
  exact Real.exp_le_exp.mpr hp

lemma crudePaddingFactors_exp_bound (R : ℕ) (q : Fin R → ℕ) (L : ℝ)
    (hL : 1 ≤ L) (hq : ∀ i, ((q i).primeFactors.card : ℝ) ≤ 100 * Real.log L) :
    (∏ i, L * crudePaddingWeight (q i)) ≤ Real.exp (201 * R * Real.log L) := by
  have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hi (i : Fin R) : L * crudePaddingWeight (q i) ≤
      Real.exp (201 * Real.log L) := by
    calc
      _ ≤ L * Real.exp (200 * Real.log L) :=
        mul_le_mul_of_nonneg_left (crudePaddingWeight_exp_bound (q i) L hL (hq i)) hLp.le
      _ = Real.exp (201 * Real.log L) := by
        conv_lhs => lhs; rw [← Real.exp_log hLp]
        rw [← Real.exp_add]
        congr 1
        ring
  calc
    _ ≤ ∏ _i : Fin R, Real.exp (201 * Real.log L) :=
      prod_le_prod₀ (fun _ _ => by unfold crudePaddingWeight; positivity) (fun i _ => hi i)
    _ = Real.exp (201 * R * Real.log L) := by
      rw [prod_const, card_univ, Fintype.card_fin, ← Real.exp_nat_mul]
      congr 1
      ring

/-- The positive trace factors left after discarding all denominator
cutoffs. This includes the full mixed-difference multiplicity. -/
noncomputable def crudeTraceWeight (R S : ℕ) (q : Fin R → ℕ) (L external : ℝ) : ℝ :=
  external * 2 ^ S * ∏ i, L * crudePaddingWeight (q i)

lemma crudeTraceWeight_nonneg (R S : ℕ) (q : Fin R → ℕ) (L external : ℝ)
    (hL : 0 ≤ L) (hexternal : 0 ≤ external) :
    0 ≤ crudeTraceWeight R S q L external := by
  unfold crudeTraceWeight crudePaddingWeight
  positivity

/-- Fixed exponential dimension factors and all step weights are
absorbed by an explicit `L log² L` cost. -/
theorem crudeTraceWeight_exp_bound (R S : ℕ) (q : Fin R → ℕ)
    (L external Cexternal Csingle : ℝ)
    (hL : 1 ≤ L) (hlog : 1 ≤ Real.log L)
    (hR : (R : ℝ) ≤ 2 * L) (hS : (S : ℝ) ≤ Csingle * L * Real.log L)
    (hCexternal : 0 ≤ Cexternal)
    (hext : external ≤ Real.exp (Cexternal * L))
    (hq : ∀ i, ((q i).primeFactors.card : ℝ) ≤ 100 * Real.log L) :
    crudeTraceWeight R S q L external ≤
      Real.exp ((Cexternal + Csingle + 402) * L * (Real.log L) ^ 2) := by
  have hpad := crudePaddingFactors_exp_bound R q L hL hq
  have hlog2 : Real.log 2 ≤ 1 := by
    have ht := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have htwo : (2 : ℝ) ^ S ≤ Real.exp (Csingle * L * (Real.log L) ^ 2) := by
    rw [← Real.exp_log (by norm_num : (0 : ℝ) < 2), ← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    have hSpos : 0 ≤ Csingle * L * Real.log L := (Nat.cast_nonneg S).trans hS
    calc
      _ ≤ (S : ℝ) := by nlinarith
      _ ≤ Csingle * L * Real.log L := hS
      _ ≤ Csingle * L * (Real.log L) ^ 2 := by
        have ht := mul_le_mul_of_nonneg_left hlog hSpos
        nlinarith
  have hext' : external ≤ Real.exp (Cexternal * L * (Real.log L) ^ 2) := by
    apply hext.trans
    apply Real.exp_le_exp.mpr
    have ht : 1 ≤ (Real.log L) ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left ht (show 0 ≤ Cexternal * L by positivity)]
  have hpad' : (∏ i, L * crudePaddingWeight (q i)) ≤
      Real.exp (402 * L * (Real.log L) ^ 2) := by
    apply hpad.trans
    apply Real.exp_le_exp.mpr
    have ht := mul_le_mul_of_nonneg_right hR (show 0 ≤ 201 * Real.log L by linarith)
    have hu := mul_le_mul_of_nonneg_left hlog (show 0 ≤ 402 * L * Real.log L by positivity)
    nlinarith
  unfold crudeTraceWeight
  calc
    _ ≤ Real.exp (Cexternal * L * (Real.log L) ^ 2) *
        Real.exp (Csingle * L * (Real.log L) ^ 2) *
        Real.exp (402 * L * (Real.log L) ^ 2) := by
      apply mul_le_mul _ hpad' (by unfold crudePaddingWeight; positivity) (by positivity)
      exact mul_le_mul hext' htwo (by positivity) (by positivity)
    _ = _ := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring

end TwoPointCorrelations

end OAI
