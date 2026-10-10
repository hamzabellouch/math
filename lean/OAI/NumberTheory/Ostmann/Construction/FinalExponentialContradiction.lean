import OAI.NumberTheory.Ostmann.Construction.FinalFactorialBudget
import OAI.NumberTheory.Ostmann.Construction.FinalPermutationComparison

namespace OAI

/-! # The quantitative contradiction at the final permutation stage -/

namespace Ostmann

theorem final_exponential_contradiction (n m : ℕ) (B₁ D C δ T B E : ℝ) (η : ℂ)
    (hT : T ≤ Real.exp (D * (2 ^ (n + 1) : ℝ) * m))
    (hB0 : 0 ≤ B) (hE0 : 0 ≤ E)
    (hB : B ≤ Real.exp (C * (2 ^ (n + 1) : ℝ) * m))
    (hE : E ≤ Real.exp (-(D + 2 * B₁ + δ) * (2 ^ (n + 1) : ℝ) * m))
    (hentropy : C + D + 2 * B₁ + δ ≤ (n : ℝ) * Real.log 2 - 1)
    (hmargin : Real.log 2 < δ * (2 ^ (n + 1) : ℝ) * m)
    (hlower : Real.exp (-B₁ * (2 ^ (n + 1) : ℝ) * m) ≤ ‖η‖)
    (hcompare : ‖η‖ ^ 2 ≤ T *
      (B / (Fintype.card (FinalParityReassignments n m) : ℝ) + E)) : False := by
  let s : ℝ := (2 ^ (n + 1) : ℝ) * m
  have hcard : 0 < (Fintype.card (FinalParityReassignments n m) : ℝ) := by
    exact_mod_cast Fintype.card_pos (α := FinalParityReassignments n m)
  have hdiag : B / (Fintype.card (FinalParityReassignments n m) : ℝ) ≤
      Real.exp (-(D + 2 * B₁ + δ) * s) := by
    apply (div_le_div_of_nonneg_right hB hcard.le).trans
    simpa only [s, mul_assoc] using
      final_diagonal_entropy_bound n m (D + 2 * B₁ + δ) C (by linarith)
  have hsum : B / (Fintype.card (FinalParityReassignments n m) : ℝ) + E ≤
      2 * Real.exp (-(D + 2 * B₁ + δ) * s) := by
    have he : E ≤ Real.exp (-(D + 2 * B₁ + δ) * s) := by
      simpa only [s, mul_assoc] using hE
    linarith
  have hu : ‖η‖ ^ 2 ≤ 2 * Real.exp (-(2 * B₁ + δ) * s) := by
    apply hcompare.trans
    calc
      _ ≤ Real.exp (D * s) * (2 * Real.exp (-(D + 2 * B₁ + δ) * s)) := by
        apply mul_le_mul (by simpa only [s, mul_assoc] using hT) hsum
          (add_nonneg (div_nonneg hB0 hcard.le) hE0) (Real.exp_nonneg _)
      _ = _ := by rw [show Real.exp (D * s) * (2 * Real.exp (-(D + 2 * B₁ + δ) * s)) =
          2 * (Real.exp (D * s) * Real.exp (-(D + 2 * B₁ + δ) * s)) by ring,
          ← Real.exp_add]; congr 2; ring
  have hl : Real.exp (-(2 * B₁) * s) ≤ ‖η‖ ^ 2 := by
    have hl' : Real.exp (-B₁ * s) ≤ ‖η‖ := by simpa only [s, mul_assoc] using hlower
    have h := pow_le_pow_left₀ (Real.exp_nonneg _) hl' 2
    rw [← Real.exp_nat_mul] at h
    convert h using 1
    congr 1
    ring
  have hstrict : 2 * Real.exp (-(2 * B₁ + δ) * s) < Real.exp (-(2 * B₁) * s) := by
    rw [← Real.exp_log (by norm_num : (0 : ℝ) < 2), ← Real.exp_add]
    apply Real.exp_lt_exp.mpr
    have hm' : Real.log 2 < δ * s := by simpa only [s, mul_assoc] using hmargin
    nlinarith
  exact (not_lt_of_ge (hl.trans hu)) hstrict

end Ostmann

end OAI
