import OAI.NumberTheory.TwoPoint.Walks.RetainedRowScale

namespace OAI

/-! The manuscript's final exponential savings at eta = exp(-J),
K = exp(4J), and a fixed sufficiently large W. -/

namespace TwoPointCorrelations

lemma two_pow_eq_exp (J : ℕ) : (2 : ℝ) ^ J = Real.exp ((J : ℝ) * Real.log 2) := by
  rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num)]
  congr 1
  ring

lemma quantitative_small_terms (L W : ℝ) (J : ℕ) (hL : 1 ≤ L) (hW : 1 ≤ W)
    (hJ : 60 * (J : ℝ) ≤ Real.log L) :
    Real.exp J * (2 : ℝ) ^ J * L ^ (-1 / 20 : ℝ) ≤ Real.exp (-(J : ℝ)) ∧
    (2 : ℝ) ^ J * Real.exp (-4 * (J : ℝ)) ≤ Real.exp (-(J : ℝ)) ∧
    (2 : ℝ) ^ J * L ^ (-100 : ℝ) ≤ Real.exp (-(J : ℝ)) ∧
    (2 : ℝ) ^ J * Real.exp (-2 * W * J) ≤ Real.exp (-(J : ℝ)) := by
  have hLp : 0 < L := by linarith
  have hJ0 : (0 : ℝ) ≤ J := Nat.cast_nonneg _
  have hlog : 0 ≤ Real.log L := Real.log_nonneg hL
  have hlogtwo : Real.log 2 ≤ 1 := by
    have ht := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    linarith
  have htwo : (J : ℝ) * Real.log 2 ≤ J := by nlinarith
  have hWJ : (J : ℝ) ≤ W * J := by nlinarith
  rw [two_pow_eq_exp]
  simp only [Real.rpow_def_of_pos hLp]
  repeat rw [← Real.exp_add]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> apply Real.exp_le_exp.mpr <;> nlinarith

lemma quantitative_spectral_term (C W : ℝ) (J : ℕ) (hC : 0 ≤ C) (hW : 0 < W)
    (hchoice : Real.exp 5 * (C / Real.sqrt W) ≤ Real.exp (-1)) :
    Real.exp (5 * (J : ℝ)) * (C / Real.sqrt W) ^ J ≤ Real.exp (-(J : ℝ)) := by
  have he : Real.exp (5 * (J : ℝ)) = (Real.exp 5) ^ J := by
    rw [mul_comm, Real.exp_nat_mul]
  rw [he, ← mul_pow]
  have hp := pow_le_pow_left₀ (mul_nonneg (Real.exp_pos _).le (by positivity)) hchoice J
  calc
    _ ≤ (Real.exp (-1)) ^ J := hp
    _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring

lemma primeSupplyCount_final_budget (L W : ℝ) (hL : 1 ≤ L) (hW : 1 ≤ W) :
    60 * (primeSupplyCount W L : ℝ) ≤ Real.log L := by
  have hj := primeSupplyCount_mul_bound W L (by linarith) hL
  have hJ0 : (0 : ℝ) ≤ primeSupplyCount W L := Nat.cast_nonneg _
  nlinarith

lemma primeSupplyCount_saving (L W : ℝ) (hL : 1 ≤ L) (_hW : 0 < W) :
    Real.exp (-(primeSupplyCount W L : ℝ)) ≤
      Real.exp 1 * L ^ (-(1 / (1200 * W)) : ℝ) := by
  have hLp : 0 < L := by linarith
  have hf := Nat.lt_floor_add_one (((1 / 200 : ℝ) * Real.log L) / (6 * W))
  have he : ((1 / 200 : ℝ) * Real.log L) / (6 * W) = Real.log L / (1200 * W) := by ring
  change ((1 / 200 : ℝ) * Real.log L) / (6 * W) < (primeSupplyCount W L : ℝ) + 1 at hf
  rw [he] at hf
  rw [Real.rpow_def_of_pos hLp, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hz : Real.log L * (-(1 / (1200 * W))) = -(Real.log L / (1200 * W)) := by ring
  rw [hz]
  linarith

lemma exists_fixed_spectral_parameter (C : ℝ) (hC : 0 ≤ C) :
    ∃ W : ℝ, 10 ≤ W ∧ Real.exp 5 * (C / Real.sqrt W) ≤ Real.exp (-1) := by
  let a := Real.exp 6 * C + 4
  have ha : 4 ≤ a := by
    have hp := mul_nonneg (Real.exp_pos (6 : ℝ)).le hC
    dsimp only [a]
    linarith
  have hap : 0 < a := by linarith
  refine ⟨a ^ 2, by nlinarith, ?_⟩
  rw [Real.sqrt_sq hap.le, ← mul_div_assoc]
  apply (div_le_iff₀ hap).mpr
  have he : Real.exp (-1) * Real.exp 6 = Real.exp 5 := by
    rw [← Real.exp_add]
    norm_num
  dsimp [a]
  rw [mul_add, ← mul_assoc, he]
  linarith [Real.exp_pos (-1)]

end TwoPointCorrelations

end OAI
