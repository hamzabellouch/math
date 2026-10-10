import OAI.Combinatorics.EditApproximation.Geometry.BandOptimizerWork
import OAI.Combinatorics.EditApproximation.Refinement.ComputedNumericalParameters

namespace OAI

/-! The compiled optimizer counter specialized to the literal representative
bands. Preparation of the input arrays remains a separate finite loop. -/

namespace EditApproximation

theorem computedBandActions_length_le {nx ny M : ℕ} (parent : TargetInterval nx)
    (r : TargetInterval ny) (b P : ℕ) (tau theta velocity : ℚ)
    (child : Fin M → TargetInterval ny → ℚ) :
    (computedBandActions parent r b P tau theta velocity child).length ≤
      (wideActionList M parent r b P).length := by
  dsimp only [computedBandActions]
  split_ifs <;> first | exact List.length_filter_le _ _ | exact Nat.zero_le _

theorem representativeBandActions_length_le {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (r : TargetInterval target.length)
    (b P : ℕ) (tau theta : ℚ) (child : Fin M → TargetInterval target.length → ℚ) :
    (representativeBandActions source target parent r b P tau theta child).length ≤
      (wideActionList M parent r b P).length := by
  dsimp only [representativeBandActions]
  split_ifs <;> first | exact computedBandActions_length_le _ _ _ _ _ _ _ _ | exact Nat.zero_le _

def localOptimizerArithmeticBudget (M P H : ℕ) : ℕ :=
  ((40 * P + 2) ^ (2 * M) + 1) * (M * (40 * P + 2) ^ 2 + 1) *
    (H + M * (40 * P + 2) ^ 2 + 4) ^ 210

theorem materializedRepresentativeBand_work_le {α : Type*} (source target : List α) {M : ℕ}
    (parent : TargetInterval source.length) (r : TargetInterval target.length)
    (b P H : ℕ) (hP : 0 < P) (tau theta : ℚ)
    (child : Fin M → TargetInterval target.length → ℚ) (mass : Fin M → ℚ)
    (linear : Fin M × TargetInterval target.length → ℚ) (j : ℕ)
    (hj : j ≤ (H + (bandCoordinates
      (representativeBandActions source target parent r b P tau theta child).toFinset).card + 2) ^ 80) :
    (materializedBandActionWithWork
      (representativeBandActions source target parent r b P tau theta child) mass linear
      (H + (bandCoordinates
        (representativeBandActions source target parent r b P tau theta child).toFinset).card + 2) j).2 ≤
      localOptimizerArithmeticBudget M P H := by
  let band := representativeBandActions source target parent r b P tau theta child
  have hlength : band.length ≤ (40 * P + 2) ^ (2 * M) :=
    (representativeBandActions_length_le source target parent r b P tau theta child).trans
      (wideActionList_length_le M parent r b P hP)
  have hdimension : (bandCoordinates band.toFinset).card ≤ M * (40 * P + 2) ^ 2 :=
    bandCoordinates_card_le parent r hP band
      (fun action ha => representativeBandActions_wide source target parent r b P tau theta child action ha)
  apply (materializedBandActionWithWork_optimizer_cost band mass linear _ j hj).trans
  unfold localOptimizerArithmeticBudget
  apply Nat.mul_le_mul
  · exact Nat.mul_le_mul (Nat.add_le_add_right hlength 1) (Nat.add_le_add_right hdimension 1)
  · apply Nat.pow_le_pow_left
    dsimp only [band] at hdimension
    omega

theorem localOptimizerArithmeticBudget_cap (H M P p : ℕ) (hH : 64 ≤ H) (hM : M ≤ H)
    (hP : 1 ≤ P) (hPcap : P ≤ H ^ (p + 20)) :
    localOptimizerArithmeticBudget M P H ≤
      2 * H ^ (44 * M * (p + 1)) * H ^ (10000 * (p + 1)) := by
  have hbox : 40 * P + 2 ≤ H ^ (p + 22) := by
    have hconstant : 42 ≤ H ^ 2 := by nlinarith
    calc
      _ ≤ 42 * P := by omega
      _ ≤ H ^ 2 * H ^ (p + 20) := Nat.mul_le_mul hconstant hPcap
      _ = H ^ (2 + (p + 20)) := (pow_add H 2 (p + 20)).symm
      _ = _ := by congr 1; omega
  have hlist : (40 * P + 2) ^ (2 * M) ≤ H ^ (44 * M * (p + 1)) := by
    calc
      _ ≤ (H ^ (p + 22)) ^ (2 * M) := Nat.pow_le_pow_left hbox _
      _ = H ^ ((p + 22) * (2 * M)) := (pow_mul H _ _).symm
      _ ≤ _ := Nat.pow_le_pow_right (by omega) (by nlinarith)
  have hlist1 : (40 * P + 2) ^ (2 * M) + 1 ≤ 2 * H ^ (44 * M * (p + 1)) := by
    have hunit : 1 ≤ H ^ (44 * M * (p + 1)) := Nat.one_le_pow _ _ (by omega)
    omega
  have hdimension : M * (40 * P + 2) ^ 2 + 1 ≤ H ^ (2 * p + 46) := by
    have h := optimizer_parameter_budget_le H M P p hH hM hP hPcap
    omega
  have hG := optimizer_parameter_budget_le H M P p hH hM hP hPcap
  have hproduct : (M * (40 * P + 2) ^ 2 + 1) *
      (H + M * (40 * P + 2) ^ 2 + 4) ^ 210 ≤ H ^ (10000 * (p + 1)) := by
    calc
      _ ≤ H ^ (2 * p + 46) * (H ^ (2 * p + 46)) ^ 210 :=
        Nat.mul_le_mul hdimension (Nat.pow_le_pow_left hG _)
      _ = (H ^ (2 * p + 46)) ^ 211 := (pow_succ' _ 210).symm
      _ = H ^ ((2 * p + 46) * 211) := (pow_mul H _ _).symm
      _ ≤ _ := Nat.pow_le_pow_right (by omega) (by omega)
  calc
    localOptimizerArithmeticBudget M P H =
        ((40 * P + 2) ^ (2 * M) + 1) *
          ((M * (40 * P + 2) ^ 2 + 1) * (H + M * (40 * P + 2) ^ 2 + 4) ^ 210) := by
      unfold localOptimizerArithmeticBudget
      exact Nat.mul_assoc _ _ _
    _ ≤ _ := Nat.mul_le_mul hlist1 hproduct

end EditApproximation

end OAI
