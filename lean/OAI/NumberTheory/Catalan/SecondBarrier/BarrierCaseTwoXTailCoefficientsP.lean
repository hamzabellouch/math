import Mathlib.Data.List.GetD
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.IntervalCases
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoXExplicitGroup7

namespace OAI

noncomputable section

namespace InternalCatalan
open Polynomial

def barrierCase2PTailNumeratorCoefficient (k : ℕ) : ℚ :=
  ([-334625418567286147906955121183793659/4882812500000000000000000000000000000000,
    20127644970984429229663641286102109817/12207031250000000000000000000000000000000,
    -2852876572408096311386663148074363127/610351562500000000000000000000000000000,
    219782662978769686811412440485306881/3051757812500000000000000000000000000,
    -4894248692719660966896600643752953/19073486328125000000000000000000000,
    45491985122617474473894836809089153/15258789062500000000000000000000000,
    -568781315379457100097709309340883/30517578125000000000000000000000,
    803074381853681639161748844303/7629394531250000000000000000,
    -5453962494228714418500320647/30517578125000000000000000,
    680879861223820138383153/7629394531250000000000] : List ℚ).getD k 0

private theorem barrierCase2PTailNumeratorExplicit_coeff_0 :
    barrierCase2PTailNumeratorExplicit.coeff 0 = barrierCase2PTailNumeratorCoefficient 0 := by
  simp only [barrierCase2PTailNumeratorExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero]
  simp only [barrierCase2PTailNumeratorCoefficient, List.getD_cons_zero]

private theorem barrierCase2PTailNumeratorExplicit_coeff_1 :
    barrierCase2PTailNumeratorExplicit.coeff 1 = barrierCase2PTailNumeratorCoefficient 1 := by
  simp only [barrierCase2PTailNumeratorExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2PTailNumeratorCoefficient, List.getD_cons_zero, List.getD_cons_succ]

private theorem barrierCase2PTailNumeratorExplicit_coeff_2 :
    barrierCase2PTailNumeratorExplicit.coeff 2 = barrierCase2PTailNumeratorCoefficient 2 := by
  simp only [barrierCase2PTailNumeratorExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2PTailNumeratorCoefficient, List.getD_cons_zero, List.getD_cons_succ]

private theorem barrierCase2PTailNumeratorExplicit_coeff_3 :
    barrierCase2PTailNumeratorExplicit.coeff 3 = barrierCase2PTailNumeratorCoefficient 3 := by
  simp only [barrierCase2PTailNumeratorExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2PTailNumeratorCoefficient, List.getD_cons_zero, List.getD_cons_succ]

private theorem barrierCase2PTailNumeratorExplicit_coeff_4 :
    barrierCase2PTailNumeratorExplicit.coeff 4 = barrierCase2PTailNumeratorCoefficient 4 := by
  simp only [barrierCase2PTailNumeratorExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2PTailNumeratorCoefficient, List.getD_cons_zero, List.getD_cons_succ]

private theorem barrierCase2PTailNumeratorExplicit_coeff_5 :
    barrierCase2PTailNumeratorExplicit.coeff 5 = barrierCase2PTailNumeratorCoefficient 5 := by
  simp only [barrierCase2PTailNumeratorExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2PTailNumeratorCoefficient, List.getD_cons_zero, List.getD_cons_succ]

private theorem barrierCase2PTailNumeratorExplicit_coeff_6 :
    barrierCase2PTailNumeratorExplicit.coeff 6 = barrierCase2PTailNumeratorCoefficient 6 := by
  simp only [barrierCase2PTailNumeratorExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2PTailNumeratorCoefficient, List.getD_cons_zero, List.getD_cons_succ]

private theorem barrierCase2PTailNumeratorExplicit_coeff_7 :
    barrierCase2PTailNumeratorExplicit.coeff 7 = barrierCase2PTailNumeratorCoefficient 7 := by
  simp only [barrierCase2PTailNumeratorExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2PTailNumeratorCoefficient, List.getD_cons_zero, List.getD_cons_succ]

private theorem barrierCase2PTailNumeratorExplicit_coeff_8 :
    barrierCase2PTailNumeratorExplicit.coeff 8 = barrierCase2PTailNumeratorCoefficient 8 := by
  simp only [barrierCase2PTailNumeratorExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2PTailNumeratorCoefficient, List.getD_cons_zero, List.getD_cons_succ]

private theorem barrierCase2PTailNumeratorExplicit_coeff_9 :
    barrierCase2PTailNumeratorExplicit.coeff 9 = barrierCase2PTailNumeratorCoefficient 9 := by
  simp only [barrierCase2PTailNumeratorExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2PTailNumeratorCoefficient, List.getD_cons_zero, List.getD_cons_succ]

theorem barrierCase2PTailNumeratorExplicit_natDegree :
    barrierCase2PTailNumeratorExplicit.natDegree = 9 := by
  unfold barrierCase2PTailNumeratorExplicit
  compute_degree!

theorem barrierCase2PTailNumeratorExplicit_coeff (k : ℕ) :
    barrierCase2PTailNumeratorExplicit.coeff k = barrierCase2PTailNumeratorCoefficient k := by
  by_cases hk : k < 10
  · interval_cases k
    · exact barrierCase2PTailNumeratorExplicit_coeff_0
    · exact barrierCase2PTailNumeratorExplicit_coeff_1
    · exact barrierCase2PTailNumeratorExplicit_coeff_2
    · exact barrierCase2PTailNumeratorExplicit_coeff_3
    · exact barrierCase2PTailNumeratorExplicit_coeff_4
    · exact barrierCase2PTailNumeratorExplicit_coeff_5
    · exact barrierCase2PTailNumeratorExplicit_coeff_6
    · exact barrierCase2PTailNumeratorExplicit_coeff_7
    · exact barrierCase2PTailNumeratorExplicit_coeff_8
    · exact barrierCase2PTailNumeratorExplicit_coeff_9
  · have hlookup : barrierCase2PTailNumeratorCoefficient k = 0 := by
      unfold barrierCase2PTailNumeratorCoefficient
      apply List.getD_eq_default
      simpa only [List.length_cons, List.length_nil] using (Nat.le_of_not_gt hk)
    rw [hlookup]
    apply coeff_eq_zero_of_natDegree_lt
    rw [barrierCase2PTailNumeratorExplicit_natDegree]
    omega

def barrierCase2PTailProductCoefficient (k : ℕ) : ℚ :=
  ([4785447983749937204061879244701/24414062500000000000000000000000000,
    -474962018866734369442083826221/1220703125000000000000000000000000,
    7705227818365150047259368501/2441406250000000000000000000000,
    -3589839094005450574517959947/610351562500000000000000000000,
    84481480701896139333127067089/152587890625000000000000000000,
    -8340696096348800303572388719/7629394531250000000000000000,
    2527238180877059028537517647/76293945312500000000000000,
    -1973789704813765919735753/30517578125000000000000,
    37686962338137420137757/152587890625000000000,
    -13017638552052412621/30517578125000000,
    32299425202362199/152587890625000] : List ℚ).getD k 0

private theorem barrierCase2PTailProductExplicit_coeff_0 :
    barrierCase2PTailProductExplicit.coeff 0 = barrierCase2PTailProductCoefficient 0 := by
  simp only [barrierCase2PTailProductExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero]
  simp only [barrierCase2PTailProductCoefficient, List.getD_cons_zero]

private theorem barrierCase2PTailProductExplicit_coeff_1 :
    barrierCase2PTailProductExplicit.coeff 1 = barrierCase2PTailProductCoefficient 1 := by
  simp only [barrierCase2PTailProductExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2PTailProductCoefficient, List.getD_cons_zero, List.getD_cons_succ]

private theorem barrierCase2PTailProductExplicit_coeff_2 :
    barrierCase2PTailProductExplicit.coeff 2 = barrierCase2PTailProductCoefficient 2 := by
  simp only [barrierCase2PTailProductExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2PTailProductCoefficient, List.getD_cons_zero, List.getD_cons_succ]

private theorem barrierCase2PTailProductExplicit_coeff_3 :
    barrierCase2PTailProductExplicit.coeff 3 = barrierCase2PTailProductCoefficient 3 := by
  simp only [barrierCase2PTailProductExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2PTailProductCoefficient, List.getD_cons_zero, List.getD_cons_succ]

private theorem barrierCase2PTailProductExplicit_coeff_4 :
    barrierCase2PTailProductExplicit.coeff 4 = barrierCase2PTailProductCoefficient 4 := by
  simp only [barrierCase2PTailProductExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2PTailProductCoefficient, List.getD_cons_zero, List.getD_cons_succ]

private theorem barrierCase2PTailProductExplicit_coeff_5 :
    barrierCase2PTailProductExplicit.coeff 5 = barrierCase2PTailProductCoefficient 5 := by
  simp only [barrierCase2PTailProductExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2PTailProductCoefficient, List.getD_cons_zero, List.getD_cons_succ]

private theorem barrierCase2PTailProductExplicit_coeff_6 :
    barrierCase2PTailProductExplicit.coeff 6 = barrierCase2PTailProductCoefficient 6 := by
  simp only [barrierCase2PTailProductExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2PTailProductCoefficient, List.getD_cons_zero, List.getD_cons_succ]

private theorem barrierCase2PTailProductExplicit_coeff_7 :
    barrierCase2PTailProductExplicit.coeff 7 = barrierCase2PTailProductCoefficient 7 := by
  simp only [barrierCase2PTailProductExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2PTailProductCoefficient, List.getD_cons_zero, List.getD_cons_succ]

private theorem barrierCase2PTailProductExplicit_coeff_8 :
    barrierCase2PTailProductExplicit.coeff 8 = barrierCase2PTailProductCoefficient 8 := by
  simp only [barrierCase2PTailProductExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2PTailProductCoefficient, List.getD_cons_zero, List.getD_cons_succ]

private theorem barrierCase2PTailProductExplicit_coeff_9 :
    barrierCase2PTailProductExplicit.coeff 9 = barrierCase2PTailProductCoefficient 9 := by
  simp only [barrierCase2PTailProductExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2PTailProductCoefficient, List.getD_cons_zero, List.getD_cons_succ]

private theorem barrierCase2PTailProductExplicit_coeff_10 :
    barrierCase2PTailProductExplicit.coeff 10 = barrierCase2PTailProductCoefficient 10 := by
  simp only [barrierCase2PTailProductExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2PTailProductCoefficient, List.getD_cons_zero, List.getD_cons_succ]

theorem barrierCase2PTailProductExplicit_natDegree :
    barrierCase2PTailProductExplicit.natDegree = 10 := by
  unfold barrierCase2PTailProductExplicit
  compute_degree!

theorem barrierCase2PTailProductExplicit_coeff (k : ℕ) :
    barrierCase2PTailProductExplicit.coeff k = barrierCase2PTailProductCoefficient k := by
  by_cases hk : k < 11
  · interval_cases k
    · exact barrierCase2PTailProductExplicit_coeff_0
    · exact barrierCase2PTailProductExplicit_coeff_1
    · exact barrierCase2PTailProductExplicit_coeff_2
    · exact barrierCase2PTailProductExplicit_coeff_3
    · exact barrierCase2PTailProductExplicit_coeff_4
    · exact barrierCase2PTailProductExplicit_coeff_5
    · exact barrierCase2PTailProductExplicit_coeff_6
    · exact barrierCase2PTailProductExplicit_coeff_7
    · exact barrierCase2PTailProductExplicit_coeff_8
    · exact barrierCase2PTailProductExplicit_coeff_9
    · exact barrierCase2PTailProductExplicit_coeff_10
  · have hlookup : barrierCase2PTailProductCoefficient k = 0 := by
      unfold barrierCase2PTailProductCoefficient
      apply List.getD_eq_default
      simpa only [List.length_cons, List.length_nil] using (Nat.le_of_not_gt hk)
    rw [hlookup]
    apply coeff_eq_zero_of_natDegree_lt
    rw [barrierCase2PTailProductExplicit_natDegree]
    omega

end InternalCatalan

end

end OAI
