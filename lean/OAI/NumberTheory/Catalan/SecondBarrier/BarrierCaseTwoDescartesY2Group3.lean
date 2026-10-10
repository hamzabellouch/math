import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoDescartesY0Group0

namespace OAI

namespace InternalCatalan

open Polynomial

def barrierCase2AYTransform2Coefficient (h : ℕ) : ℚ :=
  ([-29468567785849371012404257102782431370391111831 / 149011611938476562500000000000000000000000000000000,
    -2977434812495446114353696845638464637307603111527 / 596046447753906250000000000000000000000000000000000,
    -201457815596549216134410784714304450284195247990963 / 3576278686523437500000000000000000000000000000000000,
    -2633510307610809888534437678027934316546694819748733 / 7152557373046875000000000000000000000000000000000000,
    -21072027952584250316974210184493818299292218725433469 / 14305114746093750000000000000000000000000000000000000,
    -14730087874452741619503223044591826241000848978864807 / 4768371582031250000000000000000000000000000000000000,
    1242273293766808109592345866642046367789497834996327 / 596046447753906250000000000000000000000000000000000,
    1622021631381797822212329831968617169963601197771330479 / 38146972656250000000000000000000000000000000000000000,
    13661846168777521797301608174679836037120536570862578189 / 76293945312500000000000000000000000000000000000000000,
    73490645449005696123846325049423163426369696440394564947 / 152587890625000000000000000000000000000000000000000000,
    58152956781182625907456187025931197733855929862941855943 / 61035156250000000000000000000000000000000000000000000,
    41578447392389767044595405690791048242379904737600598033 / 28610229492187500000000000000000000000000000000000000,
    1592940760729225414840314323668190545170664189697713316777 / 915527343750000000000000000000000000000000000000000000,
    6001410973679336559069436793807181638938509189532577759417 / 3662109375000000000000000000000000000000000000000000000,
    2929896215941923617488651331571818408514241932966749238361 / 2441406250000000000000000000000000000000000000000000000,
    1612855803009347594625832102512813729373738622167808378891 / 2441406250000000000000000000000000000000000000000000000,
    304639085906673529980262914720767634069566273788274662699 / 1220703125000000000000000000000000000000000000000000000,
    13160155455391400545735885499903827112656312823070513823 / 305175781250000000000000000000000000000000000000000000,
    -39754224304628931854829845652755777923909753006029865859 / 2441406250000000000000000000000000000000000000000000000,
    -38786440062552273499794450526869737457149272370144558573 / 2441406250000000000000000000000000000000000000000000000,
    -5909563786909702763872399679689333829063402807129830169 / 915527343750000000000000000000000000000000000000000000,
    -1476482497134772048707163571996691407418282748781618819 / 915527343750000000000000000000000000000000000000000000,
    -465752604043612189183612003586479532135529925444062943 / 1831054687500000000000000000000000000000000000000000000,
    -568330377708050253339574534094868438462948592398721 / 24414062500000000000000000000000000000000000000000000,
    -143422457019384964080540540006456757972146949286541 / 152587890625000000000000000000000000000000000000000000] : List ℚ).getD h 0

noncomputable def barrierCase2AYTransform2Explicit : ℝ[X] :=
  C (-29468567785849371012404257102782431370391111831 / 149011611938476562500000000000000000000000000000000) +
    C (-2977434812495446114353696845638464637307603111527 / 596046447753906250000000000000000000000000000000000) * X ^ 1 +
    C (-201457815596549216134410784714304450284195247990963 / 3576278686523437500000000000000000000000000000000000) * X ^ 2 +
    C (-2633510307610809888534437678027934316546694819748733 / 7152557373046875000000000000000000000000000000000000) * X ^ 3 +
    C (-21072027952584250316974210184493818299292218725433469 / 14305114746093750000000000000000000000000000000000000) * X ^ 4 +
    C (-14730087874452741619503223044591826241000848978864807 / 4768371582031250000000000000000000000000000000000000) * X ^ 5 +
    C (1242273293766808109592345866642046367789497834996327 / 596046447753906250000000000000000000000000000000000) * X ^ 6 +
    C (1622021631381797822212329831968617169963601197771330479 / 38146972656250000000000000000000000000000000000000000) * X ^ 7 +
    C (13661846168777521797301608174679836037120536570862578189 / 76293945312500000000000000000000000000000000000000000) * X ^ 8 +
    C (73490645449005696123846325049423163426369696440394564947 / 152587890625000000000000000000000000000000000000000000) * X ^ 9 +
    C (58152956781182625907456187025931197733855929862941855943 / 61035156250000000000000000000000000000000000000000000) * X ^ 10 +
    C (41578447392389767044595405690791048242379904737600598033 / 28610229492187500000000000000000000000000000000000000) * X ^ 11 +
    C (1592940760729225414840314323668190545170664189697713316777 / 915527343750000000000000000000000000000000000000000000) * X ^ 12 +
    C (6001410973679336559069436793807181638938509189532577759417 / 3662109375000000000000000000000000000000000000000000000) * X ^ 13 +
    C (2929896215941923617488651331571818408514241932966749238361 / 2441406250000000000000000000000000000000000000000000000) * X ^ 14 +
    C (1612855803009347594625832102512813729373738622167808378891 / 2441406250000000000000000000000000000000000000000000000) * X ^ 15 +
    C (304639085906673529980262914720767634069566273788274662699 / 1220703125000000000000000000000000000000000000000000000) * X ^ 16 +
    C (13160155455391400545735885499903827112656312823070513823 / 305175781250000000000000000000000000000000000000000000) * X ^ 17 +
    C (-39754224304628931854829845652755777923909753006029865859 / 2441406250000000000000000000000000000000000000000000000) * X ^ 18 +
    C (-38786440062552273499794450526869737457149272370144558573 / 2441406250000000000000000000000000000000000000000000000) * X ^ 19 +
    C (-5909563786909702763872399679689333829063402807129830169 / 915527343750000000000000000000000000000000000000000000) * X ^ 20 +
    C (-1476482497134772048707163571996691407418282748781618819 / 915527343750000000000000000000000000000000000000000000) * X ^ 21 +
    C (-465752604043612189183612003586479532135529925444062943 / 1831054687500000000000000000000000000000000000000000000) * X ^ 22 +
    C (-568330377708050253339574534094868438462948592398721 / 24414062500000000000000000000000000000000000000000000) * X ^ 23 +
    C (-143422457019384964080540540006456757972146949286541 / 152587890625000000000000000000000000000000000000000000) * X ^ 24

theorem barrierCase2AYTransform2Explicit_natDegree :
    barrierCase2AYTransform2Explicit.natDegree = 24 := by
  unfold barrierCase2AYTransform2Explicit
  compute_degree!

theorem barrier_case2_AY_transform2_coeff_rat_0 :
    barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (1 / 2) (3 / 4) 0 =
      barrierCase2AYTransform2Coefficient 0 := by decide +kernel

theorem barrier_case2_AY_transform2_coeff_rat_1 :
    barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (1 / 2) (3 / 4) 1 =
      barrierCase2AYTransform2Coefficient 1 := by decide +kernel

theorem barrier_case2_AY_transform2_coeff_rat_2 :
    barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (1 / 2) (3 / 4) 2 =
      barrierCase2AYTransform2Coefficient 2 := by decide +kernel

theorem barrier_case2_AY_transform2_coeff_rat_3 :
    barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (1 / 2) (3 / 4) 3 =
      barrierCase2AYTransform2Coefficient 3 := by decide +kernel

theorem barrier_case2_AY_transform2_coeff_rat_4 :
    barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (1 / 2) (3 / 4) 4 =
      barrierCase2AYTransform2Coefficient 4 := by decide +kernel

theorem barrier_case2_AY_transform2_explicit_coeff_0 :
    barrierCase2AYTransform2Explicit.coeff 0 =
      (barrierCase2AYTransform2Coefficient 0 : ℝ) := by
  simp only [barrierCase2AYTransform2Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero]
  simp only [barrierCase2AYTransform2Coefficient, List.getD_cons_zero]
  norm_num

theorem barrier_case2_AY_transform2_explicit_coeff_1 :
    barrierCase2AYTransform2Explicit.coeff 1 =
      (barrierCase2AYTransform2Coefficient 1 : ℝ) := by
  simp only [barrierCase2AYTransform2Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYTransform2Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrier_case2_AY_transform2_explicit_coeff_2 :
    barrierCase2AYTransform2Explicit.coeff 2 =
      (barrierCase2AYTransform2Coefficient 2 : ℝ) := by
  simp only [barrierCase2AYTransform2Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYTransform2Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrier_case2_AY_transform2_explicit_coeff_3 :
    barrierCase2AYTransform2Explicit.coeff 3 =
      (barrierCase2AYTransform2Coefficient 3 : ℝ) := by
  simp only [barrierCase2AYTransform2Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYTransform2Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrier_case2_AY_transform2_explicit_coeff_4 :
    barrierCase2AYTransform2Explicit.coeff 4 =
      (barrierCase2AYTransform2Coefficient 4 : ℝ) := by
  simp only [barrierCase2AYTransform2Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYTransform2Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrier_case2_AY_transform2_coeff_rat_5 :
    barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (1 / 2) (3 / 4) 5 =
      barrierCase2AYTransform2Coefficient 5 := by decide +kernel

theorem barrier_case2_AY_transform2_coeff_rat_6 :
    barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (1 / 2) (3 / 4) 6 =
      barrierCase2AYTransform2Coefficient 6 := by decide +kernel

theorem barrier_case2_AY_transform2_coeff_rat_7 :
    barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (1 / 2) (3 / 4) 7 =
      barrierCase2AYTransform2Coefficient 7 := by decide +kernel

theorem barrier_case2_AY_transform2_coeff_rat_8 :
    barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (1 / 2) (3 / 4) 8 =
      barrierCase2AYTransform2Coefficient 8 := by decide +kernel

theorem barrier_case2_AY_transform2_coeff_rat_9 :
    barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (1 / 2) (3 / 4) 9 =
      barrierCase2AYTransform2Coefficient 9 := by decide +kernel

theorem barrier_case2_AY_transform2_explicit_coeff_5 :
    barrierCase2AYTransform2Explicit.coeff 5 =
      (barrierCase2AYTransform2Coefficient 5 : ℝ) := by
  simp only [barrierCase2AYTransform2Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYTransform2Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrier_case2_AY_transform2_explicit_coeff_6 :
    barrierCase2AYTransform2Explicit.coeff 6 =
      (barrierCase2AYTransform2Coefficient 6 : ℝ) := by
  simp only [barrierCase2AYTransform2Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYTransform2Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrier_case2_AY_transform2_explicit_coeff_7 :
    barrierCase2AYTransform2Explicit.coeff 7 =
      (barrierCase2AYTransform2Coefficient 7 : ℝ) := by
  simp only [barrierCase2AYTransform2Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYTransform2Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrier_case2_AY_transform2_explicit_coeff_8 :
    barrierCase2AYTransform2Explicit.coeff 8 =
      (barrierCase2AYTransform2Coefficient 8 : ℝ) := by
  simp only [barrierCase2AYTransform2Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYTransform2Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrier_case2_AY_transform2_explicit_coeff_9 :
    barrierCase2AYTransform2Explicit.coeff 9 =
      (barrierCase2AYTransform2Coefficient 9 : ℝ) := by
  simp only [barrierCase2AYTransform2Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYTransform2Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrier_case2_AY_transform2_coeff_rat_10 :
    barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (1 / 2) (3 / 4) 10 =
      barrierCase2AYTransform2Coefficient 10 := by decide +kernel

theorem barrier_case2_AY_transform2_coeff_rat_11 :
    barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (1 / 2) (3 / 4) 11 =
      barrierCase2AYTransform2Coefficient 11 := by decide +kernel

theorem barrier_case2_AY_transform2_coeff_rat_12 :
    barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (1 / 2) (3 / 4) 12 =
      barrierCase2AYTransform2Coefficient 12 := by decide +kernel

theorem barrier_case2_AY_transform2_coeff_rat_13 :
    barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (1 / 2) (3 / 4) 13 =
      barrierCase2AYTransform2Coefficient 13 := by decide +kernel

theorem barrier_case2_AY_transform2_coeff_rat_14 :
    barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (1 / 2) (3 / 4) 14 =
      barrierCase2AYTransform2Coefficient 14 := by decide +kernel

theorem barrier_case2_AY_transform2_explicit_coeff_10 :
    barrierCase2AYTransform2Explicit.coeff 10 =
      (barrierCase2AYTransform2Coefficient 10 : ℝ) := by
  simp only [barrierCase2AYTransform2Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYTransform2Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrier_case2_AY_transform2_explicit_coeff_11 :
    barrierCase2AYTransform2Explicit.coeff 11 =
      (barrierCase2AYTransform2Coefficient 11 : ℝ) := by
  simp only [barrierCase2AYTransform2Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYTransform2Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrier_case2_AY_transform2_explicit_coeff_12 :
    barrierCase2AYTransform2Explicit.coeff 12 =
      (barrierCase2AYTransform2Coefficient 12 : ℝ) := by
  simp only [barrierCase2AYTransform2Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYTransform2Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrier_case2_AY_transform2_explicit_coeff_13 :
    barrierCase2AYTransform2Explicit.coeff 13 =
      (barrierCase2AYTransform2Coefficient 13 : ℝ) := by
  simp only [barrierCase2AYTransform2Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYTransform2Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrier_case2_AY_transform2_explicit_coeff_14 :
    barrierCase2AYTransform2Explicit.coeff 14 =
      (barrierCase2AYTransform2Coefficient 14 : ℝ) := by
  simp only [barrierCase2AYTransform2Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYTransform2Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrier_case2_AY_transform2_coeff_rat_15 :
    barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (1 / 2) (3 / 4) 15 =
      barrierCase2AYTransform2Coefficient 15 := by decide +kernel

theorem barrier_case2_AY_transform2_coeff_rat_16 :
    barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (1 / 2) (3 / 4) 16 =
      barrierCase2AYTransform2Coefficient 16 := by decide +kernel

theorem barrier_case2_AY_transform2_coeff_rat_17 :
    barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (1 / 2) (3 / 4) 17 =
      barrierCase2AYTransform2Coefficient 17 := by decide +kernel

theorem barrier_case2_AY_transform2_coeff_rat_18 :
    barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (1 / 2) (3 / 4) 18 =
      barrierCase2AYTransform2Coefficient 18 := by decide +kernel

theorem barrier_case2_AY_transform2_coeff_rat_19 :
    barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (1 / 2) (3 / 4) 19 =
      barrierCase2AYTransform2Coefficient 19 := by decide +kernel

theorem barrier_case2_AY_transform2_explicit_coeff_15 :
    barrierCase2AYTransform2Explicit.coeff 15 =
      (barrierCase2AYTransform2Coefficient 15 : ℝ) := by
  simp only [barrierCase2AYTransform2Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYTransform2Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrier_case2_AY_transform2_explicit_coeff_16 :
    barrierCase2AYTransform2Explicit.coeff 16 =
      (barrierCase2AYTransform2Coefficient 16 : ℝ) := by
  simp only [barrierCase2AYTransform2Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYTransform2Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrier_case2_AY_transform2_explicit_coeff_17 :
    barrierCase2AYTransform2Explicit.coeff 17 =
      (barrierCase2AYTransform2Coefficient 17 : ℝ) := by
  simp only [barrierCase2AYTransform2Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYTransform2Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrier_case2_AY_transform2_explicit_coeff_18 :
    barrierCase2AYTransform2Explicit.coeff 18 =
      (barrierCase2AYTransform2Coefficient 18 : ℝ) := by
  simp only [barrierCase2AYTransform2Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYTransform2Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrier_case2_AY_transform2_explicit_coeff_19 :
    barrierCase2AYTransform2Explicit.coeff 19 =
      (barrierCase2AYTransform2Coefficient 19 : ℝ) := by
  simp only [barrierCase2AYTransform2Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYTransform2Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

end InternalCatalan

end OAI
