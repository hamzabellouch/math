import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoDescartesY0Group0

namespace OAI

namespace InternalCatalan

open Polynomial

def barrierCase2AYTransform3Coefficient (h : ℕ) : ℚ :=
  ([-143422457019384964080540540006456757972146949286541 / 152587890625000000000000000000000000000000000000000000,
    -13328852305020656769974420328867986569078499453047847 / 610351562500000000000000000000000000000000000000000000,
    -405073511543650819301080934964722549053360065816570661 / 1831054687500000000000000000000000000000000000000000000,
    -1135715502151477029448121480712888010404496946542335209 / 915527343750000000000000000000000000000000000000000000,
    -3425747014757532840387408046604750189100980151421780073 / 915527343750000000000000000000000000000000000000000000,
    -32564922254395114794043131666483789414566624556349199 / 19531250000000000000000000000000000000000000000000000,
    96507491766964192008323381540874751067786163701854775211 / 2441406250000000000000000000000000000000000000000000000,
    2552136099683715674198722117827879481369002003219286563 / 12207031250000000000000000000000000000000000000000000,
    757295683155663124924691968667443065370025938184710453169 / 1220703125000000000000000000000000000000000000000000000,
    3081347631187943503290080929183422725649931198655770031221 / 2441406250000000000000000000000000000000000000000000000,
    894974956378438662157180107167251898953560334080624379907 / 488281250000000000000000000000000000000000000000000000,
    6762715922934768192302940241411982273797805158671382025807 / 3662109375000000000000000000000000000000000000000000000,
    49897915571152220668070685145880004745954607525119213777 / 45776367187500000000000000000000000000000000000000000,
    -8478892304126901706129993081424673920933645530641695947 / 228881835937500000000000000000000000000000000000000000,
    -250883345684911847930727702269439739886830864462697542683 / 305175781250000000000000000000000000000000000000000000,
    -139548911805189759334085179198262041423478654187395622079 / 152587890625000000000000000000000000000000000000000000,
    -42842999955418773787975250759537820647632678736432955307 / 76293945312500000000000000000000000000000000000000000,
    -7677384199066108545301224087264333207407796782438804823 / 38146972656250000000000000000000000000000000000000000,
    -576371618304089744975361850231714547694133029671007137 / 19073486328125000000000000000000000000000000000000000,
    53105118518658103982573517692925793524071100845888027 / 9536743164062500000000000000000000000000000000000000,
    10310494448084278033147754923819461246573435357971077 / 3576278686523437500000000000000000000000000000000000,
    778043333408210218430483767526511181284896861087257 / 3576278686523437500000000000000000000000000000000000,
    -16157727069445508923697447903700348673024154406613 / 447034835815429687500000000000000000000000000000000,
    35186487237831991152495949797694230294009192933 / 74505805969238281250000000000000000000000000000000,
    -427438929851263500756115967545179267 / 372529029846191406250000000000000000000000] : List ℚ).getD h 0

noncomputable def barrierCase2AYTransform3Explicit : ℝ[X] :=
  C (-143422457019384964080540540006456757972146949286541 / 152587890625000000000000000000000000000000000000000000) +
    C (-13328852305020656769974420328867986569078499453047847 / 610351562500000000000000000000000000000000000000000000) * X ^ 1 +
    C (-405073511543650819301080934964722549053360065816570661 / 1831054687500000000000000000000000000000000000000000000) * X ^ 2 +
    C (-1135715502151477029448121480712888010404496946542335209 / 915527343750000000000000000000000000000000000000000000) * X ^ 3 +
    C (-3425747014757532840387408046604750189100980151421780073 / 915527343750000000000000000000000000000000000000000000) * X ^ 4 +
    C (-32564922254395114794043131666483789414566624556349199 / 19531250000000000000000000000000000000000000000000000) * X ^ 5 +
    C (96507491766964192008323381540874751067786163701854775211 / 2441406250000000000000000000000000000000000000000000000) * X ^ 6 +
    C (2552136099683715674198722117827879481369002003219286563 / 12207031250000000000000000000000000000000000000000000) * X ^ 7 +
    C (757295683155663124924691968667443065370025938184710453169 / 1220703125000000000000000000000000000000000000000000000) * X ^ 8 +
    C (3081347631187943503290080929183422725649931198655770031221 / 2441406250000000000000000000000000000000000000000000000) * X ^ 9 +
    C (894974956378438662157180107167251898953560334080624379907 / 488281250000000000000000000000000000000000000000000000) * X ^ 10 +
    C (6762715922934768192302940241411982273797805158671382025807 / 3662109375000000000000000000000000000000000000000000000) * X ^ 11 +
    C (49897915571152220668070685145880004745954607525119213777 / 45776367187500000000000000000000000000000000000000000) * X ^ 12 +
    C (-8478892304126901706129993081424673920933645530641695947 / 228881835937500000000000000000000000000000000000000000) * X ^ 13 +
    C (-250883345684911847930727702269439739886830864462697542683 / 305175781250000000000000000000000000000000000000000000) * X ^ 14 +
    C (-139548911805189759334085179198262041423478654187395622079 / 152587890625000000000000000000000000000000000000000000) * X ^ 15 +
    C (-42842999955418773787975250759537820647632678736432955307 / 76293945312500000000000000000000000000000000000000000) * X ^ 16 +
    C (-7677384199066108545301224087264333207407796782438804823 / 38146972656250000000000000000000000000000000000000000) * X ^ 17 +
    C (-576371618304089744975361850231714547694133029671007137 / 19073486328125000000000000000000000000000000000000000) * X ^ 18 +
    C (53105118518658103982573517692925793524071100845888027 / 9536743164062500000000000000000000000000000000000000) * X ^ 19 +
    C (10310494448084278033147754923819461246573435357971077 / 3576278686523437500000000000000000000000000000000000) * X ^ 20 +
    C (778043333408210218430483767526511181284896861087257 / 3576278686523437500000000000000000000000000000000000) * X ^ 21 +
    C (-16157727069445508923697447903700348673024154406613 / 447034835815429687500000000000000000000000000000000) * X ^ 22 +
    C (35186487237831991152495949797694230294009192933 / 74505805969238281250000000000000000000000000000000) * X ^ 23 +
    C (-427438929851263500756115967545179267 / 372529029846191406250000000000000000000000) * X ^ 24

theorem barrierCase2AYTransform3Explicit_natDegree :
    barrierCase2AYTransform3Explicit.natDegree = 24 := by
  unfold barrierCase2AYTransform3Explicit
  compute_degree!

theorem barrier_case2_AY_transform3_coeff_rat_0 :
    barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (3 / 4) (1) 0 =
      barrierCase2AYTransform3Coefficient 0 := by decide +kernel

theorem barrier_case2_AY_transform3_coeff_rat_1 :
    barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (3 / 4) (1) 1 =
      barrierCase2AYTransform3Coefficient 1 := by decide +kernel

theorem barrier_case2_AY_transform3_coeff_rat_2 :
    barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (3 / 4) (1) 2 =
      barrierCase2AYTransform3Coefficient 2 := by decide +kernel

theorem barrier_case2_AY_transform3_coeff_rat_3 :
    barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (3 / 4) (1) 3 =
      barrierCase2AYTransform3Coefficient 3 := by decide +kernel

theorem barrier_case2_AY_transform3_coeff_rat_4 :
    barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (3 / 4) (1) 4 =
      barrierCase2AYTransform3Coefficient 4 := by decide +kernel

theorem barrier_case2_AY_transform3_explicit_coeff_0 :
    barrierCase2AYTransform3Explicit.coeff 0 =
      (barrierCase2AYTransform3Coefficient 0 : ℝ) := by
  simp only [barrierCase2AYTransform3Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero]
  simp only [barrierCase2AYTransform3Coefficient, List.getD_cons_zero]
  norm_num

theorem barrier_case2_AY_transform3_explicit_coeff_1 :
    barrierCase2AYTransform3Explicit.coeff 1 =
      (barrierCase2AYTransform3Coefficient 1 : ℝ) := by
  simp only [barrierCase2AYTransform3Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYTransform3Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrier_case2_AY_transform3_explicit_coeff_2 :
    barrierCase2AYTransform3Explicit.coeff 2 =
      (barrierCase2AYTransform3Coefficient 2 : ℝ) := by
  simp only [barrierCase2AYTransform3Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYTransform3Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrier_case2_AY_transform3_explicit_coeff_3 :
    barrierCase2AYTransform3Explicit.coeff 3 =
      (barrierCase2AYTransform3Coefficient 3 : ℝ) := by
  simp only [barrierCase2AYTransform3Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYTransform3Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrier_case2_AY_transform3_explicit_coeff_4 :
    barrierCase2AYTransform3Explicit.coeff 4 =
      (barrierCase2AYTransform3Coefficient 4 : ℝ) := by
  simp only [barrierCase2AYTransform3Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYTransform3Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrier_case2_AY_transform3_coeff_rat_5 :
    barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (3 / 4) (1) 5 =
      barrierCase2AYTransform3Coefficient 5 := by decide +kernel

theorem barrier_case2_AY_transform3_coeff_rat_6 :
    barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (3 / 4) (1) 6 =
      barrierCase2AYTransform3Coefficient 6 := by decide +kernel

theorem barrier_case2_AY_transform3_coeff_rat_7 :
    barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (3 / 4) (1) 7 =
      barrierCase2AYTransform3Coefficient 7 := by decide +kernel

theorem barrier_case2_AY_transform3_coeff_rat_8 :
    barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (3 / 4) (1) 8 =
      barrierCase2AYTransform3Coefficient 8 := by decide +kernel

theorem barrier_case2_AY_transform3_coeff_rat_9 :
    barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (3 / 4) (1) 9 =
      barrierCase2AYTransform3Coefficient 9 := by decide +kernel

theorem barrier_case2_AY_transform3_explicit_coeff_5 :
    barrierCase2AYTransform3Explicit.coeff 5 =
      (barrierCase2AYTransform3Coefficient 5 : ℝ) := by
  simp only [barrierCase2AYTransform3Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYTransform3Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrier_case2_AY_transform3_explicit_coeff_6 :
    barrierCase2AYTransform3Explicit.coeff 6 =
      (barrierCase2AYTransform3Coefficient 6 : ℝ) := by
  simp only [barrierCase2AYTransform3Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYTransform3Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrier_case2_AY_transform3_explicit_coeff_7 :
    barrierCase2AYTransform3Explicit.coeff 7 =
      (barrierCase2AYTransform3Coefficient 7 : ℝ) := by
  simp only [barrierCase2AYTransform3Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYTransform3Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrier_case2_AY_transform3_explicit_coeff_8 :
    barrierCase2AYTransform3Explicit.coeff 8 =
      (barrierCase2AYTransform3Coefficient 8 : ℝ) := by
  simp only [barrierCase2AYTransform3Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYTransform3Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrier_case2_AY_transform3_explicit_coeff_9 :
    barrierCase2AYTransform3Explicit.coeff 9 =
      (barrierCase2AYTransform3Coefficient 9 : ℝ) := by
  simp only [barrierCase2AYTransform3Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYTransform3Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrier_case2_AY_transform3_coeff_rat_10 :
    barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (3 / 4) (1) 10 =
      barrierCase2AYTransform3Coefficient 10 := by decide +kernel

theorem barrier_case2_AY_transform3_coeff_rat_11 :
    barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (3 / 4) (1) 11 =
      barrierCase2AYTransform3Coefficient 11 := by decide +kernel

theorem barrier_case2_AY_transform3_coeff_rat_12 :
    barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (3 / 4) (1) 12 =
      barrierCase2AYTransform3Coefficient 12 := by decide +kernel

theorem barrier_case2_AY_transform3_coeff_rat_13 :
    barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (3 / 4) (1) 13 =
      barrierCase2AYTransform3Coefficient 13 := by decide +kernel

theorem barrier_case2_AY_transform3_coeff_rat_14 :
    barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (3 / 4) (1) 14 =
      barrierCase2AYTransform3Coefficient 14 := by decide +kernel

theorem barrier_case2_AY_transform3_explicit_coeff_10 :
    barrierCase2AYTransform3Explicit.coeff 10 =
      (barrierCase2AYTransform3Coefficient 10 : ℝ) := by
  simp only [barrierCase2AYTransform3Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYTransform3Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrier_case2_AY_transform3_explicit_coeff_11 :
    barrierCase2AYTransform3Explicit.coeff 11 =
      (barrierCase2AYTransform3Coefficient 11 : ℝ) := by
  simp only [barrierCase2AYTransform3Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYTransform3Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrier_case2_AY_transform3_explicit_coeff_12 :
    barrierCase2AYTransform3Explicit.coeff 12 =
      (barrierCase2AYTransform3Coefficient 12 : ℝ) := by
  simp only [barrierCase2AYTransform3Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYTransform3Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrier_case2_AY_transform3_explicit_coeff_13 :
    barrierCase2AYTransform3Explicit.coeff 13 =
      (barrierCase2AYTransform3Coefficient 13 : ℝ) := by
  simp only [barrierCase2AYTransform3Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYTransform3Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrier_case2_AY_transform3_explicit_coeff_14 :
    barrierCase2AYTransform3Explicit.coeff 14 =
      (barrierCase2AYTransform3Coefficient 14 : ℝ) := by
  simp only [barrierCase2AYTransform3Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYTransform3Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrier_case2_AY_transform3_coeff_rat_15 :
    barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (3 / 4) (1) 15 =
      barrierCase2AYTransform3Coefficient 15 := by decide +kernel

theorem barrier_case2_AY_transform3_coeff_rat_16 :
    barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (3 / 4) (1) 16 =
      barrierCase2AYTransform3Coefficient 16 := by decide +kernel

theorem barrier_case2_AY_transform3_coeff_rat_17 :
    barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (3 / 4) (1) 17 =
      barrierCase2AYTransform3Coefficient 17 := by decide +kernel

theorem barrier_case2_AY_transform3_coeff_rat_18 :
    barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (3 / 4) (1) 18 =
      barrierCase2AYTransform3Coefficient 18 := by decide +kernel

theorem barrier_case2_AY_transform3_coeff_rat_19 :
    barrierDescartesCoeffRat barrierCase2AYCoefficient 24 (3 / 4) (1) 19 =
      barrierCase2AYTransform3Coefficient 19 := by decide +kernel

theorem barrier_case2_AY_transform3_explicit_coeff_15 :
    barrierCase2AYTransform3Explicit.coeff 15 =
      (barrierCase2AYTransform3Coefficient 15 : ℝ) := by
  simp only [barrierCase2AYTransform3Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYTransform3Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrier_case2_AY_transform3_explicit_coeff_16 :
    barrierCase2AYTransform3Explicit.coeff 16 =
      (barrierCase2AYTransform3Coefficient 16 : ℝ) := by
  simp only [barrierCase2AYTransform3Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYTransform3Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrier_case2_AY_transform3_explicit_coeff_17 :
    barrierCase2AYTransform3Explicit.coeff 17 =
      (barrierCase2AYTransform3Coefficient 17 : ℝ) := by
  simp only [barrierCase2AYTransform3Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYTransform3Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrier_case2_AY_transform3_explicit_coeff_18 :
    barrierCase2AYTransform3Explicit.coeff 18 =
      (barrierCase2AYTransform3Coefficient 18 : ℝ) := by
  simp only [barrierCase2AYTransform3Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYTransform3Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrier_case2_AY_transform3_explicit_coeff_19 :
    barrierCase2AYTransform3Explicit.coeff 19 =
      (barrierCase2AYTransform3Coefficient 19 : ℝ) := by
  simp only [barrierCase2AYTransform3Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AYTransform3Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

end InternalCatalan

end OAI
