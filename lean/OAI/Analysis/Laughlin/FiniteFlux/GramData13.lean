import OAI.Analysis.Laughlin.FiniteFlux.ComputeGram01Batch13
import OAI.Analysis.Laughlin.FiniteFlux.ComputeGram03Batch13
import OAI.Analysis.Laughlin.FiniteFlux.ComputeGram05Batch13
import OAI.Analysis.Laughlin.FiniteFlux.ComputeGram07Batch13
import OAI.Analysis.Laughlin.FiniteFlux.ComputeGram09Batch13
import OAI.Analysis.Laughlin.FiniteFlux.ComputeGram11Batch13
import OAI.Analysis.Laughlin.FiniteFlux.ComputeGram131313
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0101Batch13
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0103Batch13
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0105Batch13
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0107Batch13
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0109Batch13
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0111Batch13
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0113Batch13
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0303Batch13
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0305Batch13
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0307Batch13
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0309Batch13
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0311Batch13
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0313Batch13
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0505Batch13
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0507Batch13
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0509Batch13
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0511Batch13
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0513Batch13
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0707Batch13
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0709Batch13
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0711Batch13
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0713Batch13
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0909Batch13
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0911Batch13
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0913Batch13
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow1111Batch13
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow1113Batch13
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow1313Batch13
import OAI.Analysis.Laughlin.FiniteFlux.Data13
import OAI.Analysis.Laughlin.FourBody.NumericBridge
import OAI.Analysis.Laughlin.FourBody.Symmetry

namespace OAI

namespace Laughlin.Certificate
theorem source_error_13_1_1 : Y 13 1 1 = (121685493803305440547576917/8388608000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 13 1 1 0 (by decide),
    source_yRow_eq_rowCompute 13 1 1 1 (by decide),
    source_yRow_eq_rowCompute 13 1 1 2 (by decide),
    source_yRow_eq_rowCompute 13 1 1 3 (by decide),
    source_yRow_eq_rowCompute 13 1 1 4 (by decide),
    source_yRow_eq_rowCompute 13 1 1 5 (by decide),
    source_yRow_eq_rowCompute 13 1 1 6 (by decide),
    computeRow_13_1_1_0, computeRow_13_1_1_1, computeRow_13_1_1_2, computeRow_13_1_1_3, computeRow_13_1_1_4, computeRow_13_1_1_5, computeRow_13_1_1_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_13_1_3 : Y 13 1 3 = (7563908306608840424871171/8388608000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 13 1 3 0 (by decide),
    source_yRow_eq_rowCompute 13 1 3 1 (by decide),
    source_yRow_eq_rowCompute 13 1 3 2 (by decide),
    source_yRow_eq_rowCompute 13 1 3 3 (by decide),
    source_yRow_eq_rowCompute 13 1 3 4 (by decide),
    source_yRow_eq_rowCompute 13 1 3 5 (by decide),
    source_yRow_eq_rowCompute 13 1 3 6 (by decide),
    computeRow_13_1_3_0, computeRow_13_1_3_1, computeRow_13_1_3_2, computeRow_13_1_3_3, computeRow_13_1_3_4, computeRow_13_1_3_5, computeRow_13_1_3_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_13_1_5 : Y 13 1 5 = (-66091999624888726298111247/16777216000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 13 1 5 0 (by decide),
    source_yRow_eq_rowCompute 13 1 5 1 (by decide),
    source_yRow_eq_rowCompute 13 1 5 2 (by decide),
    source_yRow_eq_rowCompute 13 1 5 3 (by decide),
    source_yRow_eq_rowCompute 13 1 5 4 (by decide),
    source_yRow_eq_rowCompute 13 1 5 5 (by decide),
    source_yRow_eq_rowCompute 13 1 5 6 (by decide),
    computeRow_13_1_5_0, computeRow_13_1_5_1, computeRow_13_1_5_2, computeRow_13_1_5_3, computeRow_13_1_5_4, computeRow_13_1_5_5, computeRow_13_1_5_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_13_1_7 : Y 13 1 7 = (2728798823338271240310567/1677721600000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 13 1 7 0 (by decide),
    source_yRow_eq_rowCompute 13 1 7 1 (by decide),
    source_yRow_eq_rowCompute 13 1 7 2 (by decide),
    source_yRow_eq_rowCompute 13 1 7 3 (by decide),
    source_yRow_eq_rowCompute 13 1 7 4 (by decide),
    source_yRow_eq_rowCompute 13 1 7 5 (by decide),
    source_yRow_eq_rowCompute 13 1 7 6 (by decide),
    computeRow_13_1_7_0, computeRow_13_1_7_1, computeRow_13_1_7_2, computeRow_13_1_7_3, computeRow_13_1_7_4, computeRow_13_1_7_5, computeRow_13_1_7_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_13_1_9 : Y 13 1 9 = (-13501297339814524797227781/10485760000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 13 1 9 0 (by decide),
    source_yRow_eq_rowCompute 13 1 9 1 (by decide),
    source_yRow_eq_rowCompute 13 1 9 2 (by decide),
    source_yRow_eq_rowCompute 13 1 9 3 (by decide),
    source_yRow_eq_rowCompute 13 1 9 4 (by decide),
    source_yRow_eq_rowCompute 13 1 9 5 (by decide),
    source_yRow_eq_rowCompute 13 1 9 6 (by decide),
    computeRow_13_1_9_0, computeRow_13_1_9_1, computeRow_13_1_9_2, computeRow_13_1_9_3, computeRow_13_1_9_4, computeRow_13_1_9_5, computeRow_13_1_9_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_13_1_11 : Y 13 1 11 = (12432022452888993488134359/1048576000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 13 1 11 0 (by decide),
    source_yRow_eq_rowCompute 13 1 11 1 (by decide),
    source_yRow_eq_rowCompute 13 1 11 2 (by decide),
    source_yRow_eq_rowCompute 13 1 11 3 (by decide),
    source_yRow_eq_rowCompute 13 1 11 4 (by decide),
    source_yRow_eq_rowCompute 13 1 11 5 (by decide),
    source_yRow_eq_rowCompute 13 1 11 6 (by decide),
    computeRow_13_1_11_0, computeRow_13_1_11_1, computeRow_13_1_11_2, computeRow_13_1_11_3, computeRow_13_1_11_4, computeRow_13_1_11_5, computeRow_13_1_11_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_13_1_13 : Y 13 1 13 = (-165874530574631465579316753/1048576000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 13 1 13 0 (by decide),
    source_yRow_eq_rowCompute 13 1 13 1 (by decide),
    source_yRow_eq_rowCompute 13 1 13 2 (by decide),
    source_yRow_eq_rowCompute 13 1 13 3 (by decide),
    source_yRow_eq_rowCompute 13 1 13 4 (by decide),
    source_yRow_eq_rowCompute 13 1 13 5 (by decide),
    source_yRow_eq_rowCompute 13 1 13 6 (by decide),
    computeRow_13_1_13_0, computeRow_13_1_13_1, computeRow_13_1_13_2, computeRow_13_1_13_3, computeRow_13_1_13_4, computeRow_13_1_13_5, computeRow_13_1_13_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_13_3_3 : Y 13 3 3 = (-2041302613950531427151763/8388608000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 13 3 3 0 (by decide),
    source_yRow_eq_rowCompute 13 3 3 1 (by decide),
    source_yRow_eq_rowCompute 13 3 3 2 (by decide),
    source_yRow_eq_rowCompute 13 3 3 3 (by decide),
    source_yRow_eq_rowCompute 13 3 3 4 (by decide),
    source_yRow_eq_rowCompute 13 3 3 5 (by decide),
    source_yRow_eq_rowCompute 13 3 3 6 (by decide),
    computeRow_13_3_3_0, computeRow_13_3_3_1, computeRow_13_3_3_2, computeRow_13_3_3_3, computeRow_13_3_3_4, computeRow_13_3_3_5, computeRow_13_3_3_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_13_3_5 : Y 13 3 5 = (126715690823288866730217/419430400000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 13 3 5 0 (by decide),
    source_yRow_eq_rowCompute 13 3 5 1 (by decide),
    source_yRow_eq_rowCompute 13 3 5 2 (by decide),
    source_yRow_eq_rowCompute 13 3 5 3 (by decide),
    source_yRow_eq_rowCompute 13 3 5 4 (by decide),
    source_yRow_eq_rowCompute 13 3 5 5 (by decide),
    source_yRow_eq_rowCompute 13 3 5 6 (by decide),
    computeRow_13_3_5_0, computeRow_13_3_5_1, computeRow_13_3_5_2, computeRow_13_3_5_3, computeRow_13_3_5_4, computeRow_13_3_5_5, computeRow_13_3_5_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_13_3_7 : Y 13 3 7 = (-500594098074230841463629/2097152000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 13 3 7 0 (by decide),
    source_yRow_eq_rowCompute 13 3 7 1 (by decide),
    source_yRow_eq_rowCompute 13 3 7 2 (by decide),
    source_yRow_eq_rowCompute 13 3 7 3 (by decide),
    source_yRow_eq_rowCompute 13 3 7 4 (by decide),
    source_yRow_eq_rowCompute 13 3 7 5 (by decide),
    source_yRow_eq_rowCompute 13 3 7 6 (by decide),
    computeRow_13_3_7_0, computeRow_13_3_7_1, computeRow_13_3_7_2, computeRow_13_3_7_3, computeRow_13_3_7_4, computeRow_13_3_7_5, computeRow_13_3_7_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_13_3_9 : Y 13 3 9 = (-1215155073315811787592453/2621440000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 13 3 9 0 (by decide),
    source_yRow_eq_rowCompute 13 3 9 1 (by decide),
    source_yRow_eq_rowCompute 13 3 9 2 (by decide),
    source_yRow_eq_rowCompute 13 3 9 3 (by decide),
    source_yRow_eq_rowCompute 13 3 9 4 (by decide),
    source_yRow_eq_rowCompute 13 3 9 5 (by decide),
    source_yRow_eq_rowCompute 13 3 9 6 (by decide),
    computeRow_13_3_9_0, computeRow_13_3_9_1, computeRow_13_3_9_2, computeRow_13_3_9_3, computeRow_13_3_9_4, computeRow_13_3_9_5, computeRow_13_3_9_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_13_3_11 : Y 13 3 11 = (-47337050492347165740927/524288000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 13 3 11 0 (by decide),
    source_yRow_eq_rowCompute 13 3 11 1 (by decide),
    source_yRow_eq_rowCompute 13 3 11 2 (by decide),
    source_yRow_eq_rowCompute 13 3 11 3 (by decide),
    source_yRow_eq_rowCompute 13 3 11 4 (by decide),
    source_yRow_eq_rowCompute 13 3 11 5 (by decide),
    source_yRow_eq_rowCompute 13 3 11 6 (by decide),
    computeRow_13_3_11_0, computeRow_13_3_11_1, computeRow_13_3_11_2, computeRow_13_3_11_3, computeRow_13_3_11_4, computeRow_13_3_11_5, computeRow_13_3_11_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_13_3_13 : Y 13 3 13 = (-394753123867351949086959/131072000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 13 3 13 0 (by decide),
    source_yRow_eq_rowCompute 13 3 13 1 (by decide),
    source_yRow_eq_rowCompute 13 3 13 2 (by decide),
    source_yRow_eq_rowCompute 13 3 13 3 (by decide),
    source_yRow_eq_rowCompute 13 3 13 4 (by decide),
    source_yRow_eq_rowCompute 13 3 13 5 (by decide),
    source_yRow_eq_rowCompute 13 3 13 6 (by decide),
    computeRow_13_3_13_0, computeRow_13_3_13_1, computeRow_13_3_13_2, computeRow_13_3_13_3, computeRow_13_3_13_4, computeRow_13_3_13_5, computeRow_13_3_13_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_13_5_5 : Y 13 5 5 = (-1379799513707028925041063/16777216000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 13 5 5 0 (by decide),
    source_yRow_eq_rowCompute 13 5 5 1 (by decide),
    source_yRow_eq_rowCompute 13 5 5 2 (by decide),
    source_yRow_eq_rowCompute 13 5 5 3 (by decide),
    source_yRow_eq_rowCompute 13 5 5 4 (by decide),
    source_yRow_eq_rowCompute 13 5 5 5 (by decide),
    source_yRow_eq_rowCompute 13 5 5 6 (by decide),
    computeRow_13_5_5_0, computeRow_13_5_5_1, computeRow_13_5_5_2, computeRow_13_5_5_3, computeRow_13_5_5_4, computeRow_13_5_5_5, computeRow_13_5_5_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_13_5_7 : Y 13 5 7 = (701982483744393187744923/8388608000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 13 5 7 0 (by decide),
    source_yRow_eq_rowCompute 13 5 7 1 (by decide),
    source_yRow_eq_rowCompute 13 5 7 2 (by decide),
    source_yRow_eq_rowCompute 13 5 7 3 (by decide),
    source_yRow_eq_rowCompute 13 5 7 4 (by decide),
    source_yRow_eq_rowCompute 13 5 7 5 (by decide),
    source_yRow_eq_rowCompute 13 5 7 6 (by decide),
    computeRow_13_5_7_0, computeRow_13_5_7_1, computeRow_13_5_7_2, computeRow_13_5_7_3, computeRow_13_5_7_4, computeRow_13_5_7_5, computeRow_13_5_7_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_13_5_9 : Y 13 5 9 = (672840394965225922256721/2097152000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 13 5 9 0 (by decide),
    source_yRow_eq_rowCompute 13 5 9 1 (by decide),
    source_yRow_eq_rowCompute 13 5 9 2 (by decide),
    source_yRow_eq_rowCompute 13 5 9 3 (by decide),
    source_yRow_eq_rowCompute 13 5 9 4 (by decide),
    source_yRow_eq_rowCompute 13 5 9 5 (by decide),
    source_yRow_eq_rowCompute 13 5 9 6 (by decide),
    computeRow_13_5_9_0, computeRow_13_5_9_1, computeRow_13_5_9_2, computeRow_13_5_9_3, computeRow_13_5_9_4, computeRow_13_5_9_5, computeRow_13_5_9_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_13_5_11 : Y 13 5 11 = (2506297034373528441573/1048576000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 13 5 11 0 (by decide),
    source_yRow_eq_rowCompute 13 5 11 1 (by decide),
    source_yRow_eq_rowCompute 13 5 11 2 (by decide),
    source_yRow_eq_rowCompute 13 5 11 3 (by decide),
    source_yRow_eq_rowCompute 13 5 11 4 (by decide),
    source_yRow_eq_rowCompute 13 5 11 5 (by decide),
    source_yRow_eq_rowCompute 13 5 11 6 (by decide),
    computeRow_13_5_11_0, computeRow_13_5_11_1, computeRow_13_5_11_2, computeRow_13_5_11_3, computeRow_13_5_11_4, computeRow_13_5_11_5, computeRow_13_5_11_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_13_5_13 : Y 13 5 13 = (5534718096701578046307903/1048576000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 13 5 13 0 (by decide),
    source_yRow_eq_rowCompute 13 5 13 1 (by decide),
    source_yRow_eq_rowCompute 13 5 13 2 (by decide),
    source_yRow_eq_rowCompute 13 5 13 3 (by decide),
    source_yRow_eq_rowCompute 13 5 13 4 (by decide),
    source_yRow_eq_rowCompute 13 5 13 5 (by decide),
    source_yRow_eq_rowCompute 13 5 13 6 (by decide),
    computeRow_13_5_13_0, computeRow_13_5_13_1, computeRow_13_5_13_2, computeRow_13_5_13_3, computeRow_13_5_13_4, computeRow_13_5_13_5, computeRow_13_5_13_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_13_7_7 : Y 13 7 7 = (126607865811947282465541/838860800000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 13 7 7 0 (by decide),
    source_yRow_eq_rowCompute 13 7 7 1 (by decide),
    source_yRow_eq_rowCompute 13 7 7 2 (by decide),
    source_yRow_eq_rowCompute 13 7 7 3 (by decide),
    source_yRow_eq_rowCompute 13 7 7 4 (by decide),
    source_yRow_eq_rowCompute 13 7 7 5 (by decide),
    source_yRow_eq_rowCompute 13 7 7 6 (by decide),
    computeRow_13_7_7_0, computeRow_13_7_7_1, computeRow_13_7_7_2, computeRow_13_7_7_3, computeRow_13_7_7_4, computeRow_13_7_7_5, computeRow_13_7_7_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_13_7_9 : Y 13 7 9 = (-175665130303631642663517/1048576000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 13 7 9 0 (by decide),
    source_yRow_eq_rowCompute 13 7 9 1 (by decide),
    source_yRow_eq_rowCompute 13 7 9 2 (by decide),
    source_yRow_eq_rowCompute 13 7 9 3 (by decide),
    source_yRow_eq_rowCompute 13 7 9 4 (by decide),
    source_yRow_eq_rowCompute 13 7 9 5 (by decide),
    source_yRow_eq_rowCompute 13 7 9 6 (by decide),
    computeRow_13_7_9_0, computeRow_13_7_9_1, computeRow_13_7_9_2, computeRow_13_7_9_3, computeRow_13_7_9_4, computeRow_13_7_9_5, computeRow_13_7_9_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_13_7_11 : Y 13 7 11 = (420722950805223871087107/524288000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 13 7 11 0 (by decide),
    source_yRow_eq_rowCompute 13 7 11 1 (by decide),
    source_yRow_eq_rowCompute 13 7 11 2 (by decide),
    source_yRow_eq_rowCompute 13 7 11 3 (by decide),
    source_yRow_eq_rowCompute 13 7 11 4 (by decide),
    source_yRow_eq_rowCompute 13 7 11 5 (by decide),
    source_yRow_eq_rowCompute 13 7 11 6 (by decide),
    computeRow_13_7_11_0, computeRow_13_7_11_1, computeRow_13_7_11_2, computeRow_13_7_11_3, computeRow_13_7_11_4, computeRow_13_7_11_5, computeRow_13_7_11_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_13_7_13 : Y 13 7 13 = (-2485443250416390286101651/524288000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 13 7 13 0 (by decide),
    source_yRow_eq_rowCompute 13 7 13 1 (by decide),
    source_yRow_eq_rowCompute 13 7 13 2 (by decide),
    source_yRow_eq_rowCompute 13 7 13 3 (by decide),
    source_yRow_eq_rowCompute 13 7 13 4 (by decide),
    source_yRow_eq_rowCompute 13 7 13 5 (by decide),
    source_yRow_eq_rowCompute 13 7 13 6 (by decide),
    computeRow_13_7_13_0, computeRow_13_7_13_1, computeRow_13_7_13_2, computeRow_13_7_13_3, computeRow_13_7_13_4, computeRow_13_7_13_5, computeRow_13_7_13_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_13_9_9 : Y 13 9 9 = (-125541053085493256369427/262144000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 13 9 9 0 (by decide),
    source_yRow_eq_rowCompute 13 9 9 1 (by decide),
    source_yRow_eq_rowCompute 13 9 9 2 (by decide),
    source_yRow_eq_rowCompute 13 9 9 3 (by decide),
    source_yRow_eq_rowCompute 13 9 9 4 (by decide),
    source_yRow_eq_rowCompute 13 9 9 5 (by decide),
    source_yRow_eq_rowCompute 13 9 9 6 (by decide),
    computeRow_13_9_9_0, computeRow_13_9_9_1, computeRow_13_9_9_2, computeRow_13_9_9_3, computeRow_13_9_9_4, computeRow_13_9_9_5, computeRow_13_9_9_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_13_9_11 : Y 13 9 11 = (1437479079722043725179197/655360000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 13 9 11 0 (by decide),
    source_yRow_eq_rowCompute 13 9 11 1 (by decide),
    source_yRow_eq_rowCompute 13 9 11 2 (by decide),
    source_yRow_eq_rowCompute 13 9 11 3 (by decide),
    source_yRow_eq_rowCompute 13 9 11 4 (by decide),
    source_yRow_eq_rowCompute 13 9 11 5 (by decide),
    source_yRow_eq_rowCompute 13 9 11 6 (by decide),
    computeRow_13_9_11_0, computeRow_13_9_11_1, computeRow_13_9_11_2, computeRow_13_9_11_3, computeRow_13_9_11_4, computeRow_13_9_11_5, computeRow_13_9_11_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_13_9_13 : Y 13 9 13 = (-2022830025440980274156781/655360000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 13 9 13 0 (by decide),
    source_yRow_eq_rowCompute 13 9 13 1 (by decide),
    source_yRow_eq_rowCompute 13 9 13 2 (by decide),
    source_yRow_eq_rowCompute 13 9 13 3 (by decide),
    source_yRow_eq_rowCompute 13 9 13 4 (by decide),
    source_yRow_eq_rowCompute 13 9 13 5 (by decide),
    source_yRow_eq_rowCompute 13 9 13 6 (by decide),
    computeRow_13_9_13_0, computeRow_13_9_13_1, computeRow_13_9_13_2, computeRow_13_9_13_3, computeRow_13_9_13_4, computeRow_13_9_13_5, computeRow_13_9_13_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_13_11_11 : Y 13 11 11 = (-184207969249874832456117/65536000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 13 11 11 0 (by decide),
    source_yRow_eq_rowCompute 13 11 11 1 (by decide),
    source_yRow_eq_rowCompute 13 11 11 2 (by decide),
    source_yRow_eq_rowCompute 13 11 11 3 (by decide),
    source_yRow_eq_rowCompute 13 11 11 4 (by decide),
    source_yRow_eq_rowCompute 13 11 11 5 (by decide),
    source_yRow_eq_rowCompute 13 11 11 6 (by decide),
    computeRow_13_11_11_0, computeRow_13_11_11_1, computeRow_13_11_11_2, computeRow_13_11_11_3, computeRow_13_11_11_4, computeRow_13_11_11_5, computeRow_13_11_11_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_13_11_13 : Y 13 11 13 = (252554056596275363975331/65536000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 13 11 13 0 (by decide),
    source_yRow_eq_rowCompute 13 11 13 1 (by decide),
    source_yRow_eq_rowCompute 13 11 13 2 (by decide),
    source_yRow_eq_rowCompute 13 11 13 3 (by decide),
    source_yRow_eq_rowCompute 13 11 13 4 (by decide),
    source_yRow_eq_rowCompute 13 11 13 5 (by decide),
    source_yRow_eq_rowCompute 13 11 13 6 (by decide),
    computeRow_13_11_13_0, computeRow_13_11_13_1, computeRow_13_11_13_2, computeRow_13_11_13_3, computeRow_13_11_13_4, computeRow_13_11_13_5, computeRow_13_11_13_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_13_13_13 : Y 13 13 13 = (-17580701774552693245136811/13107200000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 13 13 13 0 (by decide),
    source_yRow_eq_rowCompute 13 13 13 1 (by decide),
    source_yRow_eq_rowCompute 13 13 13 2 (by decide),
    source_yRow_eq_rowCompute 13 13 13 3 (by decide),
    source_yRow_eq_rowCompute 13 13 13 4 (by decide),
    source_yRow_eq_rowCompute 13 13 13 5 (by decide),
    source_yRow_eq_rowCompute 13 13 13 6 (by decide),
    computeRow_13_13_13_0, computeRow_13_13_13_1, computeRow_13_13_13_2, computeRow_13_13_13_3, computeRow_13_13_13_4, computeRow_13_13_13_5, computeRow_13_13_13_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_gram_13_1_1 : Z 13 1 1 = (958003200 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_13_1_1

theorem source_gram_13_1_3 : Z 13 1 3 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_13_1_3

theorem source_gram_13_1_5 : Z 13 1 5 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_13_1_5

theorem source_gram_13_1_7 : Z 13 1 7 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_13_1_7

theorem source_gram_13_1_9 : Z 13 1 9 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_13_1_9

theorem source_gram_13_1_11 : Z 13 1 11 = (-29937600 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_13_1_11

theorem source_gram_13_1_13 : Z 13 1 13 = (972972000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_13_1_13

theorem source_gram_13_3_3 : Z 13 3 3 = (21772800 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_13_3_3

theorem source_gram_13_3_5 : Z 13 3 5 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_13_3_5

theorem source_gram_13_3_7 : Z 13 3 7 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_13_3_7

theorem source_gram_13_3_9 : Z 13 3 9 = (-2721600 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_13_3_9

theorem source_gram_13_3_11 : Z 13 3 11 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_13_3_11

theorem source_gram_13_3_13 : Z 13 3 13 = (291891600 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_13_3_13

theorem source_gram_13_5_5 : Z 13 5 5 = (4838400 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_13_5_5

theorem source_gram_13_5_7 : Z 13 5 7 = (-907200 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_13_5_7

theorem source_gram_13_5_9 : Z 13 5 9 = (-4082400 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_13_5_9

theorem source_gram_13_5_11 : Z 13 5 11 = (12474000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_13_5_11

theorem source_gram_13_5_13 : Z 13 5 13 = (48648600 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_13_5_13

theorem source_gram_13_7_7 : Z 13 7 7 = (453600 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_13_7_7

theorem source_gram_13_7_9 : Z 13 7 9 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_13_7_9

theorem source_gram_13_7_11 : Z 13 7 11 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_13_7_11

theorem source_gram_13_7_13 : Z 13 7 13 = (-24324300 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_13_7_13

theorem source_gram_13_9_9 : Z 13 9 9 = (5851440 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_13_9_9

theorem source_gram_13_9_11 : Z 13 9 11 = (-16839900 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_13_9_11

theorem source_gram_13_9_13 : Z 13 9 13 = (-36486450 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_13_9_13

theorem source_gram_13_11_11 : Z 13 11 11 = (52390800 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_13_11_11

theorem source_gram_13_11_13 : Z 13 11 13 = (-30405375 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_13_11_13

theorem source_gram_13_13_13 : Z 13 13 13 = (12411474075/2 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_13_13_13

theorem source_error_13_3_1 : Y 13 3 1 = (7563908306608840424871171/8388608000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_13_1_3

theorem source_gram_13_3_1 : Z 13 3 1 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_13_1_3

theorem source_error_13_5_1 : Y 13 5 1 = (-66091999624888726298111247/16777216000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_13_1_5

theorem source_gram_13_5_1 : Z 13 5 1 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_13_1_5

theorem source_error_13_5_3 : Y 13 5 3 = (126715690823288866730217/419430400000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_13_3_5

theorem source_gram_13_5_3 : Z 13 5 3 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_13_3_5

theorem source_error_13_7_1 : Y 13 7 1 = (2728798823338271240310567/1677721600000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_13_1_7

theorem source_gram_13_7_1 : Z 13 7 1 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_13_1_7

theorem source_error_13_7_3 : Y 13 7 3 = (-500594098074230841463629/2097152000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_13_3_7

theorem source_gram_13_7_3 : Z 13 7 3 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_13_3_7

theorem source_error_13_7_5 : Y 13 7 5 = (701982483744393187744923/8388608000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_13_5_7

theorem source_gram_13_7_5 : Z 13 7 5 = (-907200 : ℚ) := by
  rw [Z_symm]
  exact source_gram_13_5_7

theorem source_error_13_9_1 : Y 13 9 1 = (-13501297339814524797227781/10485760000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_13_1_9

theorem source_gram_13_9_1 : Z 13 9 1 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_13_1_9

theorem source_error_13_9_3 : Y 13 9 3 = (-1215155073315811787592453/2621440000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_13_3_9

theorem source_gram_13_9_3 : Z 13 9 3 = (-2721600 : ℚ) := by
  rw [Z_symm]
  exact source_gram_13_3_9

theorem source_error_13_9_5 : Y 13 9 5 = (672840394965225922256721/2097152000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_13_5_9

theorem source_gram_13_9_5 : Z 13 9 5 = (-4082400 : ℚ) := by
  rw [Z_symm]
  exact source_gram_13_5_9

theorem source_error_13_9_7 : Y 13 9 7 = (-175665130303631642663517/1048576000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_13_7_9

theorem source_gram_13_9_7 : Z 13 9 7 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_13_7_9

theorem source_error_13_11_1 : Y 13 11 1 = (12432022452888993488134359/1048576000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_13_1_11

theorem source_gram_13_11_1 : Z 13 11 1 = (-29937600 : ℚ) := by
  rw [Z_symm]
  exact source_gram_13_1_11

theorem source_error_13_11_3 : Y 13 11 3 = (-47337050492347165740927/524288000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_13_3_11

theorem source_gram_13_11_3 : Z 13 11 3 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_13_3_11

theorem source_error_13_11_5 : Y 13 11 5 = (2506297034373528441573/1048576000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_13_5_11

theorem source_gram_13_11_5 : Z 13 11 5 = (12474000 : ℚ) := by
  rw [Z_symm]
  exact source_gram_13_5_11

theorem source_error_13_11_7 : Y 13 11 7 = (420722950805223871087107/524288000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_13_7_11

theorem source_gram_13_11_7 : Z 13 11 7 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_13_7_11

theorem source_error_13_11_9 : Y 13 11 9 = (1437479079722043725179197/655360000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_13_9_11

theorem source_gram_13_11_9 : Z 13 11 9 = (-16839900 : ℚ) := by
  rw [Z_symm]
  exact source_gram_13_9_11

theorem source_error_13_13_1 : Y 13 13 1 = (-165874530574631465579316753/1048576000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_13_1_13

theorem source_gram_13_13_1 : Z 13 13 1 = (972972000 : ℚ) := by
  rw [Z_symm]
  exact source_gram_13_1_13

theorem source_error_13_13_3 : Y 13 13 3 = (-394753123867351949086959/131072000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_13_3_13

theorem source_gram_13_13_3 : Z 13 13 3 = (291891600 : ℚ) := by
  rw [Z_symm]
  exact source_gram_13_3_13

theorem source_error_13_13_5 : Y 13 13 5 = (5534718096701578046307903/1048576000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_13_5_13

theorem source_gram_13_13_5 : Z 13 13 5 = (48648600 : ℚ) := by
  rw [Z_symm]
  exact source_gram_13_5_13

theorem source_error_13_13_7 : Y 13 13 7 = (-2485443250416390286101651/524288000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_13_7_13

theorem source_gram_13_13_7 : Z 13 13 7 = (-24324300 : ℚ) := by
  rw [Z_symm]
  exact source_gram_13_7_13

theorem source_error_13_13_9 : Y 13 13 9 = (-2022830025440980274156781/655360000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_13_9_13

theorem source_gram_13_13_9 : Z 13 13 9 = (-36486450 : ℚ) := by
  rw [Z_symm]
  exact source_gram_13_9_13

theorem source_error_13_13_11 : Y 13 13 11 = (252554056596275363975331/65536000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_13_11_13

theorem source_gram_13_13_11 : Z 13 13 11 = (-30405375 : ℚ) := by
  rw [Z_symm]
  exact source_gram_13_11_13

theorem error_13 : errorRational 13 = candidateY_13 := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact source_error_13_1_1
  · exact source_error_13_1_3
  · exact source_error_13_1_5
  · exact source_error_13_1_7
  · exact source_error_13_1_9
  · exact source_error_13_1_11
  · exact source_error_13_1_13
  · exact source_error_13_3_1
  · exact source_error_13_3_3
  · exact source_error_13_3_5
  · exact source_error_13_3_7
  · exact source_error_13_3_9
  · exact source_error_13_3_11
  · exact source_error_13_3_13
  · exact source_error_13_5_1
  · exact source_error_13_5_3
  · exact source_error_13_5_5
  · exact source_error_13_5_7
  · exact source_error_13_5_9
  · exact source_error_13_5_11
  · exact source_error_13_5_13
  · exact source_error_13_7_1
  · exact source_error_13_7_3
  · exact source_error_13_7_5
  · exact source_error_13_7_7
  · exact source_error_13_7_9
  · exact source_error_13_7_11
  · exact source_error_13_7_13
  · exact source_error_13_9_1
  · exact source_error_13_9_3
  · exact source_error_13_9_5
  · exact source_error_13_9_7
  · exact source_error_13_9_9
  · exact source_error_13_9_11
  · exact source_error_13_9_13
  · exact source_error_13_11_1
  · exact source_error_13_11_3
  · exact source_error_13_11_5
  · exact source_error_13_11_7
  · exact source_error_13_11_9
  · exact source_error_13_11_11
  · exact source_error_13_11_13
  · exact source_error_13_13_1
  · exact source_error_13_13_3
  · exact source_error_13_13_5
  · exact source_error_13_13_7
  · exact source_error_13_13_9
  · exact source_error_13_13_11
  · exact source_error_13_13_13

theorem gram_13 : gramRational 13 = candidateZ_13 := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact source_gram_13_1_1
  · exact source_gram_13_1_3
  · exact source_gram_13_1_5
  · exact source_gram_13_1_7
  · exact source_gram_13_1_9
  · exact source_gram_13_1_11
  · exact source_gram_13_1_13
  · exact source_gram_13_3_1
  · exact source_gram_13_3_3
  · exact source_gram_13_3_5
  · exact source_gram_13_3_7
  · exact source_gram_13_3_9
  · exact source_gram_13_3_11
  · exact source_gram_13_3_13
  · exact source_gram_13_5_1
  · exact source_gram_13_5_3
  · exact source_gram_13_5_5
  · exact source_gram_13_5_7
  · exact source_gram_13_5_9
  · exact source_gram_13_5_11
  · exact source_gram_13_5_13
  · exact source_gram_13_7_1
  · exact source_gram_13_7_3
  · exact source_gram_13_7_5
  · exact source_gram_13_7_7
  · exact source_gram_13_7_9
  · exact source_gram_13_7_11
  · exact source_gram_13_7_13
  · exact source_gram_13_9_1
  · exact source_gram_13_9_3
  · exact source_gram_13_9_5
  · exact source_gram_13_9_7
  · exact source_gram_13_9_9
  · exact source_gram_13_9_11
  · exact source_gram_13_9_13
  · exact source_gram_13_11_1
  · exact source_gram_13_11_3
  · exact source_gram_13_11_5
  · exact source_gram_13_11_7
  · exact source_gram_13_11_9
  · exact source_gram_13_11_11
  · exact source_gram_13_11_13
  · exact source_gram_13_13_1
  · exact source_gram_13_13_3
  · exact source_gram_13_13_5
  · exact source_gram_13_13_7
  · exact source_gram_13_13_9
  · exact source_gram_13_13_11
  · exact source_gram_13_13_13

end Laughlin.Certificate

end OAI
