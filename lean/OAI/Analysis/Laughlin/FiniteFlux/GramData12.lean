import OAI.Analysis.Laughlin.FiniteFlux.ComputeGram01Batch12
import OAI.Analysis.Laughlin.FiniteFlux.ComputeGram03Batch12
import OAI.Analysis.Laughlin.FiniteFlux.ComputeGram05Batch12
import OAI.Analysis.Laughlin.FiniteFlux.ComputeGram07Batch12
import OAI.Analysis.Laughlin.FiniteFlux.ComputeGram09Batch12
import OAI.Analysis.Laughlin.FiniteFlux.ComputeGram111112
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0101Batch12
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0103Batch12
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0105Batch12
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0107Batch12
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0109Batch12
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0111Batch12
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0303Batch12
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0305Batch12
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0307Batch12
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0309Batch12
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0311Batch12
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0505Batch12
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0507Batch12
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0509Batch12
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0511Batch12
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0707Batch12
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0709Batch12
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0711Batch12
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0909Batch12
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0911Batch12
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow1111Batch12
import OAI.Analysis.Laughlin.FiniteFlux.Data12
import OAI.Analysis.Laughlin.FourBody.NumericBridge
import OAI.Analysis.Laughlin.FourBody.Symmetry

namespace OAI

namespace Laughlin.Certificate
theorem source_error_12_1_1 : Y 12 1 1 = (-21758497948837526814361611/16777216000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 12 1 1 0 (by decide),
    source_yRow_eq_rowCompute 12 1 1 1 (by decide),
    source_yRow_eq_rowCompute 12 1 1 2 (by decide),
    source_yRow_eq_rowCompute 12 1 1 3 (by decide),
    source_yRow_eq_rowCompute 12 1 1 4 (by decide),
    source_yRow_eq_rowCompute 12 1 1 5 (by decide),
    source_yRow_eq_rowCompute 12 1 1 6 (by decide),
    computeRow_12_1_1_0, computeRow_12_1_1_1, computeRow_12_1_1_2, computeRow_12_1_1_3, computeRow_12_1_1_4, computeRow_12_1_1_5, computeRow_12_1_1_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_12_1_3 : Y 12 1 3 = (7514500960705467759694389/41943040000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 12 1 3 0 (by decide),
    source_yRow_eq_rowCompute 12 1 3 1 (by decide),
    source_yRow_eq_rowCompute 12 1 3 2 (by decide),
    source_yRow_eq_rowCompute 12 1 3 3 (by decide),
    source_yRow_eq_rowCompute 12 1 3 4 (by decide),
    source_yRow_eq_rowCompute 12 1 3 5 (by decide),
    source_yRow_eq_rowCompute 12 1 3 6 (by decide),
    computeRow_12_1_3_0, computeRow_12_1_3_1, computeRow_12_1_3_2, computeRow_12_1_3_3, computeRow_12_1_3_4, computeRow_12_1_3_5, computeRow_12_1_3_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_12_1_5 : Y 12 1 5 = (3165688667606660909537571/16777216000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 12 1 5 0 (by decide),
    source_yRow_eq_rowCompute 12 1 5 1 (by decide),
    source_yRow_eq_rowCompute 12 1 5 2 (by decide),
    source_yRow_eq_rowCompute 12 1 5 3 (by decide),
    source_yRow_eq_rowCompute 12 1 5 4 (by decide),
    source_yRow_eq_rowCompute 12 1 5 5 (by decide),
    source_yRow_eq_rowCompute 12 1 5 6 (by decide),
    computeRow_12_1_5_0, computeRow_12_1_5_1, computeRow_12_1_5_2, computeRow_12_1_5_3, computeRow_12_1_5_4, computeRow_12_1_5_5, computeRow_12_1_5_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_12_1_7 : Y 12 1 7 = (-41707520784065633150907/8388608000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 12 1 7 0 (by decide),
    source_yRow_eq_rowCompute 12 1 7 1 (by decide),
    source_yRow_eq_rowCompute 12 1 7 2 (by decide),
    source_yRow_eq_rowCompute 12 1 7 3 (by decide),
    source_yRow_eq_rowCompute 12 1 7 4 (by decide),
    source_yRow_eq_rowCompute 12 1 7 5 (by decide),
    source_yRow_eq_rowCompute 12 1 7 6 (by decide),
    computeRow_12_1_7_0, computeRow_12_1_7_1, computeRow_12_1_7_2, computeRow_12_1_7_3, computeRow_12_1_7_4, computeRow_12_1_7_5, computeRow_12_1_7_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_12_1_9 : Y 12 1 9 = (-2287894342236011100448461/10485760000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 12 1 9 0 (by decide),
    source_yRow_eq_rowCompute 12 1 9 1 (by decide),
    source_yRow_eq_rowCompute 12 1 9 2 (by decide),
    source_yRow_eq_rowCompute 12 1 9 3 (by decide),
    source_yRow_eq_rowCompute 12 1 9 4 (by decide),
    source_yRow_eq_rowCompute 12 1 9 5 (by decide),
    source_yRow_eq_rowCompute 12 1 9 6 (by decide),
    computeRow_12_1_9_0, computeRow_12_1_9_1, computeRow_12_1_9_2, computeRow_12_1_9_3, computeRow_12_1_9_4, computeRow_12_1_9_5, computeRow_12_1_9_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_12_1_11 : Y 12 1 11 = (974459105668097994666249/1048576000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 12 1 11 0 (by decide),
    source_yRow_eq_rowCompute 12 1 11 1 (by decide),
    source_yRow_eq_rowCompute 12 1 11 2 (by decide),
    source_yRow_eq_rowCompute 12 1 11 3 (by decide),
    source_yRow_eq_rowCompute 12 1 11 4 (by decide),
    source_yRow_eq_rowCompute 12 1 11 5 (by decide),
    source_yRow_eq_rowCompute 12 1 11 6 (by decide),
    computeRow_12_1_11_0, computeRow_12_1_11_1, computeRow_12_1_11_2, computeRow_12_1_11_3, computeRow_12_1_11_4, computeRow_12_1_11_5, computeRow_12_1_11_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_12_3_3 : Y 12 3 3 = (-2755174567464265689714987/41943040000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 12 3 3 0 (by decide),
    source_yRow_eq_rowCompute 12 3 3 1 (by decide),
    source_yRow_eq_rowCompute 12 3 3 2 (by decide),
    source_yRow_eq_rowCompute 12 3 3 3 (by decide),
    source_yRow_eq_rowCompute 12 3 3 4 (by decide),
    source_yRow_eq_rowCompute 12 3 3 5 (by decide),
    source_yRow_eq_rowCompute 12 3 3 6 (by decide),
    computeRow_12_3_3_0, computeRow_12_3_3_1, computeRow_12_3_3_2, computeRow_12_3_3_3, computeRow_12_3_3_4, computeRow_12_3_3_5, computeRow_12_3_3_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_12_3_5 : Y 12 3 5 = (13005450739700130750669/8388608000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 12 3 5 0 (by decide),
    source_yRow_eq_rowCompute 12 3 5 1 (by decide),
    source_yRow_eq_rowCompute 12 3 5 2 (by decide),
    source_yRow_eq_rowCompute 12 3 5 3 (by decide),
    source_yRow_eq_rowCompute 12 3 5 4 (by decide),
    source_yRow_eq_rowCompute 12 3 5 5 (by decide),
    source_yRow_eq_rowCompute 12 3 5 6 (by decide),
    computeRow_12_3_5_0, computeRow_12_3_5_1, computeRow_12_3_5_2, computeRow_12_3_5_3, computeRow_12_3_5_4, computeRow_12_3_5_5, computeRow_12_3_5_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_12_3_7 : Y 12 3 7 = (81483121238154923538567/4194304000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 12 3 7 0 (by decide),
    source_yRow_eq_rowCompute 12 3 7 1 (by decide),
    source_yRow_eq_rowCompute 12 3 7 2 (by decide),
    source_yRow_eq_rowCompute 12 3 7 3 (by decide),
    source_yRow_eq_rowCompute 12 3 7 4 (by decide),
    source_yRow_eq_rowCompute 12 3 7 5 (by decide),
    source_yRow_eq_rowCompute 12 3 7 6 (by decide),
    computeRow_12_3_7_0, computeRow_12_3_7_1, computeRow_12_3_7_2, computeRow_12_3_7_3, computeRow_12_3_7_4, computeRow_12_3_7_5, computeRow_12_3_7_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_12_3_9 : Y 12 3 9 = (404785016635235824043973/5242880000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 12 3 9 0 (by decide),
    source_yRow_eq_rowCompute 12 3 9 1 (by decide),
    source_yRow_eq_rowCompute 12 3 9 2 (by decide),
    source_yRow_eq_rowCompute 12 3 9 3 (by decide),
    source_yRow_eq_rowCompute 12 3 9 4 (by decide),
    source_yRow_eq_rowCompute 12 3 9 5 (by decide),
    source_yRow_eq_rowCompute 12 3 9 6 (by decide),
    computeRow_12_3_9_0, computeRow_12_3_9_1, computeRow_12_3_9_2, computeRow_12_3_9_3, computeRow_12_3_9_4, computeRow_12_3_9_5, computeRow_12_3_9_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_12_3_11 : Y 12 3 11 = (6215584013984995241823/40960000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 12 3 11 0 (by decide),
    source_yRow_eq_rowCompute 12 3 11 1 (by decide),
    source_yRow_eq_rowCompute 12 3 11 2 (by decide),
    source_yRow_eq_rowCompute 12 3 11 3 (by decide),
    source_yRow_eq_rowCompute 12 3 11 4 (by decide),
    source_yRow_eq_rowCompute 12 3 11 5 (by decide),
    source_yRow_eq_rowCompute 12 3 11 6 (by decide),
    computeRow_12_3_11_0, computeRow_12_3_11_1, computeRow_12_3_11_2, computeRow_12_3_11_3, computeRow_12_3_11_4, computeRow_12_3_11_5, computeRow_12_3_11_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_12_5_5 : Y 12 5 5 = (46805674377515194537803/3355443200000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 12 5 5 0 (by decide),
    source_yRow_eq_rowCompute 12 5 5 1 (by decide),
    source_yRow_eq_rowCompute 12 5 5 2 (by decide),
    source_yRow_eq_rowCompute 12 5 5 3 (by decide),
    source_yRow_eq_rowCompute 12 5 5 4 (by decide),
    source_yRow_eq_rowCompute 12 5 5 5 (by decide),
    source_yRow_eq_rowCompute 12 5 5 6 (by decide),
    computeRow_12_5_5_0, computeRow_12_5_5_1, computeRow_12_5_5_2, computeRow_12_5_5_3, computeRow_12_5_5_4, computeRow_12_5_5_5, computeRow_12_5_5_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_12_5_7 : Y 12 5 7 = (-41483885509932371903727/8388608000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 12 5 7 0 (by decide),
    source_yRow_eq_rowCompute 12 5 7 1 (by decide),
    source_yRow_eq_rowCompute 12 5 7 2 (by decide),
    source_yRow_eq_rowCompute 12 5 7 3 (by decide),
    source_yRow_eq_rowCompute 12 5 7 4 (by decide),
    source_yRow_eq_rowCompute 12 5 7 5 (by decide),
    source_yRow_eq_rowCompute 12 5 7 6 (by decide),
    computeRow_12_5_7_0, computeRow_12_5_7_1, computeRow_12_5_7_2, computeRow_12_5_7_3, computeRow_12_5_7_4, computeRow_12_5_7_5, computeRow_12_5_7_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_12_5_9 : Y 12 5 9 = (-10240121934522536047317/419430400000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 12 5 9 0 (by decide),
    source_yRow_eq_rowCompute 12 5 9 1 (by decide),
    source_yRow_eq_rowCompute 12 5 9 2 (by decide),
    source_yRow_eq_rowCompute 12 5 9 3 (by decide),
    source_yRow_eq_rowCompute 12 5 9 4 (by decide),
    source_yRow_eq_rowCompute 12 5 9 5 (by decide),
    source_yRow_eq_rowCompute 12 5 9 6 (by decide),
    computeRow_12_5_9_0, computeRow_12_5_9_1, computeRow_12_5_9_2, computeRow_12_5_9_3, computeRow_12_5_9_4, computeRow_12_5_9_5, computeRow_12_5_9_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_12_5_11 : Y 12 5 11 = (-25627330574660171363787/1048576000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 12 5 11 0 (by decide),
    source_yRow_eq_rowCompute 12 5 11 1 (by decide),
    source_yRow_eq_rowCompute 12 5 11 2 (by decide),
    source_yRow_eq_rowCompute 12 5 11 3 (by decide),
    source_yRow_eq_rowCompute 12 5 11 4 (by decide),
    source_yRow_eq_rowCompute 12 5 11 5 (by decide),
    source_yRow_eq_rowCompute 12 5 11 6 (by decide),
    computeRow_12_5_11_0, computeRow_12_5_11_1, computeRow_12_5_11_2, computeRow_12_5_11_3, computeRow_12_5_11_4, computeRow_12_5_11_5, computeRow_12_5_11_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_12_7_7 : Y 12 7 7 = (-192219299280069275276433/4194304000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 12 7 7 0 (by decide),
    source_yRow_eq_rowCompute 12 7 7 1 (by decide),
    source_yRow_eq_rowCompute 12 7 7 2 (by decide),
    source_yRow_eq_rowCompute 12 7 7 3 (by decide),
    source_yRow_eq_rowCompute 12 7 7 4 (by decide),
    source_yRow_eq_rowCompute 12 7 7 5 (by decide),
    source_yRow_eq_rowCompute 12 7 7 6 (by decide),
    computeRow_12_7_7_0, computeRow_12_7_7_1, computeRow_12_7_7_2, computeRow_12_7_7_3, computeRow_12_7_7_4, computeRow_12_7_7_5, computeRow_12_7_7_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_12_7_9 : Y 12 7 9 = (-42262827210616968341919/1048576000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 12 7 9 0 (by decide),
    source_yRow_eq_rowCompute 12 7 9 1 (by decide),
    source_yRow_eq_rowCompute 12 7 9 2 (by decide),
    source_yRow_eq_rowCompute 12 7 9 3 (by decide),
    source_yRow_eq_rowCompute 12 7 9 4 (by decide),
    source_yRow_eq_rowCompute 12 7 9 5 (by decide),
    source_yRow_eq_rowCompute 12 7 9 6 (by decide),
    computeRow_12_7_9_0, computeRow_12_7_9_1, computeRow_12_7_9_2, computeRow_12_7_9_3, computeRow_12_7_9_4, computeRow_12_7_9_5, computeRow_12_7_9_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_12_7_11 : Y 12 7 11 = (102387833991081458685459/524288000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 12 7 11 0 (by decide),
    source_yRow_eq_rowCompute 12 7 11 1 (by decide),
    source_yRow_eq_rowCompute 12 7 11 2 (by decide),
    source_yRow_eq_rowCompute 12 7 11 3 (by decide),
    source_yRow_eq_rowCompute 12 7 11 4 (by decide),
    source_yRow_eq_rowCompute 12 7 11 5 (by decide),
    source_yRow_eq_rowCompute 12 7 11 6 (by decide),
    computeRow_12_7_11_0, computeRow_12_7_11_1, computeRow_12_7_11_2, computeRow_12_7_11_3, computeRow_12_7_11_4, computeRow_12_7_11_5, computeRow_12_7_11_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_12_9_9 : Y 12 9 9 = (42184147125974825030859/1310720000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 12 9 9 0 (by decide),
    source_yRow_eq_rowCompute 12 9 9 1 (by decide),
    source_yRow_eq_rowCompute 12 9 9 2 (by decide),
    source_yRow_eq_rowCompute 12 9 9 3 (by decide),
    source_yRow_eq_rowCompute 12 9 9 4 (by decide),
    source_yRow_eq_rowCompute 12 9 9 5 (by decide),
    source_yRow_eq_rowCompute 12 9 9 6 (by decide),
    computeRow_12_9_9_0, computeRow_12_9_9_1, computeRow_12_9_9_2, computeRow_12_9_9_3, computeRow_12_9_9_4, computeRow_12_9_9_5, computeRow_12_9_9_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_12_9_11 : Y 12 9 11 = (18732467483584451907057/655360000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 12 9 11 0 (by decide),
    source_yRow_eq_rowCompute 12 9 11 1 (by decide),
    source_yRow_eq_rowCompute 12 9 11 2 (by decide),
    source_yRow_eq_rowCompute 12 9 11 3 (by decide),
    source_yRow_eq_rowCompute 12 9 11 4 (by decide),
    source_yRow_eq_rowCompute 12 9 11 5 (by decide),
    source_yRow_eq_rowCompute 12 9 11 6 (by decide),
    computeRow_12_9_11_0, computeRow_12_9_11_1, computeRow_12_9_11_2, computeRow_12_9_11_3, computeRow_12_9_11_4, computeRow_12_9_11_5, computeRow_12_9_11_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_12_11_11 : Y 12 11 11 = (-330567209557174956464307/65536000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 12 11 11 0 (by decide),
    source_yRow_eq_rowCompute 12 11 11 1 (by decide),
    source_yRow_eq_rowCompute 12 11 11 2 (by decide),
    source_yRow_eq_rowCompute 12 11 11 3 (by decide),
    source_yRow_eq_rowCompute 12 11 11 4 (by decide),
    source_yRow_eq_rowCompute 12 11 11 5 (by decide),
    source_yRow_eq_rowCompute 12 11 11 6 (by decide),
    computeRow_12_11_11_0, computeRow_12_11_11_1, computeRow_12_11_11_2, computeRow_12_11_11_3, computeRow_12_11_11_4, computeRow_12_11_11_5, computeRow_12_11_11_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_gram_12_1_1 : Z 12 1 1 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_12_1_1

theorem source_gram_12_1_3 : Z 12 1 3 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_12_1_3

theorem source_gram_12_1_5 : Z 12 1 5 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_12_1_5

theorem source_gram_12_1_7 : Z 12 1 7 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_12_1_7

theorem source_gram_12_1_9 : Z 12 1 9 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_12_1_9

theorem source_gram_12_1_11 : Z 12 1 11 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_12_1_11

theorem source_gram_12_3_3 : Z 12 3 3 = (2177280 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_12_3_3

theorem source_gram_12_3_5 : Z 12 3 5 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_12_3_5

theorem source_gram_12_3_7 : Z 12 3 7 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_12_3_7

theorem source_gram_12_3_9 : Z 12 3 9 = (-1088640 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_12_3_9

theorem source_gram_12_3_11 : Z 12 3 11 = (7484400 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_12_3_11

theorem source_gram_12_5_5 : Z 12 5 5 = (604800 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_12_5_5

theorem source_gram_12_5_7 : Z 12 5 7 = (-453600 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_12_5_7

theorem source_gram_12_5_9 : Z 12 5 9 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_12_5_9

theorem source_gram_12_5_11 : Z 12 5 11 = (2494800 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_12_5_11

theorem source_gram_12_7_7 : Z 12 7 7 = (340200 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_12_7_7

theorem source_gram_12_7_9 : Z 12 7 9 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_12_7_9

theorem source_gram_12_7_11 : Z 12 7 11 = (-1871100 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_12_7_11

theorem source_gram_12_9_9 : Z 12 9 9 = (544320 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_12_9_9

theorem source_gram_12_9_11 : Z 12 9 11 = (-3742200 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_12_9_11

theorem source_gram_12_11_11 : Z 12 11 11 = (36018675 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_12_11_11

theorem source_error_12_3_1 : Y 12 3 1 = (7514500960705467759694389/41943040000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_12_1_3

theorem source_gram_12_3_1 : Z 12 3 1 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_12_1_3

theorem source_error_12_5_1 : Y 12 5 1 = (3165688667606660909537571/16777216000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_12_1_5

theorem source_gram_12_5_1 : Z 12 5 1 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_12_1_5

theorem source_error_12_5_3 : Y 12 5 3 = (13005450739700130750669/8388608000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_12_3_5

theorem source_gram_12_5_3 : Z 12 5 3 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_12_3_5

theorem source_error_12_7_1 : Y 12 7 1 = (-41707520784065633150907/8388608000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_12_1_7

theorem source_gram_12_7_1 : Z 12 7 1 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_12_1_7

theorem source_error_12_7_3 : Y 12 7 3 = (81483121238154923538567/4194304000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_12_3_7

theorem source_gram_12_7_3 : Z 12 7 3 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_12_3_7

theorem source_error_12_7_5 : Y 12 7 5 = (-41483885509932371903727/8388608000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_12_5_7

theorem source_gram_12_7_5 : Z 12 7 5 = (-453600 : ℚ) := by
  rw [Z_symm]
  exact source_gram_12_5_7

theorem source_error_12_9_1 : Y 12 9 1 = (-2287894342236011100448461/10485760000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_12_1_9

theorem source_gram_12_9_1 : Z 12 9 1 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_12_1_9

theorem source_error_12_9_3 : Y 12 9 3 = (404785016635235824043973/5242880000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_12_3_9

theorem source_gram_12_9_3 : Z 12 9 3 = (-1088640 : ℚ) := by
  rw [Z_symm]
  exact source_gram_12_3_9

theorem source_error_12_9_5 : Y 12 9 5 = (-10240121934522536047317/419430400000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_12_5_9

theorem source_gram_12_9_5 : Z 12 9 5 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_12_5_9

theorem source_error_12_9_7 : Y 12 9 7 = (-42262827210616968341919/1048576000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_12_7_9

theorem source_gram_12_9_7 : Z 12 9 7 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_12_7_9

theorem source_error_12_11_1 : Y 12 11 1 = (974459105668097994666249/1048576000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_12_1_11

theorem source_gram_12_11_1 : Z 12 11 1 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_12_1_11

theorem source_error_12_11_3 : Y 12 11 3 = (6215584013984995241823/40960000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_12_3_11

theorem source_gram_12_11_3 : Z 12 11 3 = (7484400 : ℚ) := by
  rw [Z_symm]
  exact source_gram_12_3_11

theorem source_error_12_11_5 : Y 12 11 5 = (-25627330574660171363787/1048576000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_12_5_11

theorem source_gram_12_11_5 : Z 12 11 5 = (2494800 : ℚ) := by
  rw [Z_symm]
  exact source_gram_12_5_11

theorem source_error_12_11_7 : Y 12 11 7 = (102387833991081458685459/524288000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_12_7_11

theorem source_gram_12_11_7 : Z 12 11 7 = (-1871100 : ℚ) := by
  rw [Z_symm]
  exact source_gram_12_7_11

theorem source_error_12_11_9 : Y 12 11 9 = (18732467483584451907057/655360000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_12_9_11

theorem source_gram_12_11_9 : Z 12 11 9 = (-3742200 : ℚ) := by
  rw [Z_symm]
  exact source_gram_12_9_11

theorem error_12 : errorRational 12 = candidateY_12 := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact source_error_12_1_1
  · exact source_error_12_1_3
  · exact source_error_12_1_5
  · exact source_error_12_1_7
  · exact source_error_12_1_9
  · exact source_error_12_1_11
  · exact source_error_12_3_1
  · exact source_error_12_3_3
  · exact source_error_12_3_5
  · exact source_error_12_3_7
  · exact source_error_12_3_9
  · exact source_error_12_3_11
  · exact source_error_12_5_1
  · exact source_error_12_5_3
  · exact source_error_12_5_5
  · exact source_error_12_5_7
  · exact source_error_12_5_9
  · exact source_error_12_5_11
  · exact source_error_12_7_1
  · exact source_error_12_7_3
  · exact source_error_12_7_5
  · exact source_error_12_7_7
  · exact source_error_12_7_9
  · exact source_error_12_7_11
  · exact source_error_12_9_1
  · exact source_error_12_9_3
  · exact source_error_12_9_5
  · exact source_error_12_9_7
  · exact source_error_12_9_9
  · exact source_error_12_9_11
  · exact source_error_12_11_1
  · exact source_error_12_11_3
  · exact source_error_12_11_5
  · exact source_error_12_11_7
  · exact source_error_12_11_9
  · exact source_error_12_11_11

theorem gram_12 : gramRational 12 = candidateZ_12 := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact source_gram_12_1_1
  · exact source_gram_12_1_3
  · exact source_gram_12_1_5
  · exact source_gram_12_1_7
  · exact source_gram_12_1_9
  · exact source_gram_12_1_11
  · exact source_gram_12_3_1
  · exact source_gram_12_3_3
  · exact source_gram_12_3_5
  · exact source_gram_12_3_7
  · exact source_gram_12_3_9
  · exact source_gram_12_3_11
  · exact source_gram_12_5_1
  · exact source_gram_12_5_3
  · exact source_gram_12_5_5
  · exact source_gram_12_5_7
  · exact source_gram_12_5_9
  · exact source_gram_12_5_11
  · exact source_gram_12_7_1
  · exact source_gram_12_7_3
  · exact source_gram_12_7_5
  · exact source_gram_12_7_7
  · exact source_gram_12_7_9
  · exact source_gram_12_7_11
  · exact source_gram_12_9_1
  · exact source_gram_12_9_3
  · exact source_gram_12_9_5
  · exact source_gram_12_9_7
  · exact source_gram_12_9_9
  · exact source_gram_12_9_11
  · exact source_gram_12_11_1
  · exact source_gram_12_11_3
  · exact source_gram_12_11_5
  · exact source_gram_12_11_7
  · exact source_gram_12_11_9
  · exact source_gram_12_11_11

end Laughlin.Certificate

end OAI
