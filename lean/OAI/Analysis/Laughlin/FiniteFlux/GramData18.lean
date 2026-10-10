import OAI.Analysis.Laughlin.FiniteFlux.ComputeGram01Batch18
import OAI.Analysis.Laughlin.FiniteFlux.ComputeGram03Batch18
import OAI.Analysis.Laughlin.FiniteFlux.ComputeGram05Batch18
import OAI.Analysis.Laughlin.FiniteFlux.ComputeGram07Batch18
import OAI.Analysis.Laughlin.FiniteFlux.ComputeGram09Batch18
import OAI.Analysis.Laughlin.FiniteFlux.ComputeGram11Batch18
import OAI.Analysis.Laughlin.FiniteFlux.ComputeGram13Batch18
import OAI.Analysis.Laughlin.FiniteFlux.ComputeGram15Batch18
import OAI.Analysis.Laughlin.FiniteFlux.ComputeGram171718
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0101Batch18
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0103Batch18
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0105Batch18
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0107Batch18
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0109Batch18
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0111Batch18
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0113Batch18
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0115Batch18
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0117Batch18
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0303Batch18
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0305Batch18
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0307Batch18
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0309Batch18
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0311Batch18
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0313Batch18
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0315Batch18
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0317Batch18
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0505Batch18
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0507Batch18
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0509Batch18
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0511Batch18
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0513Batch18
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0515Batch18
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0517Batch18
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0707Batch18
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0709Batch18
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0711Batch18
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0713Batch18
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0715Batch18
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0717Batch18
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0909Batch18
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0911Batch18
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0913Batch18
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0915Batch18
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0917Batch18
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow1111Batch18
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow1113Batch18
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow1115Batch18
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow1117Batch18
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow1313Batch18
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow1315Batch18
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow1317Batch18
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow1515Batch18
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow1517Batch18
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow1717Batch18
import OAI.Analysis.Laughlin.FiniteFlux.Data18
import OAI.Analysis.Laughlin.FourBody.NumericBridge
import OAI.Analysis.Laughlin.FourBody.Symmetry

namespace OAI

namespace Laughlin.Certificate
theorem source_error_18_1_1 : Y 18 1 1 = (-3559166385880423516847027379/41943040000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 18 1 1 0 (by decide),
    source_yRow_eq_rowCompute 18 1 1 1 (by decide),
    source_yRow_eq_rowCompute 18 1 1 2 (by decide),
    source_yRow_eq_rowCompute 18 1 1 3 (by decide),
    source_yRow_eq_rowCompute 18 1 1 4 (by decide),
    source_yRow_eq_rowCompute 18 1 1 5 (by decide),
    source_yRow_eq_rowCompute 18 1 1 6 (by decide),
    computeRow_18_1_1_0, computeRow_18_1_1_1, computeRow_18_1_1_2, computeRow_18_1_1_3, computeRow_18_1_1_4, computeRow_18_1_1_5, computeRow_18_1_1_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_18_1_3 : Y 18 1 3 = (43700029260178412251303173/3276800000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 18 1 3 0 (by decide),
    source_yRow_eq_rowCompute 18 1 3 1 (by decide),
    source_yRow_eq_rowCompute 18 1 3 2 (by decide),
    source_yRow_eq_rowCompute 18 1 3 3 (by decide),
    source_yRow_eq_rowCompute 18 1 3 4 (by decide),
    source_yRow_eq_rowCompute 18 1 3 5 (by decide),
    source_yRow_eq_rowCompute 18 1 3 6 (by decide),
    computeRow_18_1_3_0, computeRow_18_1_3_1, computeRow_18_1_3_2, computeRow_18_1_3_3, computeRow_18_1_3_4, computeRow_18_1_3_5, computeRow_18_1_3_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_18_1_5 : Y 18 1 5 = (-157097886646298732847063351/41943040000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 18 1 5 0 (by decide),
    source_yRow_eq_rowCompute 18 1 5 1 (by decide),
    source_yRow_eq_rowCompute 18 1 5 2 (by decide),
    source_yRow_eq_rowCompute 18 1 5 3 (by decide),
    source_yRow_eq_rowCompute 18 1 5 4 (by decide),
    source_yRow_eq_rowCompute 18 1 5 5 (by decide),
    source_yRow_eq_rowCompute 18 1 5 6 (by decide),
    computeRow_18_1_5_0, computeRow_18_1_5_1, computeRow_18_1_5_2, computeRow_18_1_5_3, computeRow_18_1_5_4, computeRow_18_1_5_5, computeRow_18_1_5_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_18_1_7 : Y 18 1 7 = (45795850251189055946275347/20971520000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 18 1 7 0 (by decide),
    source_yRow_eq_rowCompute 18 1 7 1 (by decide),
    source_yRow_eq_rowCompute 18 1 7 2 (by decide),
    source_yRow_eq_rowCompute 18 1 7 3 (by decide),
    source_yRow_eq_rowCompute 18 1 7 4 (by decide),
    source_yRow_eq_rowCompute 18 1 7 5 (by decide),
    source_yRow_eq_rowCompute 18 1 7 6 (by decide),
    computeRow_18_1_7_0, computeRow_18_1_7_1, computeRow_18_1_7_2, computeRow_18_1_7_3, computeRow_18_1_7_4, computeRow_18_1_7_5, computeRow_18_1_7_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_18_1_9 : Y 18 1 9 = (-15768543277252499592049191/5242880000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 18 1 9 0 (by decide),
    source_yRow_eq_rowCompute 18 1 9 1 (by decide),
    source_yRow_eq_rowCompute 18 1 9 2 (by decide),
    source_yRow_eq_rowCompute 18 1 9 3 (by decide),
    source_yRow_eq_rowCompute 18 1 9 4 (by decide),
    source_yRow_eq_rowCompute 18 1 9 5 (by decide),
    source_yRow_eq_rowCompute 18 1 9 6 (by decide),
    computeRow_18_1_9_0, computeRow_18_1_9_1, computeRow_18_1_9_2, computeRow_18_1_9_3, computeRow_18_1_9_4, computeRow_18_1_9_5, computeRow_18_1_9_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_18_1_11 : Y 18 1 11 = (15774590706413201698776741/2621440000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 18 1 11 0 (by decide),
    source_yRow_eq_rowCompute 18 1 11 1 (by decide),
    source_yRow_eq_rowCompute 18 1 11 2 (by decide),
    source_yRow_eq_rowCompute 18 1 11 3 (by decide),
    source_yRow_eq_rowCompute 18 1 11 4 (by decide),
    source_yRow_eq_rowCompute 18 1 11 5 (by decide),
    source_yRow_eq_rowCompute 18 1 11 6 (by decide),
    computeRow_18_1_11_0, computeRow_18_1_11_1, computeRow_18_1_11_2, computeRow_18_1_11_3, computeRow_18_1_11_4, computeRow_18_1_11_5, computeRow_18_1_11_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_18_1_13 : Y 18 1 13 = (-111481601475376052708801013/13107200000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 18 1 13 0 (by decide),
    source_yRow_eq_rowCompute 18 1 13 1 (by decide),
    source_yRow_eq_rowCompute 18 1 13 2 (by decide),
    source_yRow_eq_rowCompute 18 1 13 3 (by decide),
    source_yRow_eq_rowCompute 18 1 13 4 (by decide),
    source_yRow_eq_rowCompute 18 1 13 5 (by decide),
    source_yRow_eq_rowCompute 18 1 13 6 (by decide),
    computeRow_18_1_13_0, computeRow_18_1_13_1, computeRow_18_1_13_2, computeRow_18_1_13_3, computeRow_18_1_13_4, computeRow_18_1_13_5, computeRow_18_1_13_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_18_1_15 : Y 18 1 15 = (-58408977661685586058262139/1310720000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 18 1 15 0 (by decide),
    source_yRow_eq_rowCompute 18 1 15 1 (by decide),
    source_yRow_eq_rowCompute 18 1 15 2 (by decide),
    source_yRow_eq_rowCompute 18 1 15 3 (by decide),
    source_yRow_eq_rowCompute 18 1 15 4 (by decide),
    source_yRow_eq_rowCompute 18 1 15 5 (by decide),
    source_yRow_eq_rowCompute 18 1 15 6 (by decide),
    computeRow_18_1_15_0, computeRow_18_1_15_1, computeRow_18_1_15_2, computeRow_18_1_15_3, computeRow_18_1_15_4, computeRow_18_1_15_5, computeRow_18_1_15_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_18_1_17 : Y 18 1 17 = (0 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 18 1 17 0 (by decide),
    source_yRow_eq_rowCompute 18 1 17 1 (by decide),
    source_yRow_eq_rowCompute 18 1 17 2 (by decide),
    source_yRow_eq_rowCompute 18 1 17 3 (by decide),
    source_yRow_eq_rowCompute 18 1 17 4 (by decide),
    source_yRow_eq_rowCompute 18 1 17 5 (by decide),
    source_yRow_eq_rowCompute 18 1 17 6 (by decide),
    computeRow_18_1_17_0, computeRow_18_1_17_1, computeRow_18_1_17_2, computeRow_18_1_17_3, computeRow_18_1_17_4, computeRow_18_1_17_5, computeRow_18_1_17_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_18_3_3 : Y 18 3 3 = (-81940194402186836366199549/26214400000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 18 3 3 0 (by decide),
    source_yRow_eq_rowCompute 18 3 3 1 (by decide),
    source_yRow_eq_rowCompute 18 3 3 2 (by decide),
    source_yRow_eq_rowCompute 18 3 3 3 (by decide),
    source_yRow_eq_rowCompute 18 3 3 4 (by decide),
    source_yRow_eq_rowCompute 18 3 3 5 (by decide),
    source_yRow_eq_rowCompute 18 3 3 6 (by decide),
    computeRow_18_3_3_0, computeRow_18_3_3_1, computeRow_18_3_3_2, computeRow_18_3_3_3, computeRow_18_3_3_4, computeRow_18_3_3_5, computeRow_18_3_3_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_18_3_5 : Y 18 3 5 = (5636036629375968042063837/5242880000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 18 3 5 0 (by decide),
    source_yRow_eq_rowCompute 18 3 5 1 (by decide),
    source_yRow_eq_rowCompute 18 3 5 2 (by decide),
    source_yRow_eq_rowCompute 18 3 5 3 (by decide),
    source_yRow_eq_rowCompute 18 3 5 4 (by decide),
    source_yRow_eq_rowCompute 18 3 5 5 (by decide),
    source_yRow_eq_rowCompute 18 3 5 6 (by decide),
    computeRow_18_3_5_0, computeRow_18_3_5_1, computeRow_18_3_5_2, computeRow_18_3_5_3, computeRow_18_3_5_4, computeRow_18_3_5_5, computeRow_18_3_5_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_18_3_7 : Y 18 3 7 = (-2298714004872189626128407/5242880000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 18 3 7 0 (by decide),
    source_yRow_eq_rowCompute 18 3 7 1 (by decide),
    source_yRow_eq_rowCompute 18 3 7 2 (by decide),
    source_yRow_eq_rowCompute 18 3 7 3 (by decide),
    source_yRow_eq_rowCompute 18 3 7 4 (by decide),
    source_yRow_eq_rowCompute 18 3 7 5 (by decide),
    source_yRow_eq_rowCompute 18 3 7 6 (by decide),
    computeRow_18_3_7_0, computeRow_18_3_7_1, computeRow_18_3_7_2, computeRow_18_3_7_3, computeRow_18_3_7_4, computeRow_18_3_7_5, computeRow_18_3_7_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_18_3_9 : Y 18 3 9 = (297813059860269307535181/1638400000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 18 3 9 0 (by decide),
    source_yRow_eq_rowCompute 18 3 9 1 (by decide),
    source_yRow_eq_rowCompute 18 3 9 2 (by decide),
    source_yRow_eq_rowCompute 18 3 9 3 (by decide),
    source_yRow_eq_rowCompute 18 3 9 4 (by decide),
    source_yRow_eq_rowCompute 18 3 9 5 (by decide),
    source_yRow_eq_rowCompute 18 3 9 6 (by decide),
    computeRow_18_3_9_0, computeRow_18_3_9_1, computeRow_18_3_9_2, computeRow_18_3_9_3, computeRow_18_3_9_4, computeRow_18_3_9_5, computeRow_18_3_9_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_18_3_11 : Y 18 3 11 = (-427966983073658698687017/3276800000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 18 3 11 0 (by decide),
    source_yRow_eq_rowCompute 18 3 11 1 (by decide),
    source_yRow_eq_rowCompute 18 3 11 2 (by decide),
    source_yRow_eq_rowCompute 18 3 11 3 (by decide),
    source_yRow_eq_rowCompute 18 3 11 4 (by decide),
    source_yRow_eq_rowCompute 18 3 11 5 (by decide),
    source_yRow_eq_rowCompute 18 3 11 6 (by decide),
    computeRow_18_3_11_0, computeRow_18_3_11_1, computeRow_18_3_11_2, computeRow_18_3_11_3, computeRow_18_3_11_4, computeRow_18_3_11_5, computeRow_18_3_11_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_18_3_13 : Y 18 3 13 = (460639052423449997118021/1638400000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 18 3 13 0 (by decide),
    source_yRow_eq_rowCompute 18 3 13 1 (by decide),
    source_yRow_eq_rowCompute 18 3 13 2 (by decide),
    source_yRow_eq_rowCompute 18 3 13 3 (by decide),
    source_yRow_eq_rowCompute 18 3 13 4 (by decide),
    source_yRow_eq_rowCompute 18 3 13 5 (by decide),
    source_yRow_eq_rowCompute 18 3 13 6 (by decide),
    computeRow_18_3_13_0, computeRow_18_3_13_1, computeRow_18_3_13_2, computeRow_18_3_13_3, computeRow_18_3_13_4, computeRow_18_3_13_5, computeRow_18_3_13_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_18_3_15 : Y 18 3 15 = (856489912851915268585659/327680000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 18 3 15 0 (by decide),
    source_yRow_eq_rowCompute 18 3 15 1 (by decide),
    source_yRow_eq_rowCompute 18 3 15 2 (by decide),
    source_yRow_eq_rowCompute 18 3 15 3 (by decide),
    source_yRow_eq_rowCompute 18 3 15 4 (by decide),
    source_yRow_eq_rowCompute 18 3 15 5 (by decide),
    source_yRow_eq_rowCompute 18 3 15 6 (by decide),
    computeRow_18_3_15_0, computeRow_18_3_15_1, computeRow_18_3_15_2, computeRow_18_3_15_3, computeRow_18_3_15_4, computeRow_18_3_15_5, computeRow_18_3_15_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_18_3_17 : Y 18 3 17 = (0 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 18 3 17 0 (by decide),
    source_yRow_eq_rowCompute 18 3 17 1 (by decide),
    source_yRow_eq_rowCompute 18 3 17 2 (by decide),
    source_yRow_eq_rowCompute 18 3 17 3 (by decide),
    source_yRow_eq_rowCompute 18 3 17 4 (by decide),
    source_yRow_eq_rowCompute 18 3 17 5 (by decide),
    source_yRow_eq_rowCompute 18 3 17 6 (by decide),
    computeRow_18_3_17_0, computeRow_18_3_17_1, computeRow_18_3_17_2, computeRow_18_3_17_3, computeRow_18_3_17_4, computeRow_18_3_17_5, computeRow_18_3_17_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_18_5_5 : Y 18 5 5 = (-17038127051364859101889227/41943040000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 18 5 5 0 (by decide),
    source_yRow_eq_rowCompute 18 5 5 1 (by decide),
    source_yRow_eq_rowCompute 18 5 5 2 (by decide),
    source_yRow_eq_rowCompute 18 5 5 3 (by decide),
    source_yRow_eq_rowCompute 18 5 5 4 (by decide),
    source_yRow_eq_rowCompute 18 5 5 5 (by decide),
    source_yRow_eq_rowCompute 18 5 5 6 (by decide),
    computeRow_18_5_5_0, computeRow_18_5_5_1, computeRow_18_5_5_2, computeRow_18_5_5_3, computeRow_18_5_5_4, computeRow_18_5_5_5, computeRow_18_5_5_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_18_5_7 : Y 18 5 7 = (3236875371562490528333463/20971520000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 18 5 7 0 (by decide),
    source_yRow_eq_rowCompute 18 5 7 1 (by decide),
    source_yRow_eq_rowCompute 18 5 7 2 (by decide),
    source_yRow_eq_rowCompute 18 5 7 3 (by decide),
    source_yRow_eq_rowCompute 18 5 7 4 (by decide),
    source_yRow_eq_rowCompute 18 5 7 5 (by decide),
    source_yRow_eq_rowCompute 18 5 7 6 (by decide),
    computeRow_18_5_7_0, computeRow_18_5_7_1, computeRow_18_5_7_2, computeRow_18_5_7_3, computeRow_18_5_7_4, computeRow_18_5_7_5, computeRow_18_5_7_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_18_5_9 : Y 18 5 9 = (109159200441997398693/5242880000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 18 5 9 0 (by decide),
    source_yRow_eq_rowCompute 18 5 9 1 (by decide),
    source_yRow_eq_rowCompute 18 5 9 2 (by decide),
    source_yRow_eq_rowCompute 18 5 9 3 (by decide),
    source_yRow_eq_rowCompute 18 5 9 4 (by decide),
    source_yRow_eq_rowCompute 18 5 9 5 (by decide),
    source_yRow_eq_rowCompute 18 5 9 6 (by decide),
    computeRow_18_5_9_0, computeRow_18_5_9_1, computeRow_18_5_9_2, computeRow_18_5_9_3, computeRow_18_5_9_4, computeRow_18_5_9_5, computeRow_18_5_9_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_18_5_11 : Y 18 5 11 = (-76974792598120601955771/524288000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 18 5 11 0 (by decide),
    source_yRow_eq_rowCompute 18 5 11 1 (by decide),
    source_yRow_eq_rowCompute 18 5 11 2 (by decide),
    source_yRow_eq_rowCompute 18 5 11 3 (by decide),
    source_yRow_eq_rowCompute 18 5 11 4 (by decide),
    source_yRow_eq_rowCompute 18 5 11 5 (by decide),
    source_yRow_eq_rowCompute 18 5 11 6 (by decide),
    computeRow_18_5_11_0, computeRow_18_5_11_1, computeRow_18_5_11_2, computeRow_18_5_11_3, computeRow_18_5_11_4, computeRow_18_5_11_5, computeRow_18_5_11_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_18_5_13 : Y 18 5 13 = (525900691396984091231043/2621440000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 18 5 13 0 (by decide),
    source_yRow_eq_rowCompute 18 5 13 1 (by decide),
    source_yRow_eq_rowCompute 18 5 13 2 (by decide),
    source_yRow_eq_rowCompute 18 5 13 3 (by decide),
    source_yRow_eq_rowCompute 18 5 13 4 (by decide),
    source_yRow_eq_rowCompute 18 5 13 5 (by decide),
    source_yRow_eq_rowCompute 18 5 13 6 (by decide),
    computeRow_18_5_13_0, computeRow_18_5_13_1, computeRow_18_5_13_2, computeRow_18_5_13_3, computeRow_18_5_13_4, computeRow_18_5_13_5, computeRow_18_5_13_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_18_5_15 : Y 18 5 15 = (166478085484275751174989/262144000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 18 5 15 0 (by decide),
    source_yRow_eq_rowCompute 18 5 15 1 (by decide),
    source_yRow_eq_rowCompute 18 5 15 2 (by decide),
    source_yRow_eq_rowCompute 18 5 15 3 (by decide),
    source_yRow_eq_rowCompute 18 5 15 4 (by decide),
    source_yRow_eq_rowCompute 18 5 15 5 (by decide),
    source_yRow_eq_rowCompute 18 5 15 6 (by decide),
    computeRow_18_5_15_0, computeRow_18_5_15_1, computeRow_18_5_15_2, computeRow_18_5_15_3, computeRow_18_5_15_4, computeRow_18_5_15_5, computeRow_18_5_15_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_18_5_17 : Y 18 5 17 = (0 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 18 5 17 0 (by decide),
    source_yRow_eq_rowCompute 18 5 17 1 (by decide),
    source_yRow_eq_rowCompute 18 5 17 2 (by decide),
    source_yRow_eq_rowCompute 18 5 17 3 (by decide),
    source_yRow_eq_rowCompute 18 5 17 4 (by decide),
    source_yRow_eq_rowCompute 18 5 17 5 (by decide),
    source_yRow_eq_rowCompute 18 5 17 6 (by decide),
    computeRow_18_5_17_0, computeRow_18_5_17_1, computeRow_18_5_17_2, computeRow_18_5_17_3, computeRow_18_5_17_4, computeRow_18_5_17_5, computeRow_18_5_17_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_18_7_7 : Y 18 7 7 = (-152920142255560594957119/2097152000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 18 7 7 0 (by decide),
    source_yRow_eq_rowCompute 18 7 7 1 (by decide),
    source_yRow_eq_rowCompute 18 7 7 2 (by decide),
    source_yRow_eq_rowCompute 18 7 7 3 (by decide),
    source_yRow_eq_rowCompute 18 7 7 4 (by decide),
    source_yRow_eq_rowCompute 18 7 7 5 (by decide),
    source_yRow_eq_rowCompute 18 7 7 6 (by decide),
    computeRow_18_7_7_0, computeRow_18_7_7_1, computeRow_18_7_7_2, computeRow_18_7_7_3, computeRow_18_7_7_4, computeRow_18_7_7_5, computeRow_18_7_7_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_18_7_9 : Y 18 7 9 = (76480320836604209603463/2621440000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 18 7 9 0 (by decide),
    source_yRow_eq_rowCompute 18 7 9 1 (by decide),
    source_yRow_eq_rowCompute 18 7 9 2 (by decide),
    source_yRow_eq_rowCompute 18 7 9 3 (by decide),
    source_yRow_eq_rowCompute 18 7 9 4 (by decide),
    source_yRow_eq_rowCompute 18 7 9 5 (by decide),
    source_yRow_eq_rowCompute 18 7 9 6 (by decide),
    computeRow_18_7_9_0, computeRow_18_7_9_1, computeRow_18_7_9_2, computeRow_18_7_9_3, computeRow_18_7_9_4, computeRow_18_7_9_5, computeRow_18_7_9_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_18_7_11 : Y 18 7 11 = (34507713700153945513647/1310720000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 18 7 11 0 (by decide),
    source_yRow_eq_rowCompute 18 7 11 1 (by decide),
    source_yRow_eq_rowCompute 18 7 11 2 (by decide),
    source_yRow_eq_rowCompute 18 7 11 3 (by decide),
    source_yRow_eq_rowCompute 18 7 11 4 (by decide),
    source_yRow_eq_rowCompute 18 7 11 5 (by decide),
    source_yRow_eq_rowCompute 18 7 11 6 (by decide),
    computeRow_18_7_11_0, computeRow_18_7_11_1, computeRow_18_7_11_2, computeRow_18_7_11_3, computeRow_18_7_11_4, computeRow_18_7_11_5, computeRow_18_7_11_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_18_7_13 : Y 18 7 13 = (-126720387057916007218863/1310720000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 18 7 13 0 (by decide),
    source_yRow_eq_rowCompute 18 7 13 1 (by decide),
    source_yRow_eq_rowCompute 18 7 13 2 (by decide),
    source_yRow_eq_rowCompute 18 7 13 3 (by decide),
    source_yRow_eq_rowCompute 18 7 13 4 (by decide),
    source_yRow_eq_rowCompute 18 7 13 5 (by decide),
    source_yRow_eq_rowCompute 18 7 13 6 (by decide),
    computeRow_18_7_13_0, computeRow_18_7_13_1, computeRow_18_7_13_2, computeRow_18_7_13_3, computeRow_18_7_13_4, computeRow_18_7_13_5, computeRow_18_7_13_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_18_7_15 : Y 18 7 15 = (-293804443074929463225549/655360000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 18 7 15 0 (by decide),
    source_yRow_eq_rowCompute 18 7 15 1 (by decide),
    source_yRow_eq_rowCompute 18 7 15 2 (by decide),
    source_yRow_eq_rowCompute 18 7 15 3 (by decide),
    source_yRow_eq_rowCompute 18 7 15 4 (by decide),
    source_yRow_eq_rowCompute 18 7 15 5 (by decide),
    source_yRow_eq_rowCompute 18 7 15 6 (by decide),
    computeRow_18_7_15_0, computeRow_18_7_15_1, computeRow_18_7_15_2, computeRow_18_7_15_3, computeRow_18_7_15_4, computeRow_18_7_15_5, computeRow_18_7_15_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_18_7_17 : Y 18 7 17 = (0 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 18 7 17 0 (by decide),
    source_yRow_eq_rowCompute 18 7 17 1 (by decide),
    source_yRow_eq_rowCompute 18 7 17 2 (by decide),
    source_yRow_eq_rowCompute 18 7 17 3 (by decide),
    source_yRow_eq_rowCompute 18 7 17 4 (by decide),
    source_yRow_eq_rowCompute 18 7 17 5 (by decide),
    source_yRow_eq_rowCompute 18 7 17 6 (by decide),
    computeRow_18_7_17_0, computeRow_18_7_17_1, computeRow_18_7_17_2, computeRow_18_7_17_3, computeRow_18_7_17_4, computeRow_18_7_17_5, computeRow_18_7_17_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_18_9_9 : Y 18 9 9 = (-59366777784768563477067/655360000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 18 9 9 0 (by decide),
    source_yRow_eq_rowCompute 18 9 9 1 (by decide),
    source_yRow_eq_rowCompute 18 9 9 2 (by decide),
    source_yRow_eq_rowCompute 18 9 9 3 (by decide),
    source_yRow_eq_rowCompute 18 9 9 4 (by decide),
    source_yRow_eq_rowCompute 18 9 9 5 (by decide),
    source_yRow_eq_rowCompute 18 9 9 6 (by decide),
    computeRow_18_9_9_0, computeRow_18_9_9_1, computeRow_18_9_9_2, computeRow_18_9_9_3, computeRow_18_9_9_4, computeRow_18_9_9_5, computeRow_18_9_9_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_18_9_11 : Y 18 9 11 = (50562764756881342854273/327680000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 18 9 11 0 (by decide),
    source_yRow_eq_rowCompute 18 9 11 1 (by decide),
    source_yRow_eq_rowCompute 18 9 11 2 (by decide),
    source_yRow_eq_rowCompute 18 9 11 3 (by decide),
    source_yRow_eq_rowCompute 18 9 11 4 (by decide),
    source_yRow_eq_rowCompute 18 9 11 5 (by decide),
    source_yRow_eq_rowCompute 18 9 11 6 (by decide),
    computeRow_18_9_11_0, computeRow_18_9_11_1, computeRow_18_9_11_2, computeRow_18_9_11_3, computeRow_18_9_11_4, computeRow_18_9_11_5, computeRow_18_9_11_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_18_9_13 : Y 18 9 13 = (-141645844790470070219169/1638400000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 18 9 13 0 (by decide),
    source_yRow_eq_rowCompute 18 9 13 1 (by decide),
    source_yRow_eq_rowCompute 18 9 13 2 (by decide),
    source_yRow_eq_rowCompute 18 9 13 3 (by decide),
    source_yRow_eq_rowCompute 18 9 13 4 (by decide),
    source_yRow_eq_rowCompute 18 9 13 5 (by decide),
    source_yRow_eq_rowCompute 18 9 13 6 (by decide),
    computeRow_18_9_13_0, computeRow_18_9_13_1, computeRow_18_9_13_2, computeRow_18_9_13_3, computeRow_18_9_13_4, computeRow_18_9_13_5, computeRow_18_9_13_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_18_9_15 : Y 18 9 15 = (-70438571087878610696079/163840000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 18 9 15 0 (by decide),
    source_yRow_eq_rowCompute 18 9 15 1 (by decide),
    source_yRow_eq_rowCompute 18 9 15 2 (by decide),
    source_yRow_eq_rowCompute 18 9 15 3 (by decide),
    source_yRow_eq_rowCompute 18 9 15 4 (by decide),
    source_yRow_eq_rowCompute 18 9 15 5 (by decide),
    source_yRow_eq_rowCompute 18 9 15 6 (by decide),
    computeRow_18_9_15_0, computeRow_18_9_15_1, computeRow_18_9_15_2, computeRow_18_9_15_3, computeRow_18_9_15_4, computeRow_18_9_15_5, computeRow_18_9_15_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_18_9_17 : Y 18 9 17 = (0 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 18 9 17 0 (by decide),
    source_yRow_eq_rowCompute 18 9 17 1 (by decide),
    source_yRow_eq_rowCompute 18 9 17 2 (by decide),
    source_yRow_eq_rowCompute 18 9 17 3 (by decide),
    source_yRow_eq_rowCompute 18 9 17 4 (by decide),
    source_yRow_eq_rowCompute 18 9 17 5 (by decide),
    source_yRow_eq_rowCompute 18 9 17 6 (by decide),
    computeRow_18_9_17_0, computeRow_18_9_17_1, computeRow_18_9_17_2, computeRow_18_9_17_3, computeRow_18_9_17_4, computeRow_18_9_17_5, computeRow_18_9_17_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_18_11_11 : Y 18 11 11 = (-60223184109272615717979/163840000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 18 11 11 0 (by decide),
    source_yRow_eq_rowCompute 18 11 11 1 (by decide),
    source_yRow_eq_rowCompute 18 11 11 2 (by decide),
    source_yRow_eq_rowCompute 18 11 11 3 (by decide),
    source_yRow_eq_rowCompute 18 11 11 4 (by decide),
    source_yRow_eq_rowCompute 18 11 11 5 (by decide),
    source_yRow_eq_rowCompute 18 11 11 6 (by decide),
    computeRow_18_11_11_0, computeRow_18_11_11_1, computeRow_18_11_11_2, computeRow_18_11_11_3, computeRow_18_11_11_4, computeRow_18_11_11_5, computeRow_18_11_11_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_18_11_13 : Y 18 11 13 = (241267392281008969222347/819200000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 18 11 13 0 (by decide),
    source_yRow_eq_rowCompute 18 11 13 1 (by decide),
    source_yRow_eq_rowCompute 18 11 13 2 (by decide),
    source_yRow_eq_rowCompute 18 11 13 3 (by decide),
    source_yRow_eq_rowCompute 18 11 13 4 (by decide),
    source_yRow_eq_rowCompute 18 11 13 5 (by decide),
    source_yRow_eq_rowCompute 18 11 13 6 (by decide),
    computeRow_18_11_13_0, computeRow_18_11_13_1, computeRow_18_11_13_2, computeRow_18_11_13_3, computeRow_18_11_13_4, computeRow_18_11_13_5, computeRow_18_11_13_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_18_11_15 : Y 18 11 15 = (153598002652096074585513/81920000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 18 11 15 0 (by decide),
    source_yRow_eq_rowCompute 18 11 15 1 (by decide),
    source_yRow_eq_rowCompute 18 11 15 2 (by decide),
    source_yRow_eq_rowCompute 18 11 15 3 (by decide),
    source_yRow_eq_rowCompute 18 11 15 4 (by decide),
    source_yRow_eq_rowCompute 18 11 15 5 (by decide),
    source_yRow_eq_rowCompute 18 11 15 6 (by decide),
    computeRow_18_11_15_0, computeRow_18_11_15_1, computeRow_18_11_15_2, computeRow_18_11_15_3, computeRow_18_11_15_4, computeRow_18_11_15_5, computeRow_18_11_15_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_18_11_17 : Y 18 11 17 = (0 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 18 11 17 0 (by decide),
    source_yRow_eq_rowCompute 18 11 17 1 (by decide),
    source_yRow_eq_rowCompute 18 11 17 2 (by decide),
    source_yRow_eq_rowCompute 18 11 17 3 (by decide),
    source_yRow_eq_rowCompute 18 11 17 4 (by decide),
    source_yRow_eq_rowCompute 18 11 17 5 (by decide),
    source_yRow_eq_rowCompute 18 11 17 6 (by decide),
    computeRow_18_11_17_0, computeRow_18_11_17_1, computeRow_18_11_17_2, computeRow_18_11_17_3, computeRow_18_11_17_4, computeRow_18_11_17_5, computeRow_18_11_17_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_18_13_13 : Y 18 13 13 = (-149658956021574385833447/819200000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 18 13 13 0 (by decide),
    source_yRow_eq_rowCompute 18 13 13 1 (by decide),
    source_yRow_eq_rowCompute 18 13 13 2 (by decide),
    source_yRow_eq_rowCompute 18 13 13 3 (by decide),
    source_yRow_eq_rowCompute 18 13 13 4 (by decide),
    source_yRow_eq_rowCompute 18 13 13 5 (by decide),
    source_yRow_eq_rowCompute 18 13 13 6 (by decide),
    computeRow_18_13_13_0, computeRow_18_13_13_1, computeRow_18_13_13_2, computeRow_18_13_13_3, computeRow_18_13_13_4, computeRow_18_13_13_5, computeRow_18_13_13_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_18_13_15 : Y 18 13 15 = (-32035926190597582065813/16384000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 18 13 15 0 (by decide),
    source_yRow_eq_rowCompute 18 13 15 1 (by decide),
    source_yRow_eq_rowCompute 18 13 15 2 (by decide),
    source_yRow_eq_rowCompute 18 13 15 3 (by decide),
    source_yRow_eq_rowCompute 18 13 15 4 (by decide),
    source_yRow_eq_rowCompute 18 13 15 5 (by decide),
    source_yRow_eq_rowCompute 18 13 15 6 (by decide),
    computeRow_18_13_15_0, computeRow_18_13_15_1, computeRow_18_13_15_2, computeRow_18_13_15_3, computeRow_18_13_15_4, computeRow_18_13_15_5, computeRow_18_13_15_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_18_13_17 : Y 18 13 17 = (0 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 18 13 17 0 (by decide),
    source_yRow_eq_rowCompute 18 13 17 1 (by decide),
    source_yRow_eq_rowCompute 18 13 17 2 (by decide),
    source_yRow_eq_rowCompute 18 13 17 3 (by decide),
    source_yRow_eq_rowCompute 18 13 17 4 (by decide),
    source_yRow_eq_rowCompute 18 13 17 5 (by decide),
    source_yRow_eq_rowCompute 18 13 17 6 (by decide),
    computeRow_18_13_17_0, computeRow_18_13_17_1, computeRow_18_13_17_2, computeRow_18_13_17_3, computeRow_18_13_17_4, computeRow_18_13_17_5, computeRow_18_13_17_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_18_15_15 : Y 18 15 15 = (-884740548279231685308267/40960000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 18 15 15 0 (by decide),
    source_yRow_eq_rowCompute 18 15 15 1 (by decide),
    source_yRow_eq_rowCompute 18 15 15 2 (by decide),
    source_yRow_eq_rowCompute 18 15 15 3 (by decide),
    source_yRow_eq_rowCompute 18 15 15 4 (by decide),
    source_yRow_eq_rowCompute 18 15 15 5 (by decide),
    source_yRow_eq_rowCompute 18 15 15 6 (by decide),
    computeRow_18_15_15_0, computeRow_18_15_15_1, computeRow_18_15_15_2, computeRow_18_15_15_3, computeRow_18_15_15_4, computeRow_18_15_15_5, computeRow_18_15_15_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_18_15_17 : Y 18 15 17 = (0 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 18 15 17 0 (by decide),
    source_yRow_eq_rowCompute 18 15 17 1 (by decide),
    source_yRow_eq_rowCompute 18 15 17 2 (by decide),
    source_yRow_eq_rowCompute 18 15 17 3 (by decide),
    source_yRow_eq_rowCompute 18 15 17 4 (by decide),
    source_yRow_eq_rowCompute 18 15 17 5 (by decide),
    source_yRow_eq_rowCompute 18 15 17 6 (by decide),
    computeRow_18_15_17_0, computeRow_18_15_17_1, computeRow_18_15_17_2, computeRow_18_15_17_3, computeRow_18_15_17_4, computeRow_18_15_17_5, computeRow_18_15_17_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_18_17_17 : Y 18 17 17 = (0 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 18 17 17 0 (by decide),
    source_yRow_eq_rowCompute 18 17 17 1 (by decide),
    source_yRow_eq_rowCompute 18 17 17 2 (by decide),
    source_yRow_eq_rowCompute 18 17 17 3 (by decide),
    source_yRow_eq_rowCompute 18 17 17 4 (by decide),
    source_yRow_eq_rowCompute 18 17 17 5 (by decide),
    source_yRow_eq_rowCompute 18 17 17 6 (by decide),
    computeRow_18_17_17_0, computeRow_18_17_17_1, computeRow_18_17_17_2, computeRow_18_17_17_3, computeRow_18_17_17_4, computeRow_18_17_17_5, computeRow_18_17_17_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_gram_18_1_1 : Z 18 1 1 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_18_1_1

theorem source_gram_18_1_3 : Z 18 1 3 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_18_1_3

theorem source_gram_18_1_5 : Z 18 1 5 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_18_1_5

theorem source_gram_18_1_7 : Z 18 1 7 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_18_1_7

theorem source_gram_18_1_9 : Z 18 1 9 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_18_1_9

theorem source_gram_18_1_11 : Z 18 1 11 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_18_1_11

theorem source_gram_18_1_13 : Z 18 1 13 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_18_1_13

theorem source_gram_18_1_15 : Z 18 1 15 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_18_1_15

theorem source_gram_18_1_17 : Z 18 1 17 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_18_1_17

theorem source_gram_18_3_3 : Z 18 3 3 = (7846046208000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_18_3_3

theorem source_gram_18_3_5 : Z 18 3 5 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_18_3_5

theorem source_gram_18_3_7 : Z 18 3 7 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_18_3_7

theorem source_gram_18_3_9 : Z 18 3 9 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_18_3_9

theorem source_gram_18_3_11 : Z 18 3 11 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_18_3_11

theorem source_gram_18_3_13 : Z 18 3 13 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_18_3_13

theorem source_gram_18_3_15 : Z 18 3 15 = (-858161304000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_18_3_15

theorem source_gram_18_3_17 : Z 18 3 17 = (16672848192000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_18_3_17

theorem source_gram_18_5_5 : Z 18 5 5 = (747242496000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_18_5_5

theorem source_gram_18_5_7 : Z 18 5 7 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_18_5_7

theorem source_gram_18_5_9 : Z 18 5 9 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_18_5_9

theorem source_gram_18_5_11 : Z 18 5 11 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_18_5_11

theorem source_gram_18_5_13 : Z 18 5 13 = (-140107968000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_18_5_13

theorem source_gram_18_5_15 : Z 18 5 15 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_18_5_15

theorem source_gram_18_5_17 : Z 18 5 17 = (11115232128000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_18_5_17

theorem source_gram_18_7_7 : Z 18 7 7 = (201180672000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_18_7_7

theorem source_gram_18_7_9 : Z 18 7 9 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_18_7_9

theorem source_gram_18_7_11 : Z 18 7 11 = (-47151720000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_18_7_11

theorem source_gram_18_7_13 : Z 18 7 13 = (-163459296000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_18_7_13

theorem source_gram_18_7_15 : Z 18 7 15 = (643620978000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_18_7_15

theorem source_gram_18_7_17 : Z 18 7 17 = (4168212048000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_18_7_17

theorem source_gram_18_9_9 : Z 18 9 9 = (98761420800 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_18_9_9

theorem source_gram_18_9_11 : Z 18 9 11 = (-113164128000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_18_9_11

theorem source_gram_18_9_13 : Z 18 9 13 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_18_9_13

theorem source_gram_18_9_15 : Z 18 9 15 = (367783416000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_18_9_15

theorem source_gram_18_9_17 : Z 18 9 17 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_18_9_17

theorem source_gram_18_11_11 : Z 18 11 11 = (149313780000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_18_11_11

theorem source_gram_18_11_13 : Z 18 11 13 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_18_11_13

theorem source_gram_18_11_15 : Z 18 11 15 = (-421418497500 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_18_11_15

theorem source_gram_18_11_17 : Z 18 11 17 = (-1736755020000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_18_11_17

theorem source_gram_18_13_13 : Z 18 13 13 = (329837508000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_18_13_13

theorem source_gram_18_13_15 : Z 18 13 15 = (-1195296102000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_18_13_15

theorem source_gram_18_13_17 : Z 18 13 17 = (-2084106024000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_18_13_17

theorem source_gram_18_15_15 : Z 18 15 15 = (6169949911125 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_18_15_15

theorem source_gram_18_15_17 : Z 18 15 17 = (-1823592771000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_18_15_17

theorem source_gram_18_17_17 : Z 18 17 17 = (354298024080000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_18_17_17

theorem source_error_18_3_1 : Y 18 3 1 = (43700029260178412251303173/3276800000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_18_1_3

theorem source_gram_18_3_1 : Z 18 3 1 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_18_1_3

theorem source_error_18_5_1 : Y 18 5 1 = (-157097886646298732847063351/41943040000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_18_1_5

theorem source_gram_18_5_1 : Z 18 5 1 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_18_1_5

theorem source_error_18_5_3 : Y 18 5 3 = (5636036629375968042063837/5242880000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_18_3_5

theorem source_gram_18_5_3 : Z 18 5 3 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_18_3_5

theorem source_error_18_7_1 : Y 18 7 1 = (45795850251189055946275347/20971520000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_18_1_7

theorem source_gram_18_7_1 : Z 18 7 1 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_18_1_7

theorem source_error_18_7_3 : Y 18 7 3 = (-2298714004872189626128407/5242880000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_18_3_7

theorem source_gram_18_7_3 : Z 18 7 3 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_18_3_7

theorem source_error_18_7_5 : Y 18 7 5 = (3236875371562490528333463/20971520000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_18_5_7

theorem source_gram_18_7_5 : Z 18 7 5 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_18_5_7

theorem source_error_18_9_1 : Y 18 9 1 = (-15768543277252499592049191/5242880000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_18_1_9

theorem source_gram_18_9_1 : Z 18 9 1 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_18_1_9

theorem source_error_18_9_3 : Y 18 9 3 = (297813059860269307535181/1638400000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_18_3_9

theorem source_gram_18_9_3 : Z 18 9 3 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_18_3_9

theorem source_error_18_9_5 : Y 18 9 5 = (109159200441997398693/5242880000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_18_5_9

theorem source_gram_18_9_5 : Z 18 9 5 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_18_5_9

theorem source_error_18_9_7 : Y 18 9 7 = (76480320836604209603463/2621440000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_18_7_9

theorem source_gram_18_9_7 : Z 18 9 7 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_18_7_9

theorem source_error_18_11_1 : Y 18 11 1 = (15774590706413201698776741/2621440000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_18_1_11

theorem source_gram_18_11_1 : Z 18 11 1 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_18_1_11

theorem source_error_18_11_3 : Y 18 11 3 = (-427966983073658698687017/3276800000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_18_3_11

theorem source_gram_18_11_3 : Z 18 11 3 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_18_3_11

theorem source_error_18_11_5 : Y 18 11 5 = (-76974792598120601955771/524288000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_18_5_11

theorem source_gram_18_11_5 : Z 18 11 5 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_18_5_11

theorem source_error_18_11_7 : Y 18 11 7 = (34507713700153945513647/1310720000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_18_7_11

theorem source_gram_18_11_7 : Z 18 11 7 = (-47151720000 : ℚ) := by
  rw [Z_symm]
  exact source_gram_18_7_11

theorem source_error_18_11_9 : Y 18 11 9 = (50562764756881342854273/327680000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_18_9_11

theorem source_gram_18_11_9 : Z 18 11 9 = (-113164128000 : ℚ) := by
  rw [Z_symm]
  exact source_gram_18_9_11

theorem source_error_18_13_1 : Y 18 13 1 = (-111481601475376052708801013/13107200000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_18_1_13

theorem source_gram_18_13_1 : Z 18 13 1 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_18_1_13

theorem source_error_18_13_3 : Y 18 13 3 = (460639052423449997118021/1638400000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_18_3_13

theorem source_gram_18_13_3 : Z 18 13 3 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_18_3_13

theorem source_error_18_13_5 : Y 18 13 5 = (525900691396984091231043/2621440000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_18_5_13

theorem source_gram_18_13_5 : Z 18 13 5 = (-140107968000 : ℚ) := by
  rw [Z_symm]
  exact source_gram_18_5_13

theorem source_error_18_13_7 : Y 18 13 7 = (-126720387057916007218863/1310720000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_18_7_13

theorem source_gram_18_13_7 : Z 18 13 7 = (-163459296000 : ℚ) := by
  rw [Z_symm]
  exact source_gram_18_7_13

theorem source_error_18_13_9 : Y 18 13 9 = (-141645844790470070219169/1638400000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_18_9_13

theorem source_gram_18_13_9 : Z 18 13 9 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_18_9_13

theorem source_error_18_13_11 : Y 18 13 11 = (241267392281008969222347/819200000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_18_11_13

theorem source_gram_18_13_11 : Z 18 13 11 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_18_11_13

theorem source_error_18_15_1 : Y 18 15 1 = (-58408977661685586058262139/1310720000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_18_1_15

theorem source_gram_18_15_1 : Z 18 15 1 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_18_1_15

theorem source_error_18_15_3 : Y 18 15 3 = (856489912851915268585659/327680000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_18_3_15

theorem source_gram_18_15_3 : Z 18 15 3 = (-858161304000 : ℚ) := by
  rw [Z_symm]
  exact source_gram_18_3_15

theorem source_error_18_15_5 : Y 18 15 5 = (166478085484275751174989/262144000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_18_5_15

theorem source_gram_18_15_5 : Z 18 15 5 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_18_5_15

theorem source_error_18_15_7 : Y 18 15 7 = (-293804443074929463225549/655360000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_18_7_15

theorem source_gram_18_15_7 : Z 18 15 7 = (643620978000 : ℚ) := by
  rw [Z_symm]
  exact source_gram_18_7_15

theorem source_error_18_15_9 : Y 18 15 9 = (-70438571087878610696079/163840000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_18_9_15

theorem source_gram_18_15_9 : Z 18 15 9 = (367783416000 : ℚ) := by
  rw [Z_symm]
  exact source_gram_18_9_15

theorem source_error_18_15_11 : Y 18 15 11 = (153598002652096074585513/81920000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_18_11_15

theorem source_gram_18_15_11 : Z 18 15 11 = (-421418497500 : ℚ) := by
  rw [Z_symm]
  exact source_gram_18_11_15

theorem source_error_18_15_13 : Y 18 15 13 = (-32035926190597582065813/16384000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_18_13_15

theorem source_gram_18_15_13 : Z 18 15 13 = (-1195296102000 : ℚ) := by
  rw [Z_symm]
  exact source_gram_18_13_15

theorem source_error_18_17_1 : Y 18 17 1 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_18_1_17

theorem source_gram_18_17_1 : Z 18 17 1 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_18_1_17

theorem source_error_18_17_3 : Y 18 17 3 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_18_3_17

theorem source_gram_18_17_3 : Z 18 17 3 = (16672848192000 : ℚ) := by
  rw [Z_symm]
  exact source_gram_18_3_17

theorem source_error_18_17_5 : Y 18 17 5 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_18_5_17

theorem source_gram_18_17_5 : Z 18 17 5 = (11115232128000 : ℚ) := by
  rw [Z_symm]
  exact source_gram_18_5_17

theorem source_error_18_17_7 : Y 18 17 7 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_18_7_17

theorem source_gram_18_17_7 : Z 18 17 7 = (4168212048000 : ℚ) := by
  rw [Z_symm]
  exact source_gram_18_7_17

theorem source_error_18_17_9 : Y 18 17 9 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_18_9_17

theorem source_gram_18_17_9 : Z 18 17 9 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_18_9_17

theorem source_error_18_17_11 : Y 18 17 11 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_18_11_17

theorem source_gram_18_17_11 : Z 18 17 11 = (-1736755020000 : ℚ) := by
  rw [Z_symm]
  exact source_gram_18_11_17

theorem source_error_18_17_13 : Y 18 17 13 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_18_13_17

theorem source_gram_18_17_13 : Z 18 17 13 = (-2084106024000 : ℚ) := by
  rw [Z_symm]
  exact source_gram_18_13_17

theorem source_error_18_17_15 : Y 18 17 15 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_18_15_17

theorem source_gram_18_17_15 : Z 18 17 15 = (-1823592771000 : ℚ) := by
  rw [Z_symm]
  exact source_gram_18_15_17

theorem error_18 : errorRational 18 = candidateY_18 := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact source_error_18_1_1
  · exact source_error_18_1_3
  · exact source_error_18_1_5
  · exact source_error_18_1_7
  · exact source_error_18_1_9
  · exact source_error_18_1_11
  · exact source_error_18_1_13
  · exact source_error_18_1_15
  · exact source_error_18_1_17
  · exact source_error_18_3_1
  · exact source_error_18_3_3
  · exact source_error_18_3_5
  · exact source_error_18_3_7
  · exact source_error_18_3_9
  · exact source_error_18_3_11
  · exact source_error_18_3_13
  · exact source_error_18_3_15
  · exact source_error_18_3_17
  · exact source_error_18_5_1
  · exact source_error_18_5_3
  · exact source_error_18_5_5
  · exact source_error_18_5_7
  · exact source_error_18_5_9
  · exact source_error_18_5_11
  · exact source_error_18_5_13
  · exact source_error_18_5_15
  · exact source_error_18_5_17
  · exact source_error_18_7_1
  · exact source_error_18_7_3
  · exact source_error_18_7_5
  · exact source_error_18_7_7
  · exact source_error_18_7_9
  · exact source_error_18_7_11
  · exact source_error_18_7_13
  · exact source_error_18_7_15
  · exact source_error_18_7_17
  · exact source_error_18_9_1
  · exact source_error_18_9_3
  · exact source_error_18_9_5
  · exact source_error_18_9_7
  · exact source_error_18_9_9
  · exact source_error_18_9_11
  · exact source_error_18_9_13
  · exact source_error_18_9_15
  · exact source_error_18_9_17
  · exact source_error_18_11_1
  · exact source_error_18_11_3
  · exact source_error_18_11_5
  · exact source_error_18_11_7
  · exact source_error_18_11_9
  · exact source_error_18_11_11
  · exact source_error_18_11_13
  · exact source_error_18_11_15
  · exact source_error_18_11_17
  · exact source_error_18_13_1
  · exact source_error_18_13_3
  · exact source_error_18_13_5
  · exact source_error_18_13_7
  · exact source_error_18_13_9
  · exact source_error_18_13_11
  · exact source_error_18_13_13
  · exact source_error_18_13_15
  · exact source_error_18_13_17
  · exact source_error_18_15_1
  · exact source_error_18_15_3
  · exact source_error_18_15_5
  · exact source_error_18_15_7
  · exact source_error_18_15_9
  · exact source_error_18_15_11
  · exact source_error_18_15_13
  · exact source_error_18_15_15
  · exact source_error_18_15_17
  · exact source_error_18_17_1
  · exact source_error_18_17_3
  · exact source_error_18_17_5
  · exact source_error_18_17_7
  · exact source_error_18_17_9
  · exact source_error_18_17_11
  · exact source_error_18_17_13
  · exact source_error_18_17_15
  · exact source_error_18_17_17

theorem gram_18 : gramRational 18 = candidateZ_18 := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact source_gram_18_1_1
  · exact source_gram_18_1_3
  · exact source_gram_18_1_5
  · exact source_gram_18_1_7
  · exact source_gram_18_1_9
  · exact source_gram_18_1_11
  · exact source_gram_18_1_13
  · exact source_gram_18_1_15
  · exact source_gram_18_1_17
  · exact source_gram_18_3_1
  · exact source_gram_18_3_3
  · exact source_gram_18_3_5
  · exact source_gram_18_3_7
  · exact source_gram_18_3_9
  · exact source_gram_18_3_11
  · exact source_gram_18_3_13
  · exact source_gram_18_3_15
  · exact source_gram_18_3_17
  · exact source_gram_18_5_1
  · exact source_gram_18_5_3
  · exact source_gram_18_5_5
  · exact source_gram_18_5_7
  · exact source_gram_18_5_9
  · exact source_gram_18_5_11
  · exact source_gram_18_5_13
  · exact source_gram_18_5_15
  · exact source_gram_18_5_17
  · exact source_gram_18_7_1
  · exact source_gram_18_7_3
  · exact source_gram_18_7_5
  · exact source_gram_18_7_7
  · exact source_gram_18_7_9
  · exact source_gram_18_7_11
  · exact source_gram_18_7_13
  · exact source_gram_18_7_15
  · exact source_gram_18_7_17
  · exact source_gram_18_9_1
  · exact source_gram_18_9_3
  · exact source_gram_18_9_5
  · exact source_gram_18_9_7
  · exact source_gram_18_9_9
  · exact source_gram_18_9_11
  · exact source_gram_18_9_13
  · exact source_gram_18_9_15
  · exact source_gram_18_9_17
  · exact source_gram_18_11_1
  · exact source_gram_18_11_3
  · exact source_gram_18_11_5
  · exact source_gram_18_11_7
  · exact source_gram_18_11_9
  · exact source_gram_18_11_11
  · exact source_gram_18_11_13
  · exact source_gram_18_11_15
  · exact source_gram_18_11_17
  · exact source_gram_18_13_1
  · exact source_gram_18_13_3
  · exact source_gram_18_13_5
  · exact source_gram_18_13_7
  · exact source_gram_18_13_9
  · exact source_gram_18_13_11
  · exact source_gram_18_13_13
  · exact source_gram_18_13_15
  · exact source_gram_18_13_17
  · exact source_gram_18_15_1
  · exact source_gram_18_15_3
  · exact source_gram_18_15_5
  · exact source_gram_18_15_7
  · exact source_gram_18_15_9
  · exact source_gram_18_15_11
  · exact source_gram_18_15_13
  · exact source_gram_18_15_15
  · exact source_gram_18_15_17
  · exact source_gram_18_17_1
  · exact source_gram_18_17_3
  · exact source_gram_18_17_5
  · exact source_gram_18_17_7
  · exact source_gram_18_17_9
  · exact source_gram_18_17_11
  · exact source_gram_18_17_13
  · exact source_gram_18_17_15
  · exact source_gram_18_17_17

end Laughlin.Certificate

end OAI
