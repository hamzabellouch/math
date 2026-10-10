import OAI.Analysis.Laughlin.FiniteFlux.ComputeGram01Batch17
import OAI.Analysis.Laughlin.FiniteFlux.ComputeGram03Batch17
import OAI.Analysis.Laughlin.FiniteFlux.ComputeGram05Batch17
import OAI.Analysis.Laughlin.FiniteFlux.ComputeGram07Batch17
import OAI.Analysis.Laughlin.FiniteFlux.ComputeGram09Batch17
import OAI.Analysis.Laughlin.FiniteFlux.ComputeGram11Batch17
import OAI.Analysis.Laughlin.FiniteFlux.ComputeGram13Batch17
import OAI.Analysis.Laughlin.FiniteFlux.ComputeGram15Batch17
import OAI.Analysis.Laughlin.FiniteFlux.ComputeGram171717
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0101Batch17
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0103Batch17
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0105Batch17
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0107Batch17
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0109Batch17
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0111Batch17
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0113Batch17
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0115Batch17
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0117Batch17
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0303Batch17
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0305Batch17
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0307Batch17
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0309Batch17
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0311Batch17
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0313Batch17
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0315Batch17
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0317Batch17
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0505Batch17
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0507Batch17
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0509Batch17
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0511Batch17
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0513Batch17
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0515Batch17
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0517Batch17
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0707Batch17
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0709Batch17
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0711Batch17
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0713Batch17
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0715Batch17
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0717Batch17
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0909Batch17
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0911Batch17
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0913Batch17
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0915Batch17
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0917Batch17
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow1111Batch17
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow1113Batch17
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow1115Batch17
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow1117Batch17
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow1313Batch17
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow1315Batch17
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow1317Batch17
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow1515Batch17
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow1517Batch17
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow1717Batch17
import OAI.Analysis.Laughlin.FiniteFlux.Data17
import OAI.Analysis.Laughlin.FourBody.NumericBridge
import OAI.Analysis.Laughlin.FourBody.Symmetry

namespace OAI

namespace Laughlin.Certificate
theorem source_error_17_1_1 : Y 17 1 1 = (-27062893468327394953193285367/419430400000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 17 1 1 0 (by decide),
    source_yRow_eq_rowCompute 17 1 1 1 (by decide),
    source_yRow_eq_rowCompute 17 1 1 2 (by decide),
    source_yRow_eq_rowCompute 17 1 1 3 (by decide),
    source_yRow_eq_rowCompute 17 1 1 4 (by decide),
    source_yRow_eq_rowCompute 17 1 1 5 (by decide),
    source_yRow_eq_rowCompute 17 1 1 6 (by decide),
    computeRow_17_1_1_0, computeRow_17_1_1_1, computeRow_17_1_1_2, computeRow_17_1_1_3, computeRow_17_1_1_4, computeRow_17_1_1_5, computeRow_17_1_1_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_17_1_3 : Y 17 1 3 = (-34150355623889743675914477/104857600000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 17 1 3 0 (by decide),
    source_yRow_eq_rowCompute 17 1 3 1 (by decide),
    source_yRow_eq_rowCompute 17 1 3 2 (by decide),
    source_yRow_eq_rowCompute 17 1 3 3 (by decide),
    source_yRow_eq_rowCompute 17 1 3 4 (by decide),
    source_yRow_eq_rowCompute 17 1 3 5 (by decide),
    source_yRow_eq_rowCompute 17 1 3 6 (by decide),
    computeRow_17_1_3_0, computeRow_17_1_3_1, computeRow_17_1_3_2, computeRow_17_1_3_3, computeRow_17_1_3_4, computeRow_17_1_3_5, computeRow_17_1_3_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_17_1_5 : Y 17 1 5 = (260924265129905899387586721/83886080000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 17 1 5 0 (by decide),
    source_yRow_eq_rowCompute 17 1 5 1 (by decide),
    source_yRow_eq_rowCompute 17 1 5 2 (by decide),
    source_yRow_eq_rowCompute 17 1 5 3 (by decide),
    source_yRow_eq_rowCompute 17 1 5 4 (by decide),
    source_yRow_eq_rowCompute 17 1 5 5 (by decide),
    source_yRow_eq_rowCompute 17 1 5 6 (by decide),
    computeRow_17_1_5_0, computeRow_17_1_5_1, computeRow_17_1_5_2, computeRow_17_1_5_3, computeRow_17_1_5_4, computeRow_17_1_5_5, computeRow_17_1_5_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_17_1_7 : Y 17 1 7 = (-67528457531024325424642053/41943040000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 17 1 7 0 (by decide),
    source_yRow_eq_rowCompute 17 1 7 1 (by decide),
    source_yRow_eq_rowCompute 17 1 7 2 (by decide),
    source_yRow_eq_rowCompute 17 1 7 3 (by decide),
    source_yRow_eq_rowCompute 17 1 7 4 (by decide),
    source_yRow_eq_rowCompute 17 1 7 5 (by decide),
    source_yRow_eq_rowCompute 17 1 7 6 (by decide),
    computeRow_17_1_7_0, computeRow_17_1_7_1, computeRow_17_1_7_2, computeRow_17_1_7_3, computeRow_17_1_7_4, computeRow_17_1_7_5, computeRow_17_1_7_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_17_1_9 : Y 17 1 9 = (-30137637143983305054521403/52428800000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 17 1 9 0 (by decide),
    source_yRow_eq_rowCompute 17 1 9 1 (by decide),
    source_yRow_eq_rowCompute 17 1 9 2 (by decide),
    source_yRow_eq_rowCompute 17 1 9 3 (by decide),
    source_yRow_eq_rowCompute 17 1 9 4 (by decide),
    source_yRow_eq_rowCompute 17 1 9 5 (by decide),
    source_yRow_eq_rowCompute 17 1 9 6 (by decide),
    computeRow_17_1_9_0, computeRow_17_1_9_1, computeRow_17_1_9_2, computeRow_17_1_9_3, computeRow_17_1_9_4, computeRow_17_1_9_5, computeRow_17_1_9_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_17_1_11 : Y 17 1 11 = (95166999960067286140262373/26214400000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 17 1 11 0 (by decide),
    source_yRow_eq_rowCompute 17 1 11 1 (by decide),
    source_yRow_eq_rowCompute 17 1 11 2 (by decide),
    source_yRow_eq_rowCompute 17 1 11 3 (by decide),
    source_yRow_eq_rowCompute 17 1 11 4 (by decide),
    source_yRow_eq_rowCompute 17 1 11 5 (by decide),
    source_yRow_eq_rowCompute 17 1 11 6 (by decide),
    computeRow_17_1_11_0, computeRow_17_1_11_1, computeRow_17_1_11_2, computeRow_17_1_11_3, computeRow_17_1_11_4, computeRow_17_1_11_5, computeRow_17_1_11_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_17_1_13 : Y 17 1 13 = (-175538440354363800262225677/26214400000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 17 1 13 0 (by decide),
    source_yRow_eq_rowCompute 17 1 13 1 (by decide),
    source_yRow_eq_rowCompute 17 1 13 2 (by decide),
    source_yRow_eq_rowCompute 17 1 13 3 (by decide),
    source_yRow_eq_rowCompute 17 1 13 4 (by decide),
    source_yRow_eq_rowCompute 17 1 13 5 (by decide),
    source_yRow_eq_rowCompute 17 1 13 6 (by decide),
    computeRow_17_1_13_0, computeRow_17_1_13_1, computeRow_17_1_13_2, computeRow_17_1_13_3, computeRow_17_1_13_4, computeRow_17_1_13_5, computeRow_17_1_13_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_17_1_15 : Y 17 1 15 = (69154353838247955125781933/2621440000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 17 1 15 0 (by decide),
    source_yRow_eq_rowCompute 17 1 15 1 (by decide),
    source_yRow_eq_rowCompute 17 1 15 2 (by decide),
    source_yRow_eq_rowCompute 17 1 15 3 (by decide),
    source_yRow_eq_rowCompute 17 1 15 4 (by decide),
    source_yRow_eq_rowCompute 17 1 15 5 (by decide),
    source_yRow_eq_rowCompute 17 1 15 6 (by decide),
    computeRow_17_1_15_0, computeRow_17_1_15_1, computeRow_17_1_15_2, computeRow_17_1_15_3, computeRow_17_1_15_4, computeRow_17_1_15_5, computeRow_17_1_15_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_17_1_17 : Y 17 1 17 = (0 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 17 1 17 0 (by decide),
    source_yRow_eq_rowCompute 17 1 17 1 (by decide),
    source_yRow_eq_rowCompute 17 1 17 2 (by decide),
    source_yRow_eq_rowCompute 17 1 17 3 (by decide),
    source_yRow_eq_rowCompute 17 1 17 4 (by decide),
    source_yRow_eq_rowCompute 17 1 17 5 (by decide),
    source_yRow_eq_rowCompute 17 1 17 6 (by decide),
    computeRow_17_1_17_0, computeRow_17_1_17_1, computeRow_17_1_17_2, computeRow_17_1_17_3, computeRow_17_1_17_4, computeRow_17_1_17_5, computeRow_17_1_17_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_17_3_3 : Y 17 3 3 = (-259433233939629173544831711/1048576000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 17 3 3 0 (by decide),
    source_yRow_eq_rowCompute 17 3 3 1 (by decide),
    source_yRow_eq_rowCompute 17 3 3 2 (by decide),
    source_yRow_eq_rowCompute 17 3 3 3 (by decide),
    source_yRow_eq_rowCompute 17 3 3 4 (by decide),
    source_yRow_eq_rowCompute 17 3 3 5 (by decide),
    source_yRow_eq_rowCompute 17 3 3 6 (by decide),
    computeRow_17_3_3_0, computeRow_17_3_3_1, computeRow_17_3_3_2, computeRow_17_3_3_3, computeRow_17_3_3_4, computeRow_17_3_3_5, computeRow_17_3_3_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_17_3_5 : Y 17 3 5 = (10972785710270109216153663/104857600000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 17 3 5 0 (by decide),
    source_yRow_eq_rowCompute 17 3 5 1 (by decide),
    source_yRow_eq_rowCompute 17 3 5 2 (by decide),
    source_yRow_eq_rowCompute 17 3 5 3 (by decide),
    source_yRow_eq_rowCompute 17 3 5 4 (by decide),
    source_yRow_eq_rowCompute 17 3 5 5 (by decide),
    source_yRow_eq_rowCompute 17 3 5 6 (by decide),
    computeRow_17_3_5_0, computeRow_17_3_5_1, computeRow_17_3_5_2, computeRow_17_3_5_3, computeRow_17_3_5_4, computeRow_17_3_5_5, computeRow_17_3_5_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_17_3_7 : Y 17 3 7 = (-408068525315759942414781/13107200000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 17 3 7 0 (by decide),
    source_yRow_eq_rowCompute 17 3 7 1 (by decide),
    source_yRow_eq_rowCompute 17 3 7 2 (by decide),
    source_yRow_eq_rowCompute 17 3 7 3 (by decide),
    source_yRow_eq_rowCompute 17 3 7 4 (by decide),
    source_yRow_eq_rowCompute 17 3 7 5 (by decide),
    source_yRow_eq_rowCompute 17 3 7 6 (by decide),
    computeRow_17_3_7_0, computeRow_17_3_7_1, computeRow_17_3_7_2, computeRow_17_3_7_3, computeRow_17_3_7_4, computeRow_17_3_7_5, computeRow_17_3_7_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_17_3_9 : Y 17 3 9 = (729849806595543331244547/65536000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 17 3 9 0 (by decide),
    source_yRow_eq_rowCompute 17 3 9 1 (by decide),
    source_yRow_eq_rowCompute 17 3 9 2 (by decide),
    source_yRow_eq_rowCompute 17 3 9 3 (by decide),
    source_yRow_eq_rowCompute 17 3 9 4 (by decide),
    source_yRow_eq_rowCompute 17 3 9 5 (by decide),
    source_yRow_eq_rowCompute 17 3 9 6 (by decide),
    computeRow_17_3_9_0, computeRow_17_3_9_1, computeRow_17_3_9_2, computeRow_17_3_9_3, computeRow_17_3_9_4, computeRow_17_3_9_5, computeRow_17_3_9_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_17_3_11 : Y 17 3 11 = (11113201543710491752527/13107200000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 17 3 11 0 (by decide),
    source_yRow_eq_rowCompute 17 3 11 1 (by decide),
    source_yRow_eq_rowCompute 17 3 11 2 (by decide),
    source_yRow_eq_rowCompute 17 3 11 3 (by decide),
    source_yRow_eq_rowCompute 17 3 11 4 (by decide),
    source_yRow_eq_rowCompute 17 3 11 5 (by decide),
    source_yRow_eq_rowCompute 17 3 11 6 (by decide),
    computeRow_17_3_11_0, computeRow_17_3_11_1, computeRow_17_3_11_2, computeRow_17_3_11_3, computeRow_17_3_11_4, computeRow_17_3_11_5, computeRow_17_3_11_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_17_3_13 : Y 17 3 13 = (-12885057439514659527475347/32768000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 17 3 13 0 (by decide),
    source_yRow_eq_rowCompute 17 3 13 1 (by decide),
    source_yRow_eq_rowCompute 17 3 13 2 (by decide),
    source_yRow_eq_rowCompute 17 3 13 3 (by decide),
    source_yRow_eq_rowCompute 17 3 13 4 (by decide),
    source_yRow_eq_rowCompute 17 3 13 5 (by decide),
    source_yRow_eq_rowCompute 17 3 13 6 (by decide),
    computeRow_17_3_13_0, computeRow_17_3_13_1, computeRow_17_3_13_2, computeRow_17_3_13_3, computeRow_17_3_13_4, computeRow_17_3_13_5, computeRow_17_3_13_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_17_3_15 : Y 17 3 15 = (1281998470570534260875331/1638400000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 17 3 15 0 (by decide),
    source_yRow_eq_rowCompute 17 3 15 1 (by decide),
    source_yRow_eq_rowCompute 17 3 15 2 (by decide),
    source_yRow_eq_rowCompute 17 3 15 3 (by decide),
    source_yRow_eq_rowCompute 17 3 15 4 (by decide),
    source_yRow_eq_rowCompute 17 3 15 5 (by decide),
    source_yRow_eq_rowCompute 17 3 15 6 (by decide),
    computeRow_17_3_15_0, computeRow_17_3_15_1, computeRow_17_3_15_2, computeRow_17_3_15_3, computeRow_17_3_15_4, computeRow_17_3_15_5, computeRow_17_3_15_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_17_3_17 : Y 17 3 17 = (0 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 17 3 17 0 (by decide),
    source_yRow_eq_rowCompute 17 3 17 1 (by decide),
    source_yRow_eq_rowCompute 17 3 17 2 (by decide),
    source_yRow_eq_rowCompute 17 3 17 3 (by decide),
    source_yRow_eq_rowCompute 17 3 17 4 (by decide),
    source_yRow_eq_rowCompute 17 3 17 5 (by decide),
    source_yRow_eq_rowCompute 17 3 17 6 (by decide),
    computeRow_17_3_17_0, computeRow_17_3_17_1, computeRow_17_3_17_2, computeRow_17_3_17_3, computeRow_17_3_17_4, computeRow_17_3_17_5, computeRow_17_3_17_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_17_5_5 : Y 17 5 5 = (-16291154585525363835188931/83886080000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 17 5 5 0 (by decide),
    source_yRow_eq_rowCompute 17 5 5 1 (by decide),
    source_yRow_eq_rowCompute 17 5 5 2 (by decide),
    source_yRow_eq_rowCompute 17 5 5 3 (by decide),
    source_yRow_eq_rowCompute 17 5 5 4 (by decide),
    source_yRow_eq_rowCompute 17 5 5 5 (by decide),
    source_yRow_eq_rowCompute 17 5 5 6 (by decide),
    computeRow_17_5_5_0, computeRow_17_5_5_1, computeRow_17_5_5_2, computeRow_17_5_5_3, computeRow_17_5_5_4, computeRow_17_5_5_5, computeRow_17_5_5_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_17_5_7 : Y 17 5 7 = (4351689332062192591003071/41943040000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 17 5 7 0 (by decide),
    source_yRow_eq_rowCompute 17 5 7 1 (by decide),
    source_yRow_eq_rowCompute 17 5 7 2 (by decide),
    source_yRow_eq_rowCompute 17 5 7 3 (by decide),
    source_yRow_eq_rowCompute 17 5 7 4 (by decide),
    source_yRow_eq_rowCompute 17 5 7 5 (by decide),
    source_yRow_eq_rowCompute 17 5 7 6 (by decide),
    computeRow_17_5_7_0, computeRow_17_5_7_1, computeRow_17_5_7_2, computeRow_17_5_7_3, computeRow_17_5_7_4, computeRow_17_5_7_5, computeRow_17_5_7_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_17_5_9 : Y 17 5 9 = (83301302217472013622717/10485760000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 17 5 9 0 (by decide),
    source_yRow_eq_rowCompute 17 5 9 1 (by decide),
    source_yRow_eq_rowCompute 17 5 9 2 (by decide),
    source_yRow_eq_rowCompute 17 5 9 3 (by decide),
    source_yRow_eq_rowCompute 17 5 9 4 (by decide),
    source_yRow_eq_rowCompute 17 5 9 5 (by decide),
    source_yRow_eq_rowCompute 17 5 9 6 (by decide),
    computeRow_17_5_9_0, computeRow_17_5_9_1, computeRow_17_5_9_2, computeRow_17_5_9_3, computeRow_17_5_9_4, computeRow_17_5_9_5, computeRow_17_5_9_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_17_5_11 : Y 17 5 11 = (-203973650747133817508343/1048576000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 17 5 11 0 (by decide),
    source_yRow_eq_rowCompute 17 5 11 1 (by decide),
    source_yRow_eq_rowCompute 17 5 11 2 (by decide),
    source_yRow_eq_rowCompute 17 5 11 3 (by decide),
    source_yRow_eq_rowCompute 17 5 11 4 (by decide),
    source_yRow_eq_rowCompute 17 5 11 5 (by decide),
    source_yRow_eq_rowCompute 17 5 11 6 (by decide),
    computeRow_17_5_11_0, computeRow_17_5_11_1, computeRow_17_5_11_2, computeRow_17_5_11_3, computeRow_17_5_11_4, computeRow_17_5_11_5, computeRow_17_5_11_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_17_5_13 : Y 17 5 13 = (16866893128958580992747463/26214400000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 17 5 13 0 (by decide),
    source_yRow_eq_rowCompute 17 5 13 1 (by decide),
    source_yRow_eq_rowCompute 17 5 13 2 (by decide),
    source_yRow_eq_rowCompute 17 5 13 3 (by decide),
    source_yRow_eq_rowCompute 17 5 13 4 (by decide),
    source_yRow_eq_rowCompute 17 5 13 5 (by decide),
    source_yRow_eq_rowCompute 17 5 13 6 (by decide),
    computeRow_17_5_13_0, computeRow_17_5_13_1, computeRow_17_5_13_2, computeRow_17_5_13_3, computeRow_17_5_13_4, computeRow_17_5_13_5, computeRow_17_5_13_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_17_5_15 : Y 17 5 15 = (-99471136192512553900431/104857600000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 17 5 15 0 (by decide),
    source_yRow_eq_rowCompute 17 5 15 1 (by decide),
    source_yRow_eq_rowCompute 17 5 15 2 (by decide),
    source_yRow_eq_rowCompute 17 5 15 3 (by decide),
    source_yRow_eq_rowCompute 17 5 15 4 (by decide),
    source_yRow_eq_rowCompute 17 5 15 5 (by decide),
    source_yRow_eq_rowCompute 17 5 15 6 (by decide),
    computeRow_17_5_15_0, computeRow_17_5_15_1, computeRow_17_5_15_2, computeRow_17_5_15_3, computeRow_17_5_15_4, computeRow_17_5_15_5, computeRow_17_5_15_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_17_5_17 : Y 17 5 17 = (0 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 17 5 17 0 (by decide),
    source_yRow_eq_rowCompute 17 5 17 1 (by decide),
    source_yRow_eq_rowCompute 17 5 17 2 (by decide),
    source_yRow_eq_rowCompute 17 5 17 3 (by decide),
    source_yRow_eq_rowCompute 17 5 17 4 (by decide),
    source_yRow_eq_rowCompute 17 5 17 5 (by decide),
    source_yRow_eq_rowCompute 17 5 17 6 (by decide),
    computeRow_17_5_17_0, computeRow_17_5_17_1, computeRow_17_5_17_2, computeRow_17_5_17_3, computeRow_17_5_17_4, computeRow_17_5_17_5, computeRow_17_5_17_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_17_7_7 : Y 17 7 7 = (-1404556469174930860536363/20971520000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 17 7 7 0 (by decide),
    source_yRow_eq_rowCompute 17 7 7 1 (by decide),
    source_yRow_eq_rowCompute 17 7 7 2 (by decide),
    source_yRow_eq_rowCompute 17 7 7 3 (by decide),
    source_yRow_eq_rowCompute 17 7 7 4 (by decide),
    source_yRow_eq_rowCompute 17 7 7 5 (by decide),
    source_yRow_eq_rowCompute 17 7 7 6 (by decide),
    computeRow_17_7_7_0, computeRow_17_7_7_1, computeRow_17_7_7_2, computeRow_17_7_7_3, computeRow_17_7_7_4, computeRow_17_7_7_5, computeRow_17_7_7_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_17_7_9 : Y 17 7 9 = (138574461584170298662731/26214400000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 17 7 9 0 (by decide),
    source_yRow_eq_rowCompute 17 7 9 1 (by decide),
    source_yRow_eq_rowCompute 17 7 9 2 (by decide),
    source_yRow_eq_rowCompute 17 7 9 3 (by decide),
    source_yRow_eq_rowCompute 17 7 9 4 (by decide),
    source_yRow_eq_rowCompute 17 7 9 5 (by decide),
    source_yRow_eq_rowCompute 17 7 9 6 (by decide),
    computeRow_17_7_9_0, computeRow_17_7_9_1, computeRow_17_7_9_2, computeRow_17_7_9_3, computeRow_17_7_9_4, computeRow_17_7_9_5, computeRow_17_7_9_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_17_7_11 : Y 17 7 11 = (322312699672503215100579/2621440000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 17 7 11 0 (by decide),
    source_yRow_eq_rowCompute 17 7 11 1 (by decide),
    source_yRow_eq_rowCompute 17 7 11 2 (by decide),
    source_yRow_eq_rowCompute 17 7 11 3 (by decide),
    source_yRow_eq_rowCompute 17 7 11 4 (by decide),
    source_yRow_eq_rowCompute 17 7 11 5 (by decide),
    source_yRow_eq_rowCompute 17 7 11 6 (by decide),
    computeRow_17_7_11_0, computeRow_17_7_11_1, computeRow_17_7_11_2, computeRow_17_7_11_3, computeRow_17_7_11_4, computeRow_17_7_11_5, computeRow_17_7_11_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_17_7_13 : Y 17 7 13 = (-5414374042135146758937267/13107200000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 17 7 13 0 (by decide),
    source_yRow_eq_rowCompute 17 7 13 1 (by decide),
    source_yRow_eq_rowCompute 17 7 13 2 (by decide),
    source_yRow_eq_rowCompute 17 7 13 3 (by decide),
    source_yRow_eq_rowCompute 17 7 13 4 (by decide),
    source_yRow_eq_rowCompute 17 7 13 5 (by decide),
    source_yRow_eq_rowCompute 17 7 13 6 (by decide),
    computeRow_17_7_13_0, computeRow_17_7_13_1, computeRow_17_7_13_2, computeRow_17_7_13_3, computeRow_17_7_13_4, computeRow_17_7_13_5, computeRow_17_7_13_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_17_7_15 : Y 17 7 15 = (53455862611083189243987/1310720000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 17 7 15 0 (by decide),
    source_yRow_eq_rowCompute 17 7 15 1 (by decide),
    source_yRow_eq_rowCompute 17 7 15 2 (by decide),
    source_yRow_eq_rowCompute 17 7 15 3 (by decide),
    source_yRow_eq_rowCompute 17 7 15 4 (by decide),
    source_yRow_eq_rowCompute 17 7 15 5 (by decide),
    source_yRow_eq_rowCompute 17 7 15 6 (by decide),
    computeRow_17_7_15_0, computeRow_17_7_15_1, computeRow_17_7_15_2, computeRow_17_7_15_3, computeRow_17_7_15_4, computeRow_17_7_15_5, computeRow_17_7_15_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_17_7_17 : Y 17 7 17 = (0 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 17 7 17 0 (by decide),
    source_yRow_eq_rowCompute 17 7 17 1 (by decide),
    source_yRow_eq_rowCompute 17 7 17 2 (by decide),
    source_yRow_eq_rowCompute 17 7 17 3 (by decide),
    source_yRow_eq_rowCompute 17 7 17 4 (by decide),
    source_yRow_eq_rowCompute 17 7 17 5 (by decide),
    source_yRow_eq_rowCompute 17 7 17 6 (by decide),
    computeRow_17_7_17_0, computeRow_17_7_17_1, computeRow_17_7_17_2, computeRow_17_7_17_3, computeRow_17_7_17_4, computeRow_17_7_17_5, computeRow_17_7_17_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_17_9_9 : Y 17 9 9 = (-560195899211802719046699/32768000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 17 9 9 0 (by decide),
    source_yRow_eq_rowCompute 17 9 9 1 (by decide),
    source_yRow_eq_rowCompute 17 9 9 2 (by decide),
    source_yRow_eq_rowCompute 17 9 9 3 (by decide),
    source_yRow_eq_rowCompute 17 9 9 4 (by decide),
    source_yRow_eq_rowCompute 17 9 9 5 (by decide),
    source_yRow_eq_rowCompute 17 9 9 6 (by decide),
    computeRow_17_9_9_0, computeRow_17_9_9_1, computeRow_17_9_9_2, computeRow_17_9_9_3, computeRow_17_9_9_4, computeRow_17_9_9_5, computeRow_17_9_9_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_17_9_11 : Y 17 9 11 = (1543576781120216089401/131072000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 17 9 11 0 (by decide),
    source_yRow_eq_rowCompute 17 9 11 1 (by decide),
    source_yRow_eq_rowCompute 17 9 11 2 (by decide),
    source_yRow_eq_rowCompute 17 9 11 3 (by decide),
    source_yRow_eq_rowCompute 17 9 11 4 (by decide),
    source_yRow_eq_rowCompute 17 9 11 5 (by decide),
    source_yRow_eq_rowCompute 17 9 11 6 (by decide),
    computeRow_17_9_11_0, computeRow_17_9_11_1, computeRow_17_9_11_2, computeRow_17_9_11_3, computeRow_17_9_11_4, computeRow_17_9_11_5, computeRow_17_9_11_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_17_9_13 : Y 17 9 13 = (727025046163822366323363/16384000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 17 9 13 0 (by decide),
    source_yRow_eq_rowCompute 17 9 13 1 (by decide),
    source_yRow_eq_rowCompute 17 9 13 2 (by decide),
    source_yRow_eq_rowCompute 17 9 13 3 (by decide),
    source_yRow_eq_rowCompute 17 9 13 4 (by decide),
    source_yRow_eq_rowCompute 17 9 13 5 (by decide),
    source_yRow_eq_rowCompute 17 9 13 6 (by decide),
    computeRow_17_9_13_0, computeRow_17_9_13_1, computeRow_17_9_13_2, computeRow_17_9_13_3, computeRow_17_9_13_4, computeRow_17_9_13_5, computeRow_17_9_13_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_17_9_15 : Y 17 9 15 = (948970636189602992298333/1638400000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 17 9 15 0 (by decide),
    source_yRow_eq_rowCompute 17 9 15 1 (by decide),
    source_yRow_eq_rowCompute 17 9 15 2 (by decide),
    source_yRow_eq_rowCompute 17 9 15 3 (by decide),
    source_yRow_eq_rowCompute 17 9 15 4 (by decide),
    source_yRow_eq_rowCompute 17 9 15 5 (by decide),
    source_yRow_eq_rowCompute 17 9 15 6 (by decide),
    computeRow_17_9_15_0, computeRow_17_9_15_1, computeRow_17_9_15_2, computeRow_17_9_15_3, computeRow_17_9_15_4, computeRow_17_9_15_5, computeRow_17_9_15_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_17_9_17 : Y 17 9 17 = (0 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 17 9 17 0 (by decide),
    source_yRow_eq_rowCompute 17 9 17 1 (by decide),
    source_yRow_eq_rowCompute 17 9 17 2 (by decide),
    source_yRow_eq_rowCompute 17 9 17 3 (by decide),
    source_yRow_eq_rowCompute 17 9 17 4 (by decide),
    source_yRow_eq_rowCompute 17 9 17 5 (by decide),
    source_yRow_eq_rowCompute 17 9 17 6 (by decide),
    computeRow_17_9_17_0, computeRow_17_9_17_1, computeRow_17_9_17_2, computeRow_17_9_17_3, computeRow_17_9_17_4, computeRow_17_9_17_5, computeRow_17_9_17_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_17_11_11 : Y 17 11 11 = (-428477431290639456169917/1638400000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 17 11 11 0 (by decide),
    source_yRow_eq_rowCompute 17 11 11 1 (by decide),
    source_yRow_eq_rowCompute 17 11 11 2 (by decide),
    source_yRow_eq_rowCompute 17 11 11 3 (by decide),
    source_yRow_eq_rowCompute 17 11 11 4 (by decide),
    source_yRow_eq_rowCompute 17 11 11 5 (by decide),
    source_yRow_eq_rowCompute 17 11 11 6 (by decide),
    computeRow_17_11_11_0, computeRow_17_11_11_1, computeRow_17_11_11_2, computeRow_17_11_11_3, computeRow_17_11_11_4, computeRow_17_11_11_5, computeRow_17_11_11_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_17_11_13 : Y 17 11 13 = (1054078060656605687920503/1638400000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 17 11 13 0 (by decide),
    source_yRow_eq_rowCompute 17 11 13 1 (by decide),
    source_yRow_eq_rowCompute 17 11 13 2 (by decide),
    source_yRow_eq_rowCompute 17 11 13 3 (by decide),
    source_yRow_eq_rowCompute 17 11 13 4 (by decide),
    source_yRow_eq_rowCompute 17 11 13 5 (by decide),
    source_yRow_eq_rowCompute 17 11 13 6 (by decide),
    computeRow_17_11_13_0, computeRow_17_11_13_1, computeRow_17_11_13_2, computeRow_17_11_13_3, computeRow_17_11_13_4, computeRow_17_11_13_5, computeRow_17_11_13_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_17_11_15 : Y 17 11 15 = (-99701519947816820212179/163840000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 17 11 15 0 (by decide),
    source_yRow_eq_rowCompute 17 11 15 1 (by decide),
    source_yRow_eq_rowCompute 17 11 15 2 (by decide),
    source_yRow_eq_rowCompute 17 11 15 3 (by decide),
    source_yRow_eq_rowCompute 17 11 15 4 (by decide),
    source_yRow_eq_rowCompute 17 11 15 5 (by decide),
    source_yRow_eq_rowCompute 17 11 15 6 (by decide),
    computeRow_17_11_15_0, computeRow_17_11_15_1, computeRow_17_11_15_2, computeRow_17_11_15_3, computeRow_17_11_15_4, computeRow_17_11_15_5, computeRow_17_11_15_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_17_11_17 : Y 17 11 17 = (0 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 17 11 17 0 (by decide),
    source_yRow_eq_rowCompute 17 11 17 1 (by decide),
    source_yRow_eq_rowCompute 17 11 17 2 (by decide),
    source_yRow_eq_rowCompute 17 11 17 3 (by decide),
    source_yRow_eq_rowCompute 17 11 17 4 (by decide),
    source_yRow_eq_rowCompute 17 11 17 5 (by decide),
    source_yRow_eq_rowCompute 17 11 17 6 (by decide),
    computeRow_17_11_17_0, computeRow_17_11_17_1, computeRow_17_11_17_2, computeRow_17_11_17_3, computeRow_17_11_17_4, computeRow_17_11_17_5, computeRow_17_11_17_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_17_13_13 : Y 17 13 13 = (-13417206537411611280214011/8192000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 17 13 13 0 (by decide),
    source_yRow_eq_rowCompute 17 13 13 1 (by decide),
    source_yRow_eq_rowCompute 17 13 13 2 (by decide),
    source_yRow_eq_rowCompute 17 13 13 3 (by decide),
    source_yRow_eq_rowCompute 17 13 13 4 (by decide),
    source_yRow_eq_rowCompute 17 13 13 5 (by decide),
    source_yRow_eq_rowCompute 17 13 13 6 (by decide),
    computeRow_17_13_13_0, computeRow_17_13_13_1, computeRow_17_13_13_2, computeRow_17_13_13_3, computeRow_17_13_13_4, computeRow_17_13_13_5, computeRow_17_13_13_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_17_13_15 : Y 17 13 15 = (797255391734832796032267/819200000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 17 13 15 0 (by decide),
    source_yRow_eq_rowCompute 17 13 15 1 (by decide),
    source_yRow_eq_rowCompute 17 13 15 2 (by decide),
    source_yRow_eq_rowCompute 17 13 15 3 (by decide),
    source_yRow_eq_rowCompute 17 13 15 4 (by decide),
    source_yRow_eq_rowCompute 17 13 15 5 (by decide),
    source_yRow_eq_rowCompute 17 13 15 6 (by decide),
    computeRow_17_13_15_0, computeRow_17_13_15_1, computeRow_17_13_15_2, computeRow_17_13_15_3, computeRow_17_13_15_4, computeRow_17_13_15_5, computeRow_17_13_15_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_17_13_17 : Y 17 13 17 = (0 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 17 13 17 0 (by decide),
    source_yRow_eq_rowCompute 17 13 17 1 (by decide),
    source_yRow_eq_rowCompute 17 13 17 2 (by decide),
    source_yRow_eq_rowCompute 17 13 17 3 (by decide),
    source_yRow_eq_rowCompute 17 13 17 4 (by decide),
    source_yRow_eq_rowCompute 17 13 17 5 (by decide),
    source_yRow_eq_rowCompute 17 13 17 6 (by decide),
    computeRow_17_13_17_0, computeRow_17_13_17_1, computeRow_17_13_17_2, computeRow_17_13_17_3, computeRow_17_13_17_4, computeRow_17_13_17_5, computeRow_17_13_17_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_17_15_15 : Y 17 15 15 = (-2081041110780259193873307/81920000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 17 15 15 0 (by decide),
    source_yRow_eq_rowCompute 17 15 15 1 (by decide),
    source_yRow_eq_rowCompute 17 15 15 2 (by decide),
    source_yRow_eq_rowCompute 17 15 15 3 (by decide),
    source_yRow_eq_rowCompute 17 15 15 4 (by decide),
    source_yRow_eq_rowCompute 17 15 15 5 (by decide),
    source_yRow_eq_rowCompute 17 15 15 6 (by decide),
    computeRow_17_15_15_0, computeRow_17_15_15_1, computeRow_17_15_15_2, computeRow_17_15_15_3, computeRow_17_15_15_4, computeRow_17_15_15_5, computeRow_17_15_15_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_17_15_17 : Y 17 15 17 = (0 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 17 15 17 0 (by decide),
    source_yRow_eq_rowCompute 17 15 17 1 (by decide),
    source_yRow_eq_rowCompute 17 15 17 2 (by decide),
    source_yRow_eq_rowCompute 17 15 17 3 (by decide),
    source_yRow_eq_rowCompute 17 15 17 4 (by decide),
    source_yRow_eq_rowCompute 17 15 17 5 (by decide),
    source_yRow_eq_rowCompute 17 15 17 6 (by decide),
    computeRow_17_15_17_0, computeRow_17_15_17_1, computeRow_17_15_17_2, computeRow_17_15_17_3, computeRow_17_15_17_4, computeRow_17_15_17_5, computeRow_17_15_17_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_17_17_17 : Y 17 17 17 = (0 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 17 17 17 0 (by decide),
    source_yRow_eq_rowCompute 17 17 17 1 (by decide),
    source_yRow_eq_rowCompute 17 17 17 2 (by decide),
    source_yRow_eq_rowCompute 17 17 17 3 (by decide),
    source_yRow_eq_rowCompute 17 17 17 4 (by decide),
    source_yRow_eq_rowCompute 17 17 17 5 (by decide),
    source_yRow_eq_rowCompute 17 17 17 6 (by decide),
    computeRow_17_17_17_0, computeRow_17_17_17_1, computeRow_17_17_17_2, computeRow_17_17_17_3, computeRow_17_17_17_4, computeRow_17_17_17_5, computeRow_17_17_17_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_gram_17_1_1 : Z 17 1 1 = (41845579776000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_17_1_1

theorem source_gram_17_1_3 : Z 17 1 3 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_17_1_3

theorem source_gram_17_1_5 : Z 17 1 5 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_17_1_5

theorem source_gram_17_1_7 : Z 17 1 7 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_17_1_7

theorem source_gram_17_1_9 : Z 17 1 9 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_17_1_9

theorem source_gram_17_1_11 : Z 17 1 11 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_17_1_11

theorem source_gram_17_1_13 : Z 17 1 13 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_17_1_13

theorem source_gram_17_1_15 : Z 17 1 15 = (-326918592000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_17_1_15

theorem source_gram_17_1_17 : Z 17 1 17 = (19451656224000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_17_1_17

theorem source_gram_17_3_3 : Z 17 3 3 = (523069747200 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_17_3_3

theorem source_gram_17_3_5 : Z 17 3 5 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_17_3_5

theorem source_gram_17_3_7 : Z 17 3 7 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_17_3_7

theorem source_gram_17_3_9 : Z 17 3 9 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_17_3_9

theorem source_gram_17_3_11 : Z 17 3 11 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_17_3_11

theorem source_gram_17_3_13 : Z 17 3 13 = (-16345929600 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_17_3_13

theorem source_gram_17_3_15 : Z 17 3 15 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_17_3_15

theorem source_gram_17_3_17 : Z 17 3 17 = (6947020080000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_17_3_17

theorem source_gram_17_5_5 : Z 17 5 5 = (57480192000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_17_5_5

theorem source_gram_17_5_7 : Z 17 5 7 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_17_5_7

theorem source_gram_17_5_9 : Z 17 5 9 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_17_5_9

theorem source_gram_17_5_11 : Z 17 5 11 = (-2694384000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_17_5_11

theorem source_gram_17_5_13 : Z 17 5 13 = (-29189160000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_17_5_13

theorem source_gram_17_5_15 : Z 17 5 15 = (204324120000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_17_5_15

theorem source_gram_17_5_17 : Z 17 5 17 = (2084106024000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_17_5_17

theorem source_gram_17_7_7 : Z 17 7 7 = (18289152000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_17_7_7

theorem source_gram_17_7_9 : Z 17 7 9 = (-1143072000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_17_7_9

theorem source_gram_17_7_11 : Z 17 7 11 = (-12573792000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_17_7_11

theorem source_gram_17_7_13 : Z 17 7 13 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_17_7_13

theorem source_gram_17_7_15 : Z 17 7 15 = (143026884000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_17_7_15

theorem source_gram_17_7_17 : Z 17 7 17 = (347351004000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_17_7_17

theorem source_gram_17_9_9 : Z 17 9 9 = (5372438400 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_17_9_9

theorem source_gram_17_9_11 : Z 17 9 11 = (-9430344000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_17_9_11

theorem source_gram_17_9_13 : Z 17 9 13 = (12259447200 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_17_9_13

theorem source_gram_17_9_15 : Z 17 9 15 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_17_9_15

theorem source_gram_17_9_17 : Z 17 9 17 = (-173675502000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_17_9_17

theorem source_gram_17_11_11 : Z 17 11 11 = (28740096000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_17_11_11

theorem source_gram_17_11_13 : Z 17 11 13 = (-24081057000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_17_11_13

theorem source_gram_17_11_15 : Z 17 11 15 = (-112378266000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_17_11_15

theorem source_gram_17_11_17 : Z 17 11 17 = (-260513253000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_17_11_17

theorem source_gram_17_13_13 : Z 17 13 13 = (55532376900 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_17_13_13

theorem source_gram_17_13_15 : Z 17 13 15 = (-166013347500 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_17_13_15

theorem source_gram_17_13_17 : Z 17 13 17 = (-217094377500 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_17_13_17

theorem source_gram_17_15_15 : Z 17 15 15 = (2442950259750 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_17_15_15

theorem source_gram_17_15_17 : Z 17 15 17 = (-151966064250 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_17_15_17

theorem source_gram_17_17_17 : Z 17 17 17 = (355589735626125 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_17_17_17

theorem source_error_17_3_1 : Y 17 3 1 = (-34150355623889743675914477/104857600000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_17_1_3

theorem source_gram_17_3_1 : Z 17 3 1 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_17_1_3

theorem source_error_17_5_1 : Y 17 5 1 = (260924265129905899387586721/83886080000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_17_1_5

theorem source_gram_17_5_1 : Z 17 5 1 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_17_1_5

theorem source_error_17_5_3 : Y 17 5 3 = (10972785710270109216153663/104857600000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_17_3_5

theorem source_gram_17_5_3 : Z 17 5 3 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_17_3_5

theorem source_error_17_7_1 : Y 17 7 1 = (-67528457531024325424642053/41943040000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_17_1_7

theorem source_gram_17_7_1 : Z 17 7 1 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_17_1_7

theorem source_error_17_7_3 : Y 17 7 3 = (-408068525315759942414781/13107200000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_17_3_7

theorem source_gram_17_7_3 : Z 17 7 3 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_17_3_7

theorem source_error_17_7_5 : Y 17 7 5 = (4351689332062192591003071/41943040000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_17_5_7

theorem source_gram_17_7_5 : Z 17 7 5 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_17_5_7

theorem source_error_17_9_1 : Y 17 9 1 = (-30137637143983305054521403/52428800000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_17_1_9

theorem source_gram_17_9_1 : Z 17 9 1 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_17_1_9

theorem source_error_17_9_3 : Y 17 9 3 = (729849806595543331244547/65536000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_17_3_9

theorem source_gram_17_9_3 : Z 17 9 3 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_17_3_9

theorem source_error_17_9_5 : Y 17 9 5 = (83301302217472013622717/10485760000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_17_5_9

theorem source_gram_17_9_5 : Z 17 9 5 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_17_5_9

theorem source_error_17_9_7 : Y 17 9 7 = (138574461584170298662731/26214400000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_17_7_9

theorem source_gram_17_9_7 : Z 17 9 7 = (-1143072000 : ℚ) := by
  rw [Z_symm]
  exact source_gram_17_7_9

theorem source_error_17_11_1 : Y 17 11 1 = (95166999960067286140262373/26214400000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_17_1_11

theorem source_gram_17_11_1 : Z 17 11 1 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_17_1_11

theorem source_error_17_11_3 : Y 17 11 3 = (11113201543710491752527/13107200000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_17_3_11

theorem source_gram_17_11_3 : Z 17 11 3 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_17_3_11

theorem source_error_17_11_5 : Y 17 11 5 = (-203973650747133817508343/1048576000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_17_5_11

theorem source_gram_17_11_5 : Z 17 11 5 = (-2694384000 : ℚ) := by
  rw [Z_symm]
  exact source_gram_17_5_11

theorem source_error_17_11_7 : Y 17 11 7 = (322312699672503215100579/2621440000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_17_7_11

theorem source_gram_17_11_7 : Z 17 11 7 = (-12573792000 : ℚ) := by
  rw [Z_symm]
  exact source_gram_17_7_11

theorem source_error_17_11_9 : Y 17 11 9 = (1543576781120216089401/131072000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_17_9_11

theorem source_gram_17_11_9 : Z 17 11 9 = (-9430344000 : ℚ) := by
  rw [Z_symm]
  exact source_gram_17_9_11

theorem source_error_17_13_1 : Y 17 13 1 = (-175538440354363800262225677/26214400000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_17_1_13

theorem source_gram_17_13_1 : Z 17 13 1 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_17_1_13

theorem source_error_17_13_3 : Y 17 13 3 = (-12885057439514659527475347/32768000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_17_3_13

theorem source_gram_17_13_3 : Z 17 13 3 = (-16345929600 : ℚ) := by
  rw [Z_symm]
  exact source_gram_17_3_13

theorem source_error_17_13_5 : Y 17 13 5 = (16866893128958580992747463/26214400000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_17_5_13

theorem source_gram_17_13_5 : Z 17 13 5 = (-29189160000 : ℚ) := by
  rw [Z_symm]
  exact source_gram_17_5_13

theorem source_error_17_13_7 : Y 17 13 7 = (-5414374042135146758937267/13107200000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_17_7_13

theorem source_gram_17_13_7 : Z 17 13 7 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_17_7_13

theorem source_error_17_13_9 : Y 17 13 9 = (727025046163822366323363/16384000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_17_9_13

theorem source_gram_17_13_9 : Z 17 13 9 = (12259447200 : ℚ) := by
  rw [Z_symm]
  exact source_gram_17_9_13

theorem source_error_17_13_11 : Y 17 13 11 = (1054078060656605687920503/1638400000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_17_11_13

theorem source_gram_17_13_11 : Z 17 13 11 = (-24081057000 : ℚ) := by
  rw [Z_symm]
  exact source_gram_17_11_13

theorem source_error_17_15_1 : Y 17 15 1 = (69154353838247955125781933/2621440000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_17_1_15

theorem source_gram_17_15_1 : Z 17 15 1 = (-326918592000 : ℚ) := by
  rw [Z_symm]
  exact source_gram_17_1_15

theorem source_error_17_15_3 : Y 17 15 3 = (1281998470570534260875331/1638400000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_17_3_15

theorem source_gram_17_15_3 : Z 17 15 3 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_17_3_15

theorem source_error_17_15_5 : Y 17 15 5 = (-99471136192512553900431/104857600000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_17_5_15

theorem source_gram_17_15_5 : Z 17 15 5 = (204324120000 : ℚ) := by
  rw [Z_symm]
  exact source_gram_17_5_15

theorem source_error_17_15_7 : Y 17 15 7 = (53455862611083189243987/1310720000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_17_7_15

theorem source_gram_17_15_7 : Z 17 15 7 = (143026884000 : ℚ) := by
  rw [Z_symm]
  exact source_gram_17_7_15

theorem source_error_17_15_9 : Y 17 15 9 = (948970636189602992298333/1638400000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_17_9_15

theorem source_gram_17_15_9 : Z 17 15 9 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_17_9_15

theorem source_error_17_15_11 : Y 17 15 11 = (-99701519947816820212179/163840000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_17_11_15

theorem source_gram_17_15_11 : Z 17 15 11 = (-112378266000 : ℚ) := by
  rw [Z_symm]
  exact source_gram_17_11_15

theorem source_error_17_15_13 : Y 17 15 13 = (797255391734832796032267/819200000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_17_13_15

theorem source_gram_17_15_13 : Z 17 15 13 = (-166013347500 : ℚ) := by
  rw [Z_symm]
  exact source_gram_17_13_15

theorem source_error_17_17_1 : Y 17 17 1 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_17_1_17

theorem source_gram_17_17_1 : Z 17 17 1 = (19451656224000 : ℚ) := by
  rw [Z_symm]
  exact source_gram_17_1_17

theorem source_error_17_17_3 : Y 17 17 3 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_17_3_17

theorem source_gram_17_17_3 : Z 17 17 3 = (6947020080000 : ℚ) := by
  rw [Z_symm]
  exact source_gram_17_3_17

theorem source_error_17_17_5 : Y 17 17 5 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_17_5_17

theorem source_gram_17_17_5 : Z 17 17 5 = (2084106024000 : ℚ) := by
  rw [Z_symm]
  exact source_gram_17_5_17

theorem source_error_17_17_7 : Y 17 17 7 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_17_7_17

theorem source_gram_17_17_7 : Z 17 17 7 = (347351004000 : ℚ) := by
  rw [Z_symm]
  exact source_gram_17_7_17

theorem source_error_17_17_9 : Y 17 17 9 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_17_9_17

theorem source_gram_17_17_9 : Z 17 17 9 = (-173675502000 : ℚ) := by
  rw [Z_symm]
  exact source_gram_17_9_17

theorem source_error_17_17_11 : Y 17 17 11 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_17_11_17

theorem source_gram_17_17_11 : Z 17 17 11 = (-260513253000 : ℚ) := by
  rw [Z_symm]
  exact source_gram_17_11_17

theorem source_error_17_17_13 : Y 17 17 13 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_17_13_17

theorem source_gram_17_17_13 : Z 17 17 13 = (-217094377500 : ℚ) := by
  rw [Z_symm]
  exact source_gram_17_13_17

theorem source_error_17_17_15 : Y 17 17 15 = (0 : ℚ) := by
  rw [Y_symm]
  exact source_error_17_15_17

theorem source_gram_17_17_15 : Z 17 17 15 = (-151966064250 : ℚ) := by
  rw [Z_symm]
  exact source_gram_17_15_17

theorem error_17 : errorRational 17 = candidateY_17 := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact source_error_17_1_1
  · exact source_error_17_1_3
  · exact source_error_17_1_5
  · exact source_error_17_1_7
  · exact source_error_17_1_9
  · exact source_error_17_1_11
  · exact source_error_17_1_13
  · exact source_error_17_1_15
  · exact source_error_17_1_17
  · exact source_error_17_3_1
  · exact source_error_17_3_3
  · exact source_error_17_3_5
  · exact source_error_17_3_7
  · exact source_error_17_3_9
  · exact source_error_17_3_11
  · exact source_error_17_3_13
  · exact source_error_17_3_15
  · exact source_error_17_3_17
  · exact source_error_17_5_1
  · exact source_error_17_5_3
  · exact source_error_17_5_5
  · exact source_error_17_5_7
  · exact source_error_17_5_9
  · exact source_error_17_5_11
  · exact source_error_17_5_13
  · exact source_error_17_5_15
  · exact source_error_17_5_17
  · exact source_error_17_7_1
  · exact source_error_17_7_3
  · exact source_error_17_7_5
  · exact source_error_17_7_7
  · exact source_error_17_7_9
  · exact source_error_17_7_11
  · exact source_error_17_7_13
  · exact source_error_17_7_15
  · exact source_error_17_7_17
  · exact source_error_17_9_1
  · exact source_error_17_9_3
  · exact source_error_17_9_5
  · exact source_error_17_9_7
  · exact source_error_17_9_9
  · exact source_error_17_9_11
  · exact source_error_17_9_13
  · exact source_error_17_9_15
  · exact source_error_17_9_17
  · exact source_error_17_11_1
  · exact source_error_17_11_3
  · exact source_error_17_11_5
  · exact source_error_17_11_7
  · exact source_error_17_11_9
  · exact source_error_17_11_11
  · exact source_error_17_11_13
  · exact source_error_17_11_15
  · exact source_error_17_11_17
  · exact source_error_17_13_1
  · exact source_error_17_13_3
  · exact source_error_17_13_5
  · exact source_error_17_13_7
  · exact source_error_17_13_9
  · exact source_error_17_13_11
  · exact source_error_17_13_13
  · exact source_error_17_13_15
  · exact source_error_17_13_17
  · exact source_error_17_15_1
  · exact source_error_17_15_3
  · exact source_error_17_15_5
  · exact source_error_17_15_7
  · exact source_error_17_15_9
  · exact source_error_17_15_11
  · exact source_error_17_15_13
  · exact source_error_17_15_15
  · exact source_error_17_15_17
  · exact source_error_17_17_1
  · exact source_error_17_17_3
  · exact source_error_17_17_5
  · exact source_error_17_17_7
  · exact source_error_17_17_9
  · exact source_error_17_17_11
  · exact source_error_17_17_13
  · exact source_error_17_17_15
  · exact source_error_17_17_17

theorem gram_17 : gramRational 17 = candidateZ_17 := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact source_gram_17_1_1
  · exact source_gram_17_1_3
  · exact source_gram_17_1_5
  · exact source_gram_17_1_7
  · exact source_gram_17_1_9
  · exact source_gram_17_1_11
  · exact source_gram_17_1_13
  · exact source_gram_17_1_15
  · exact source_gram_17_1_17
  · exact source_gram_17_3_1
  · exact source_gram_17_3_3
  · exact source_gram_17_3_5
  · exact source_gram_17_3_7
  · exact source_gram_17_3_9
  · exact source_gram_17_3_11
  · exact source_gram_17_3_13
  · exact source_gram_17_3_15
  · exact source_gram_17_3_17
  · exact source_gram_17_5_1
  · exact source_gram_17_5_3
  · exact source_gram_17_5_5
  · exact source_gram_17_5_7
  · exact source_gram_17_5_9
  · exact source_gram_17_5_11
  · exact source_gram_17_5_13
  · exact source_gram_17_5_15
  · exact source_gram_17_5_17
  · exact source_gram_17_7_1
  · exact source_gram_17_7_3
  · exact source_gram_17_7_5
  · exact source_gram_17_7_7
  · exact source_gram_17_7_9
  · exact source_gram_17_7_11
  · exact source_gram_17_7_13
  · exact source_gram_17_7_15
  · exact source_gram_17_7_17
  · exact source_gram_17_9_1
  · exact source_gram_17_9_3
  · exact source_gram_17_9_5
  · exact source_gram_17_9_7
  · exact source_gram_17_9_9
  · exact source_gram_17_9_11
  · exact source_gram_17_9_13
  · exact source_gram_17_9_15
  · exact source_gram_17_9_17
  · exact source_gram_17_11_1
  · exact source_gram_17_11_3
  · exact source_gram_17_11_5
  · exact source_gram_17_11_7
  · exact source_gram_17_11_9
  · exact source_gram_17_11_11
  · exact source_gram_17_11_13
  · exact source_gram_17_11_15
  · exact source_gram_17_11_17
  · exact source_gram_17_13_1
  · exact source_gram_17_13_3
  · exact source_gram_17_13_5
  · exact source_gram_17_13_7
  · exact source_gram_17_13_9
  · exact source_gram_17_13_11
  · exact source_gram_17_13_13
  · exact source_gram_17_13_15
  · exact source_gram_17_13_17
  · exact source_gram_17_15_1
  · exact source_gram_17_15_3
  · exact source_gram_17_15_5
  · exact source_gram_17_15_7
  · exact source_gram_17_15_9
  · exact source_gram_17_15_11
  · exact source_gram_17_15_13
  · exact source_gram_17_15_15
  · exact source_gram_17_15_17
  · exact source_gram_17_17_1
  · exact source_gram_17_17_3
  · exact source_gram_17_17_5
  · exact source_gram_17_17_7
  · exact source_gram_17_17_9
  · exact source_gram_17_17_11
  · exact source_gram_17_17_13
  · exact source_gram_17_17_15
  · exact source_gram_17_17_17

end Laughlin.Certificate

end OAI
