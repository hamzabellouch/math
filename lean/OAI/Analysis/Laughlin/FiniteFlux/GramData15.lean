import OAI.Analysis.Laughlin.FiniteFlux.ComputeGram01Batch15
import OAI.Analysis.Laughlin.FiniteFlux.ComputeGram03Batch15
import OAI.Analysis.Laughlin.FiniteFlux.ComputeGram05Batch15
import OAI.Analysis.Laughlin.FiniteFlux.ComputeGram07Batch15
import OAI.Analysis.Laughlin.FiniteFlux.ComputeGram09Batch15
import OAI.Analysis.Laughlin.FiniteFlux.ComputeGram11Batch15
import OAI.Analysis.Laughlin.FiniteFlux.ComputeGram13Batch15
import OAI.Analysis.Laughlin.FiniteFlux.ComputeGram151515
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0101Batch15
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0103Batch15
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0105Batch15
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0107Batch15
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0109Batch15
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0111Batch15
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0113Batch15
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0115Batch15
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0303Batch15
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0305Batch15
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0307Batch15
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0309Batch15
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0311Batch15
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0313Batch15
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0315Batch15
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0505Batch15
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0507Batch15
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0509Batch15
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0511Batch15
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0513Batch15
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0515Batch15
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0707Batch15
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0709Batch15
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0711Batch15
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0713Batch15
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0715Batch15
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0909Batch15
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0911Batch15
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0913Batch15
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0915Batch15
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow1111Batch15
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow1113Batch15
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow1115Batch15
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow1313Batch15
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow1315Batch15
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow1515Batch15
import OAI.Analysis.Laughlin.FiniteFlux.Data15
import OAI.Analysis.Laughlin.FourBody.NumericBridge
import OAI.Analysis.Laughlin.FourBody.Symmetry

namespace OAI

namespace Laughlin.Certificate
theorem source_error_15_1_1 : Y 15 1 1 = (1160239161688954312188380157/1048576000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 15 1 1 0 (by decide),
    source_yRow_eq_rowCompute 15 1 1 1 (by decide),
    source_yRow_eq_rowCompute 15 1 1 2 (by decide),
    source_yRow_eq_rowCompute 15 1 1 3 (by decide),
    source_yRow_eq_rowCompute 15 1 1 4 (by decide),
    source_yRow_eq_rowCompute 15 1 1 5 (by decide),
    source_yRow_eq_rowCompute 15 1 1 6 (by decide),
    computeRow_15_1_1_0, computeRow_15_1_1_1, computeRow_15_1_1_2, computeRow_15_1_1_3, computeRow_15_1_1_4, computeRow_15_1_1_5, computeRow_15_1_1_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_15_1_3 : Y 15 1 3 = (527769145158896263581537579/2097152000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 15 1 3 0 (by decide),
    source_yRow_eq_rowCompute 15 1 3 1 (by decide),
    source_yRow_eq_rowCompute 15 1 3 2 (by decide),
    source_yRow_eq_rowCompute 15 1 3 3 (by decide),
    source_yRow_eq_rowCompute 15 1 3 4 (by decide),
    source_yRow_eq_rowCompute 15 1 3 5 (by decide),
    source_yRow_eq_rowCompute 15 1 3 6 (by decide),
    computeRow_15_1_3_0, computeRow_15_1_3_1, computeRow_15_1_3_2, computeRow_15_1_3_3, computeRow_15_1_3_4, computeRow_15_1_3_5, computeRow_15_1_3_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_15_1_5 : Y 15 1 5 = (-364633884256427977153375413/1677721600000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 15 1 5 0 (by decide),
    source_yRow_eq_rowCompute 15 1 5 1 (by decide),
    source_yRow_eq_rowCompute 15 1 5 2 (by decide),
    source_yRow_eq_rowCompute 15 1 5 3 (by decide),
    source_yRow_eq_rowCompute 15 1 5 4 (by decide),
    source_yRow_eq_rowCompute 15 1 5 5 (by decide),
    source_yRow_eq_rowCompute 15 1 5 6 (by decide),
    computeRow_15_1_5_0, computeRow_15_1_5_1, computeRow_15_1_5_2, computeRow_15_1_5_3, computeRow_15_1_5_4, computeRow_15_1_5_5, computeRow_15_1_5_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_15_1_7 : Y 15 1 7 = (70800295830292526868599229/838860800000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 15 1 7 0 (by decide),
    source_yRow_eq_rowCompute 15 1 7 1 (by decide),
    source_yRow_eq_rowCompute 15 1 7 2 (by decide),
    source_yRow_eq_rowCompute 15 1 7 3 (by decide),
    source_yRow_eq_rowCompute 15 1 7 4 (by decide),
    source_yRow_eq_rowCompute 15 1 7 5 (by decide),
    source_yRow_eq_rowCompute 15 1 7 6 (by decide),
    computeRow_15_1_7_0, computeRow_15_1_7_1, computeRow_15_1_7_2, computeRow_15_1_7_3, computeRow_15_1_7_4, computeRow_15_1_7_5, computeRow_15_1_7_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_15_1_9 : Y 15 1 9 = (-213215905018995130639958571/1048576000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 15 1 9 0 (by decide),
    source_yRow_eq_rowCompute 15 1 9 1 (by decide),
    source_yRow_eq_rowCompute 15 1 9 2 (by decide),
    source_yRow_eq_rowCompute 15 1 9 3 (by decide),
    source_yRow_eq_rowCompute 15 1 9 4 (by decide),
    source_yRow_eq_rowCompute 15 1 9 5 (by decide),
    source_yRow_eq_rowCompute 15 1 9 6 (by decide),
    computeRow_15_1_9_0, computeRow_15_1_9_1, computeRow_15_1_9_2, computeRow_15_1_9_3, computeRow_15_1_9_4, computeRow_15_1_9_5, computeRow_15_1_9_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_15_1_11 : Y 15 1 11 = (-236988935373506936612565573/524288000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 15 1 11 0 (by decide),
    source_yRow_eq_rowCompute 15 1 11 1 (by decide),
    source_yRow_eq_rowCompute 15 1 11 2 (by decide),
    source_yRow_eq_rowCompute 15 1 11 3 (by decide),
    source_yRow_eq_rowCompute 15 1 11 4 (by decide),
    source_yRow_eq_rowCompute 15 1 11 5 (by decide),
    source_yRow_eq_rowCompute 15 1 11 6 (by decide),
    computeRow_15_1_11_0, computeRow_15_1_11_1, computeRow_15_1_11_2, computeRow_15_1_11_3, computeRow_15_1_11_4, computeRow_15_1_11_5, computeRow_15_1_11_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_15_1_13 : Y 15 1 13 = (374746885492881333249210393/524288000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 15 1 13 0 (by decide),
    source_yRow_eq_rowCompute 15 1 13 1 (by decide),
    source_yRow_eq_rowCompute 15 1 13 2 (by decide),
    source_yRow_eq_rowCompute 15 1 13 3 (by decide),
    source_yRow_eq_rowCompute 15 1 13 4 (by decide),
    source_yRow_eq_rowCompute 15 1 13 5 (by decide),
    source_yRow_eq_rowCompute 15 1 13 6 (by decide),
    computeRow_15_1_13_0, computeRow_15_1_13_1, computeRow_15_1_13_2, computeRow_15_1_13_3, computeRow_15_1_13_4, computeRow_15_1_13_5, computeRow_15_1_13_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_15_1_15 : Y 15 1 15 = (-1454272995490648196091417189/52428800000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 15 1 15 0 (by decide),
    source_yRow_eq_rowCompute 15 1 15 1 (by decide),
    source_yRow_eq_rowCompute 15 1 15 2 (by decide),
    source_yRow_eq_rowCompute 15 1 15 3 (by decide),
    source_yRow_eq_rowCompute 15 1 15 4 (by decide),
    source_yRow_eq_rowCompute 15 1 15 5 (by decide),
    source_yRow_eq_rowCompute 15 1 15 6 (by decide),
    computeRow_15_1_15_0, computeRow_15_1_15_1, computeRow_15_1_15_2, computeRow_15_1_15_3, computeRow_15_1_15_4, computeRow_15_1_15_5, computeRow_15_1_15_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_15_3_3 : Y 15 3 3 = (-79903889464778925306594867/2097152000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 15 3 3 0 (by decide),
    source_yRow_eq_rowCompute 15 3 3 1 (by decide),
    source_yRow_eq_rowCompute 15 3 3 2 (by decide),
    source_yRow_eq_rowCompute 15 3 3 3 (by decide),
    source_yRow_eq_rowCompute 15 3 3 4 (by decide),
    source_yRow_eq_rowCompute 15 3 3 5 (by decide),
    source_yRow_eq_rowCompute 15 3 3 6 (by decide),
    computeRow_15_3_3_0, computeRow_15_3_3_1, computeRow_15_3_3_2, computeRow_15_3_3_3, computeRow_15_3_3_4, computeRow_15_3_3_5, computeRow_15_3_3_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_15_3_5 : Y 15 3 5 = (10380910649344519579874271/838860800000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 15 3 5 0 (by decide),
    source_yRow_eq_rowCompute 15 3 5 1 (by decide),
    source_yRow_eq_rowCompute 15 3 5 2 (by decide),
    source_yRow_eq_rowCompute 15 3 5 3 (by decide),
    source_yRow_eq_rowCompute 15 3 5 4 (by decide),
    source_yRow_eq_rowCompute 15 3 5 5 (by decide),
    source_yRow_eq_rowCompute 15 3 5 6 (by decide),
    computeRow_15_3_5_0, computeRow_15_3_5_1, computeRow_15_3_5_2, computeRow_15_3_5_3, computeRow_15_3_5_4, computeRow_15_3_5_5, computeRow_15_3_5_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_15_3_7 : Y 15 3 7 = (2399450471501791440121389/419430400000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 15 3 7 0 (by decide),
    source_yRow_eq_rowCompute 15 3 7 1 (by decide),
    source_yRow_eq_rowCompute 15 3 7 2 (by decide),
    source_yRow_eq_rowCompute 15 3 7 3 (by decide),
    source_yRow_eq_rowCompute 15 3 7 4 (by decide),
    source_yRow_eq_rowCompute 15 3 7 5 (by decide),
    source_yRow_eq_rowCompute 15 3 7 6 (by decide),
    computeRow_15_3_7_0, computeRow_15_3_7_1, computeRow_15_3_7_2, computeRow_15_3_7_3, computeRow_15_3_7_4, computeRow_15_3_7_5, computeRow_15_3_7_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_15_3_9 : Y 15 3 9 = (7831247768240800098462597/524288000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 15 3 9 0 (by decide),
    source_yRow_eq_rowCompute 15 3 9 1 (by decide),
    source_yRow_eq_rowCompute 15 3 9 2 (by decide),
    source_yRow_eq_rowCompute 15 3 9 3 (by decide),
    source_yRow_eq_rowCompute 15 3 9 4 (by decide),
    source_yRow_eq_rowCompute 15 3 9 5 (by decide),
    source_yRow_eq_rowCompute 15 3 9 6 (by decide),
    computeRow_15_3_9_0, computeRow_15_3_9_1, computeRow_15_3_9_2, computeRow_15_3_9_3, computeRow_15_3_9_4, computeRow_15_3_9_5, computeRow_15_3_9_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_15_3_11 : Y 15 3 11 = (260365051976410952573409/52428800000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 15 3 11 0 (by decide),
    source_yRow_eq_rowCompute 15 3 11 1 (by decide),
    source_yRow_eq_rowCompute 15 3 11 2 (by decide),
    source_yRow_eq_rowCompute 15 3 11 3 (by decide),
    source_yRow_eq_rowCompute 15 3 11 4 (by decide),
    source_yRow_eq_rowCompute 15 3 11 5 (by decide),
    source_yRow_eq_rowCompute 15 3 11 6 (by decide),
    computeRow_15_3_11_0, computeRow_15_3_11_1, computeRow_15_3_11_2, computeRow_15_3_11_3, computeRow_15_3_11_4, computeRow_15_3_11_5, computeRow_15_3_11_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_15_3_13 : Y 15 3 13 = (15417580069242120546303813/262144000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 15 3 13 0 (by decide),
    source_yRow_eq_rowCompute 15 3 13 1 (by decide),
    source_yRow_eq_rowCompute 15 3 13 2 (by decide),
    source_yRow_eq_rowCompute 15 3 13 3 (by decide),
    source_yRow_eq_rowCompute 15 3 13 4 (by decide),
    source_yRow_eq_rowCompute 15 3 13 5 (by decide),
    source_yRow_eq_rowCompute 15 3 13 6 (by decide),
    computeRow_15_3_13_0, computeRow_15_3_13_1, computeRow_15_3_13_2, computeRow_15_3_13_3, computeRow_15_3_13_4, computeRow_15_3_13_5, computeRow_15_3_13_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_15_3_15 : Y 15 3 15 = (-19651317795670208550803901/26214400000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 15 3 15 0 (by decide),
    source_yRow_eq_rowCompute 15 3 15 1 (by decide),
    source_yRow_eq_rowCompute 15 3 15 2 (by decide),
    source_yRow_eq_rowCompute 15 3 15 3 (by decide),
    source_yRow_eq_rowCompute 15 3 15 4 (by decide),
    source_yRow_eq_rowCompute 15 3 15 5 (by decide),
    source_yRow_eq_rowCompute 15 3 15 6 (by decide),
    computeRow_15_3_15_0, computeRow_15_3_15_1, computeRow_15_3_15_2, computeRow_15_3_15_3, computeRow_15_3_15_4, computeRow_15_3_15_5, computeRow_15_3_15_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_15_5_5 : Y 15 5 5 = (-544144788797698439940321/335544320000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 15 5 5 0 (by decide),
    source_yRow_eq_rowCompute 15 5 5 1 (by decide),
    source_yRow_eq_rowCompute 15 5 5 2 (by decide),
    source_yRow_eq_rowCompute 15 5 5 3 (by decide),
    source_yRow_eq_rowCompute 15 5 5 4 (by decide),
    source_yRow_eq_rowCompute 15 5 5 5 (by decide),
    source_yRow_eq_rowCompute 15 5 5 6 (by decide),
    computeRow_15_5_5_0, computeRow_15_5_5_1, computeRow_15_5_5_2, computeRow_15_5_5_3, computeRow_15_5_5_4, computeRow_15_5_5_5, computeRow_15_5_5_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_15_5_7 : Y 15 5 7 = (-1550173356554793074510931/838860800000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 15 5 7 0 (by decide),
    source_yRow_eq_rowCompute 15 5 7 1 (by decide),
    source_yRow_eq_rowCompute 15 5 7 2 (by decide),
    source_yRow_eq_rowCompute 15 5 7 3 (by decide),
    source_yRow_eq_rowCompute 15 5 7 4 (by decide),
    source_yRow_eq_rowCompute 15 5 7 5 (by decide),
    source_yRow_eq_rowCompute 15 5 7 6 (by decide),
    computeRow_15_5_7_0, computeRow_15_5_7_1, computeRow_15_5_7_2, computeRow_15_5_7_3, computeRow_15_5_7_4, computeRow_15_5_7_5, computeRow_15_5_7_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_15_5_9 : Y 15 5 9 = (-251612565167710626302493/209715200000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 15 5 9 0 (by decide),
    source_yRow_eq_rowCompute 15 5 9 1 (by decide),
    source_yRow_eq_rowCompute 15 5 9 2 (by decide),
    source_yRow_eq_rowCompute 15 5 9 3 (by decide),
    source_yRow_eq_rowCompute 15 5 9 4 (by decide),
    source_yRow_eq_rowCompute 15 5 9 5 (by decide),
    source_yRow_eq_rowCompute 15 5 9 6 (by decide),
    computeRow_15_5_9_0, computeRow_15_5_9_1, computeRow_15_5_9_2, computeRow_15_5_9_3, computeRow_15_5_9_4, computeRow_15_5_9_5, computeRow_15_5_9_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_15_5_11 : Y 15 5 11 = (412467042517374252900789/104857600000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 15 5 11 0 (by decide),
    source_yRow_eq_rowCompute 15 5 11 1 (by decide),
    source_yRow_eq_rowCompute 15 5 11 2 (by decide),
    source_yRow_eq_rowCompute 15 5 11 3 (by decide),
    source_yRow_eq_rowCompute 15 5 11 4 (by decide),
    source_yRow_eq_rowCompute 15 5 11 5 (by decide),
    source_yRow_eq_rowCompute 15 5 11 6 (by decide),
    computeRow_15_5_11_0, computeRow_15_5_11_1, computeRow_15_5_11_2, computeRow_15_5_11_3, computeRow_15_5_11_4, computeRow_15_5_11_5, computeRow_15_5_11_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_15_5_13 : Y 15 5 13 = (-3917597116231063282740723/104857600000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 15 5 13 0 (by decide),
    source_yRow_eq_rowCompute 15 5 13 1 (by decide),
    source_yRow_eq_rowCompute 15 5 13 2 (by decide),
    source_yRow_eq_rowCompute 15 5 13 3 (by decide),
    source_yRow_eq_rowCompute 15 5 13 4 (by decide),
    source_yRow_eq_rowCompute 15 5 13 5 (by decide),
    source_yRow_eq_rowCompute 15 5 13 6 (by decide),
    computeRow_15_5_13_0, computeRow_15_5_13_1, computeRow_15_5_13_2, computeRow_15_5_13_3, computeRow_15_5_13_4, computeRow_15_5_13_5, computeRow_15_5_13_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_15_5_15 : Y 15 5 15 = (6737890215993101774728119/10485760000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 15 5 15 0 (by decide),
    source_yRow_eq_rowCompute 15 5 15 1 (by decide),
    source_yRow_eq_rowCompute 15 5 15 2 (by decide),
    source_yRow_eq_rowCompute 15 5 15 3 (by decide),
    source_yRow_eq_rowCompute 15 5 15 4 (by decide),
    source_yRow_eq_rowCompute 15 5 15 5 (by decide),
    source_yRow_eq_rowCompute 15 5 15 6 (by decide),
    computeRow_15_5_15_0, computeRow_15_5_15_1, computeRow_15_5_15_2, computeRow_15_5_15_3, computeRow_15_5_15_4, computeRow_15_5_15_5, computeRow_15_5_15_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_15_7_7 : Y 15 7 7 = (-11010455047903773080463201/2097152000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 15 7 7 0 (by decide),
    source_yRow_eq_rowCompute 15 7 7 1 (by decide),
    source_yRow_eq_rowCompute 15 7 7 2 (by decide),
    source_yRow_eq_rowCompute 15 7 7 3 (by decide),
    source_yRow_eq_rowCompute 15 7 7 4 (by decide),
    source_yRow_eq_rowCompute 15 7 7 5 (by decide),
    source_yRow_eq_rowCompute 15 7 7 6 (by decide),
    computeRow_15_7_7_0, computeRow_15_7_7_1, computeRow_15_7_7_2, computeRow_15_7_7_3, computeRow_15_7_7_4, computeRow_15_7_7_5, computeRow_15_7_7_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_15_7_9 : Y 15 7 9 = (483384920806779568744041/524288000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 15 7 9 0 (by decide),
    source_yRow_eq_rowCompute 15 7 9 1 (by decide),
    source_yRow_eq_rowCompute 15 7 9 2 (by decide),
    source_yRow_eq_rowCompute 15 7 9 3 (by decide),
    source_yRow_eq_rowCompute 15 7 9 4 (by decide),
    source_yRow_eq_rowCompute 15 7 9 5 (by decide),
    source_yRow_eq_rowCompute 15 7 9 6 (by decide),
    computeRow_15_7_9_0, computeRow_15_7_9_1, computeRow_15_7_9_2, computeRow_15_7_9_3, computeRow_15_7_9_4, computeRow_15_7_9_5, computeRow_15_7_9_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_15_7_11 : Y 15 7 11 = (-2196385127442123145785873/262144000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 15 7 11 0 (by decide),
    source_yRow_eq_rowCompute 15 7 11 1 (by decide),
    source_yRow_eq_rowCompute 15 7 11 2 (by decide),
    source_yRow_eq_rowCompute 15 7 11 3 (by decide),
    source_yRow_eq_rowCompute 15 7 11 4 (by decide),
    source_yRow_eq_rowCompute 15 7 11 5 (by decide),
    source_yRow_eq_rowCompute 15 7 11 6 (by decide),
    computeRow_15_7_11_0, computeRow_15_7_11_1, computeRow_15_7_11_2, computeRow_15_7_11_3, computeRow_15_7_11_4, computeRow_15_7_11_5, computeRow_15_7_11_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_15_7_13 : Y 15 7 13 = (-3020058706667129324414217/262144000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 15 7 13 0 (by decide),
    source_yRow_eq_rowCompute 15 7 13 1 (by decide),
    source_yRow_eq_rowCompute 15 7 13 2 (by decide),
    source_yRow_eq_rowCompute 15 7 13 3 (by decide),
    source_yRow_eq_rowCompute 15 7 13 4 (by decide),
    source_yRow_eq_rowCompute 15 7 13 5 (by decide),
    source_yRow_eq_rowCompute 15 7 13 6 (by decide),
    computeRow_15_7_13_0, computeRow_15_7_13_1, computeRow_15_7_13_2, computeRow_15_7_13_3, computeRow_15_7_13_4, computeRow_15_7_13_5, computeRow_15_7_13_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_15_7_15 : Y 15 7 15 = (6630571266894369608354541/26214400000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 15 7 15 0 (by decide),
    source_yRow_eq_rowCompute 15 7 15 1 (by decide),
    source_yRow_eq_rowCompute 15 7 15 2 (by decide),
    source_yRow_eq_rowCompute 15 7 15 3 (by decide),
    source_yRow_eq_rowCompute 15 7 15 4 (by decide),
    source_yRow_eq_rowCompute 15 7 15 5 (by decide),
    source_yRow_eq_rowCompute 15 7 15 6 (by decide),
    computeRow_15_7_15_0, computeRow_15_7_15_1, computeRow_15_7_15_2, computeRow_15_7_15_3, computeRow_15_7_15_4, computeRow_15_7_15_5, computeRow_15_7_15_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_15_9_9 : Y 15 9 9 = (-733927230254603053476261/131072000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 15 9 9 0 (by decide),
    source_yRow_eq_rowCompute 15 9 9 1 (by decide),
    source_yRow_eq_rowCompute 15 9 9 2 (by decide),
    source_yRow_eq_rowCompute 15 9 9 3 (by decide),
    source_yRow_eq_rowCompute 15 9 9 4 (by decide),
    source_yRow_eq_rowCompute 15 9 9 5 (by decide),
    source_yRow_eq_rowCompute 15 9 9 6 (by decide),
    computeRow_15_9_9_0, computeRow_15_9_9_1, computeRow_15_9_9_2, computeRow_15_9_9_3, computeRow_15_9_9_4, computeRow_15_9_9_5, computeRow_15_9_9_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_15_9_11 : Y 15 9 11 = (144198476217622441333917/65536000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 15 9 11 0 (by decide),
    source_yRow_eq_rowCompute 15 9 11 1 (by decide),
    source_yRow_eq_rowCompute 15 9 11 2 (by decide),
    source_yRow_eq_rowCompute 15 9 11 3 (by decide),
    source_yRow_eq_rowCompute 15 9 11 4 (by decide),
    source_yRow_eq_rowCompute 15 9 11 5 (by decide),
    source_yRow_eq_rowCompute 15 9 11 6 (by decide),
    computeRow_15_9_11_0, computeRow_15_9_11_1, computeRow_15_9_11_2, computeRow_15_9_11_3, computeRow_15_9_11_4, computeRow_15_9_11_5, computeRow_15_9_11_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_15_9_13 : Y 15 9 13 = (-270537545003843608530039/65536000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 15 9 13 0 (by decide),
    source_yRow_eq_rowCompute 15 9 13 1 (by decide),
    source_yRow_eq_rowCompute 15 9 13 2 (by decide),
    source_yRow_eq_rowCompute 15 9 13 3 (by decide),
    source_yRow_eq_rowCompute 15 9 13 4 (by decide),
    source_yRow_eq_rowCompute 15 9 13 5 (by decide),
    source_yRow_eq_rowCompute 15 9 13 6 (by decide),
    computeRow_15_9_13_0, computeRow_15_9_13_1, computeRow_15_9_13_2, computeRow_15_9_13_3, computeRow_15_9_13_4, computeRow_15_9_13_5, computeRow_15_9_13_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_15_9_15 : Y 15 9 15 = (488416974255188057862783/1310720000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 15 9 15 0 (by decide),
    source_yRow_eq_rowCompute 15 9 15 1 (by decide),
    source_yRow_eq_rowCompute 15 9 15 2 (by decide),
    source_yRow_eq_rowCompute 15 9 15 3 (by decide),
    source_yRow_eq_rowCompute 15 9 15 4 (by decide),
    source_yRow_eq_rowCompute 15 9 15 5 (by decide),
    source_yRow_eq_rowCompute 15 9 15 6 (by decide),
    computeRow_15_9_15_0, computeRow_15_9_15_1, computeRow_15_9_15_2, computeRow_15_9_15_3, computeRow_15_9_15_4, computeRow_15_9_15_5, computeRow_15_9_15_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_15_11_11 : Y 15 11 11 = (103242122786757662097687/32768000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 15 11 11 0 (by decide),
    source_yRow_eq_rowCompute 15 11 11 1 (by decide),
    source_yRow_eq_rowCompute 15 11 11 2 (by decide),
    source_yRow_eq_rowCompute 15 11 11 3 (by decide),
    source_yRow_eq_rowCompute 15 11 11 4 (by decide),
    source_yRow_eq_rowCompute 15 11 11 5 (by decide),
    source_yRow_eq_rowCompute 15 11 11 6 (by decide),
    computeRow_15_11_11_0, computeRow_15_11_11_1, computeRow_15_11_11_2, computeRow_15_11_11_3, computeRow_15_11_11_4, computeRow_15_11_11_5, computeRow_15_11_11_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_15_11_13 : Y 15 11 13 = (-1188419411670004290171681/32768000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 15 11 13 0 (by decide),
    source_yRow_eq_rowCompute 15 11 13 1 (by decide),
    source_yRow_eq_rowCompute 15 11 13 2 (by decide),
    source_yRow_eq_rowCompute 15 11 13 3 (by decide),
    source_yRow_eq_rowCompute 15 11 13 4 (by decide),
    source_yRow_eq_rowCompute 15 11 13 5 (by decide),
    source_yRow_eq_rowCompute 15 11 13 6 (by decide),
    computeRow_15_11_13_0, computeRow_15_11_13_1, computeRow_15_11_13_2, computeRow_15_11_13_3, computeRow_15_11_13_4, computeRow_15_11_13_5, computeRow_15_11_13_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_15_11_15 : Y 15 11 15 = (-946932022961651320973379/3276800000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 15 11 15 0 (by decide),
    source_yRow_eq_rowCompute 15 11 15 1 (by decide),
    source_yRow_eq_rowCompute 15 11 15 2 (by decide),
    source_yRow_eq_rowCompute 15 11 15 3 (by decide),
    source_yRow_eq_rowCompute 15 11 15 4 (by decide),
    source_yRow_eq_rowCompute 15 11 15 5 (by decide),
    source_yRow_eq_rowCompute 15 11 15 6 (by decide),
    computeRow_15_11_15_0, computeRow_15_11_15_1, computeRow_15_11_15_2, computeRow_15_11_15_3, computeRow_15_11_15_4, computeRow_15_11_15_5, computeRow_15_11_15_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_15_13_13 : Y 15 13 13 = (-13385634727914986582216457/32768000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 15 13 13 0 (by decide),
    source_yRow_eq_rowCompute 15 13 13 1 (by decide),
    source_yRow_eq_rowCompute 15 13 13 2 (by decide),
    source_yRow_eq_rowCompute 15 13 13 3 (by decide),
    source_yRow_eq_rowCompute 15 13 13 4 (by decide),
    source_yRow_eq_rowCompute 15 13 13 5 (by decide),
    source_yRow_eq_rowCompute 15 13 13 6 (by decide),
    computeRow_15_13_13_0, computeRow_15_13_13_1, computeRow_15_13_13_2, computeRow_15_13_13_3, computeRow_15_13_13_4, computeRow_15_13_13_5, computeRow_15_13_13_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_15_13_15 : Y 15 13 15 = (6044229669744752465993013/3276800000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 15 13 15 0 (by decide),
    source_yRow_eq_rowCompute 15 13 15 1 (by decide),
    source_yRow_eq_rowCompute 15 13 15 2 (by decide),
    source_yRow_eq_rowCompute 15 13 15 3 (by decide),
    source_yRow_eq_rowCompute 15 13 15 4 (by decide),
    source_yRow_eq_rowCompute 15 13 15 5 (by decide),
    source_yRow_eq_rowCompute 15 13 15 6 (by decide),
    computeRow_15_13_15_0, computeRow_15_13_15_1, computeRow_15_13_15_2, computeRow_15_13_15_3, computeRow_15_13_15_4, computeRow_15_13_15_5, computeRow_15_13_15_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_15_15_15 : Y 15 15 15 = (-31526289117493065494479881/327680000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 15 15 15 0 (by decide),
    source_yRow_eq_rowCompute 15 15 15 1 (by decide),
    source_yRow_eq_rowCompute 15 15 15 2 (by decide),
    source_yRow_eq_rowCompute 15 15 15 3 (by decide),
    source_yRow_eq_rowCompute 15 15 15 4 (by decide),
    source_yRow_eq_rowCompute 15 15 15 5 (by decide),
    source_yRow_eq_rowCompute 15 15 15 6 (by decide),
    computeRow_15_15_15_0, computeRow_15_15_15_1, computeRow_15_15_15_2, computeRow_15_15_15_3, computeRow_15_15_15_4, computeRow_15_15_15_5, computeRow_15_15_15_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_gram_15_1_1 : Z 15 1 1 = (174356582400 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_15_1_1

theorem source_gram_15_1_3 : Z 15 1 3 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_15_1_3

theorem source_gram_15_1_5 : Z 15 1 5 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_15_1_5

theorem source_gram_15_1_7 : Z 15 1 7 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_15_1_7

theorem source_gram_15_1_9 : Z 15 1 9 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_15_1_9

theorem source_gram_15_1_11 : Z 15 1 11 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_15_1_11

theorem source_gram_15_1_13 : Z 15 1 13 = (-2724321600 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_15_1_13

theorem source_gram_15_1_15 : Z 15 1 15 = (122594472000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_15_1_15

theorem source_gram_15_3_3 : Z 15 3 3 = (2874009600 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_15_3_3

theorem source_gram_15_3_5 : Z 15 3 5 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_15_3_5

theorem source_gram_15_3_7 : Z 15 3 7 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_15_3_7

theorem source_gram_15_3_9 : Z 15 3 9 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_15_3_9

theorem source_gram_15_3_11 : Z 15 3 11 = (-179625600 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_15_3_11

theorem source_gram_15_3_13 : Z 15 3 13 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_15_3_13

theorem source_gram_15_3_15 : Z 15 3 15 = (40864824000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_15_3_15

theorem source_gram_15_5_5 : Z 15 5 5 = (435456000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_15_5_5

theorem source_gram_15_5_7 : Z 15 5 7 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_15_5_7

theorem source_gram_15_5_9 : Z 15 5 9 = (-40824000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_15_5_9

theorem source_gram_15_5_11 : Z 15 5 11 = (-299376000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_15_5_11

theorem source_gram_15_5_13 : Z 15 5 13 = (1459458000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_15_5_13

theorem source_gram_15_5_15 : Z 15 5 15 = (10216206000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_15_5_15

theorem source_gram_15_7_7 : Z 15 7 7 = (177811200 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_15_7_7

theorem source_gram_15_7_9 : Z 15 7 9 = (-171460800 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_15_7_9

theorem source_gram_15_7_11 : Z 15 7 11 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_15_7_11

theorem source_gram_15_7_13 : Z 15 7 13 = (681080400 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_15_7_13

theorem source_gram_15_7_15 : Z 15 7 15 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_15_7_15

theorem source_gram_15_9_9 : Z 15 9 9 = (175543200 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_15_9_9

theorem source_gram_15_9_11 : Z 15 9 11 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_15_9_11

theorem source_gram_15_9_13 : Z 15 9 13 = (-656756100 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_15_9_13

theorem source_gram_15_9_15 : Z 15 9 15 = (-2554051500 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_15_9_15

theorem source_gram_15_11_11 : Z 15 11 11 = (340540200 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_15_11_11

theorem source_gram_15_11_13 : Z 15 11 13 = (-1605403800 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_15_11_13

theorem source_gram_15_11_15 : Z 15 11 15 = (-2554051500 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_15_11_15

theorem source_gram_15_13_13 : Z 15 13 13 = (10477692225 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_15_13_13

theorem source_gram_15_13_15 : Z 15 13 15 = (-1915538625 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_15_13_15

theorem source_gram_15_15_15 : Z 15 15 15 = (1306397342250 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_15_15_15

theorem source_error_15_3_1 : Y 15 3 1 = (527769145158896263581537579/2097152000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_15_1_3

theorem source_gram_15_3_1 : Z 15 3 1 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_15_1_3

theorem source_error_15_5_1 : Y 15 5 1 = (-364633884256427977153375413/1677721600000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_15_1_5

theorem source_gram_15_5_1 : Z 15 5 1 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_15_1_5

theorem source_error_15_5_3 : Y 15 5 3 = (10380910649344519579874271/838860800000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_15_3_5

theorem source_gram_15_5_3 : Z 15 5 3 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_15_3_5

theorem source_error_15_7_1 : Y 15 7 1 = (70800295830292526868599229/838860800000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_15_1_7

theorem source_gram_15_7_1 : Z 15 7 1 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_15_1_7

theorem source_error_15_7_3 : Y 15 7 3 = (2399450471501791440121389/419430400000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_15_3_7

theorem source_gram_15_7_3 : Z 15 7 3 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_15_3_7

theorem source_error_15_7_5 : Y 15 7 5 = (-1550173356554793074510931/838860800000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_15_5_7

theorem source_gram_15_7_5 : Z 15 7 5 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_15_5_7

theorem source_error_15_9_1 : Y 15 9 1 = (-213215905018995130639958571/1048576000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_15_1_9

theorem source_gram_15_9_1 : Z 15 9 1 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_15_1_9

theorem source_error_15_9_3 : Y 15 9 3 = (7831247768240800098462597/524288000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_15_3_9

theorem source_gram_15_9_3 : Z 15 9 3 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_15_3_9

theorem source_error_15_9_5 : Y 15 9 5 = (-251612565167710626302493/209715200000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_15_5_9

theorem source_gram_15_9_5 : Z 15 9 5 = (-40824000 : ℚ) := by
  rw [Z_symm]
  exact source_gram_15_5_9

theorem source_error_15_9_7 : Y 15 9 7 = (483384920806779568744041/524288000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_15_7_9

theorem source_gram_15_9_7 : Z 15 9 7 = (-171460800 : ℚ) := by
  rw [Z_symm]
  exact source_gram_15_7_9

theorem source_error_15_11_1 : Y 15 11 1 = (-236988935373506936612565573/524288000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_15_1_11

theorem source_gram_15_11_1 : Z 15 11 1 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_15_1_11

theorem source_error_15_11_3 : Y 15 11 3 = (260365051976410952573409/52428800000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_15_3_11

theorem source_gram_15_11_3 : Z 15 11 3 = (-179625600 : ℚ) := by
  rw [Z_symm]
  exact source_gram_15_3_11

theorem source_error_15_11_5 : Y 15 11 5 = (412467042517374252900789/104857600000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_15_5_11

theorem source_gram_15_11_5 : Z 15 11 5 = (-299376000 : ℚ) := by
  rw [Z_symm]
  exact source_gram_15_5_11

theorem source_error_15_11_7 : Y 15 11 7 = (-2196385127442123145785873/262144000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_15_7_11

theorem source_gram_15_11_7 : Z 15 11 7 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_15_7_11

theorem source_error_15_11_9 : Y 15 11 9 = (144198476217622441333917/65536000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_15_9_11

theorem source_gram_15_11_9 : Z 15 11 9 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_15_9_11

theorem source_error_15_13_1 : Y 15 13 1 = (374746885492881333249210393/524288000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_15_1_13

theorem source_gram_15_13_1 : Z 15 13 1 = (-2724321600 : ℚ) := by
  rw [Z_symm]
  exact source_gram_15_1_13

theorem source_error_15_13_3 : Y 15 13 3 = (15417580069242120546303813/262144000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_15_3_13

theorem source_gram_15_13_3 : Z 15 13 3 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_15_3_13

theorem source_error_15_13_5 : Y 15 13 5 = (-3917597116231063282740723/104857600000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_15_5_13

theorem source_gram_15_13_5 : Z 15 13 5 = (1459458000 : ℚ) := by
  rw [Z_symm]
  exact source_gram_15_5_13

theorem source_error_15_13_7 : Y 15 13 7 = (-3020058706667129324414217/262144000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_15_7_13

theorem source_gram_15_13_7 : Z 15 13 7 = (681080400 : ℚ) := by
  rw [Z_symm]
  exact source_gram_15_7_13

theorem source_error_15_13_9 : Y 15 13 9 = (-270537545003843608530039/65536000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_15_9_13

theorem source_gram_15_13_9 : Z 15 13 9 = (-656756100 : ℚ) := by
  rw [Z_symm]
  exact source_gram_15_9_13

theorem source_error_15_13_11 : Y 15 13 11 = (-1188419411670004290171681/32768000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_15_11_13

theorem source_gram_15_13_11 : Z 15 13 11 = (-1605403800 : ℚ) := by
  rw [Z_symm]
  exact source_gram_15_11_13

theorem source_error_15_15_1 : Y 15 15 1 = (-1454272995490648196091417189/52428800000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_15_1_15

theorem source_gram_15_15_1 : Z 15 15 1 = (122594472000 : ℚ) := by
  rw [Z_symm]
  exact source_gram_15_1_15

theorem source_error_15_15_3 : Y 15 15 3 = (-19651317795670208550803901/26214400000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_15_3_15

theorem source_gram_15_15_3 : Z 15 15 3 = (40864824000 : ℚ) := by
  rw [Z_symm]
  exact source_gram_15_3_15

theorem source_error_15_15_5 : Y 15 15 5 = (6737890215993101774728119/10485760000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_15_5_15

theorem source_gram_15_15_5 : Z 15 15 5 = (10216206000 : ℚ) := by
  rw [Z_symm]
  exact source_gram_15_5_15

theorem source_error_15_15_7 : Y 15 15 7 = (6630571266894369608354541/26214400000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_15_7_15

theorem source_gram_15_15_7 : Z 15 15 7 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_15_7_15

theorem source_error_15_15_9 : Y 15 15 9 = (488416974255188057862783/1310720000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_15_9_15

theorem source_gram_15_15_9 : Z 15 15 9 = (-2554051500 : ℚ) := by
  rw [Z_symm]
  exact source_gram_15_9_15

theorem source_error_15_15_11 : Y 15 15 11 = (-946932022961651320973379/3276800000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_15_11_15

theorem source_gram_15_15_11 : Z 15 15 11 = (-2554051500 : ℚ) := by
  rw [Z_symm]
  exact source_gram_15_11_15

theorem source_error_15_15_13 : Y 15 15 13 = (6044229669744752465993013/3276800000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_15_13_15

theorem source_gram_15_15_13 : Z 15 15 13 = (-1915538625 : ℚ) := by
  rw [Z_symm]
  exact source_gram_15_13_15

theorem error_15 : errorRational 15 = candidateY_15 := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact source_error_15_1_1
  · exact source_error_15_1_3
  · exact source_error_15_1_5
  · exact source_error_15_1_7
  · exact source_error_15_1_9
  · exact source_error_15_1_11
  · exact source_error_15_1_13
  · exact source_error_15_1_15
  · exact source_error_15_3_1
  · exact source_error_15_3_3
  · exact source_error_15_3_5
  · exact source_error_15_3_7
  · exact source_error_15_3_9
  · exact source_error_15_3_11
  · exact source_error_15_3_13
  · exact source_error_15_3_15
  · exact source_error_15_5_1
  · exact source_error_15_5_3
  · exact source_error_15_5_5
  · exact source_error_15_5_7
  · exact source_error_15_5_9
  · exact source_error_15_5_11
  · exact source_error_15_5_13
  · exact source_error_15_5_15
  · exact source_error_15_7_1
  · exact source_error_15_7_3
  · exact source_error_15_7_5
  · exact source_error_15_7_7
  · exact source_error_15_7_9
  · exact source_error_15_7_11
  · exact source_error_15_7_13
  · exact source_error_15_7_15
  · exact source_error_15_9_1
  · exact source_error_15_9_3
  · exact source_error_15_9_5
  · exact source_error_15_9_7
  · exact source_error_15_9_9
  · exact source_error_15_9_11
  · exact source_error_15_9_13
  · exact source_error_15_9_15
  · exact source_error_15_11_1
  · exact source_error_15_11_3
  · exact source_error_15_11_5
  · exact source_error_15_11_7
  · exact source_error_15_11_9
  · exact source_error_15_11_11
  · exact source_error_15_11_13
  · exact source_error_15_11_15
  · exact source_error_15_13_1
  · exact source_error_15_13_3
  · exact source_error_15_13_5
  · exact source_error_15_13_7
  · exact source_error_15_13_9
  · exact source_error_15_13_11
  · exact source_error_15_13_13
  · exact source_error_15_13_15
  · exact source_error_15_15_1
  · exact source_error_15_15_3
  · exact source_error_15_15_5
  · exact source_error_15_15_7
  · exact source_error_15_15_9
  · exact source_error_15_15_11
  · exact source_error_15_15_13
  · exact source_error_15_15_15

theorem gram_15 : gramRational 15 = candidateZ_15 := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact source_gram_15_1_1
  · exact source_gram_15_1_3
  · exact source_gram_15_1_5
  · exact source_gram_15_1_7
  · exact source_gram_15_1_9
  · exact source_gram_15_1_11
  · exact source_gram_15_1_13
  · exact source_gram_15_1_15
  · exact source_gram_15_3_1
  · exact source_gram_15_3_3
  · exact source_gram_15_3_5
  · exact source_gram_15_3_7
  · exact source_gram_15_3_9
  · exact source_gram_15_3_11
  · exact source_gram_15_3_13
  · exact source_gram_15_3_15
  · exact source_gram_15_5_1
  · exact source_gram_15_5_3
  · exact source_gram_15_5_5
  · exact source_gram_15_5_7
  · exact source_gram_15_5_9
  · exact source_gram_15_5_11
  · exact source_gram_15_5_13
  · exact source_gram_15_5_15
  · exact source_gram_15_7_1
  · exact source_gram_15_7_3
  · exact source_gram_15_7_5
  · exact source_gram_15_7_7
  · exact source_gram_15_7_9
  · exact source_gram_15_7_11
  · exact source_gram_15_7_13
  · exact source_gram_15_7_15
  · exact source_gram_15_9_1
  · exact source_gram_15_9_3
  · exact source_gram_15_9_5
  · exact source_gram_15_9_7
  · exact source_gram_15_9_9
  · exact source_gram_15_9_11
  · exact source_gram_15_9_13
  · exact source_gram_15_9_15
  · exact source_gram_15_11_1
  · exact source_gram_15_11_3
  · exact source_gram_15_11_5
  · exact source_gram_15_11_7
  · exact source_gram_15_11_9
  · exact source_gram_15_11_11
  · exact source_gram_15_11_13
  · exact source_gram_15_11_15
  · exact source_gram_15_13_1
  · exact source_gram_15_13_3
  · exact source_gram_15_13_5
  · exact source_gram_15_13_7
  · exact source_gram_15_13_9
  · exact source_gram_15_13_11
  · exact source_gram_15_13_13
  · exact source_gram_15_13_15
  · exact source_gram_15_15_1
  · exact source_gram_15_15_3
  · exact source_gram_15_15_5
  · exact source_gram_15_15_7
  · exact source_gram_15_15_9
  · exact source_gram_15_15_11
  · exact source_gram_15_15_13
  · exact source_gram_15_15_15

end Laughlin.Certificate

end OAI
