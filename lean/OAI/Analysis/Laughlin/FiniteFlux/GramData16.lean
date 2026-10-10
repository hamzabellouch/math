import OAI.Analysis.Laughlin.FiniteFlux.ComputeGram01Batch16
import OAI.Analysis.Laughlin.FiniteFlux.ComputeGram03Batch16
import OAI.Analysis.Laughlin.FiniteFlux.ComputeGram05Batch16
import OAI.Analysis.Laughlin.FiniteFlux.ComputeGram07Batch16
import OAI.Analysis.Laughlin.FiniteFlux.ComputeGram09Batch16
import OAI.Analysis.Laughlin.FiniteFlux.ComputeGram11Batch16
import OAI.Analysis.Laughlin.FiniteFlux.ComputeGram13Batch16
import OAI.Analysis.Laughlin.FiniteFlux.ComputeGram151516
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0101Batch16
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0103Batch16
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0105Batch16
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0107Batch16
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0109Batch16
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0111Batch16
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0113Batch16
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0115Batch16
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0303Batch16
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0305Batch16
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0307Batch16
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0309Batch16
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0311Batch16
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0313Batch16
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0315Batch16
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0505Batch16
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0507Batch16
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0509Batch16
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0511Batch16
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0513Batch16
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0515Batch16
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0707Batch16
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0709Batch16
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0711Batch16
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0713Batch16
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0715Batch16
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0909Batch16
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0911Batch16
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0913Batch16
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0915Batch16
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow1111Batch16
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow1113Batch16
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow1115Batch16
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow1313Batch16
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow1315Batch16
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow1515Batch16
import OAI.Analysis.Laughlin.FiniteFlux.Data16
import OAI.Analysis.Laughlin.FourBody.NumericBridge
import OAI.Analysis.Laughlin.FourBody.Symmetry

namespace OAI

namespace Laughlin.Certificate
theorem source_error_16_1_1 : Y 16 1 1 = (-2276708101299057121652517561/52428800000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 16 1 1 0 (by decide),
    source_yRow_eq_rowCompute 16 1 1 1 (by decide),
    source_yRow_eq_rowCompute 16 1 1 2 (by decide),
    source_yRow_eq_rowCompute 16 1 1 3 (by decide),
    source_yRow_eq_rowCompute 16 1 1 4 (by decide),
    source_yRow_eq_rowCompute 16 1 1 5 (by decide),
    source_yRow_eq_rowCompute 16 1 1 6 (by decide),
    computeRow_16_1_1_0, computeRow_16_1_1_1, computeRow_16_1_1_2, computeRow_16_1_1_3, computeRow_16_1_1_4, computeRow_16_1_1_5, computeRow_16_1_1_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_16_1_3 : Y 16 1 3 = (-39034614015379387104670971/13107200000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 16 1 3 0 (by decide),
    source_yRow_eq_rowCompute 16 1 3 1 (by decide),
    source_yRow_eq_rowCompute 16 1 3 2 (by decide),
    source_yRow_eq_rowCompute 16 1 3 3 (by decide),
    source_yRow_eq_rowCompute 16 1 3 4 (by decide),
    source_yRow_eq_rowCompute 16 1 3 5 (by decide),
    source_yRow_eq_rowCompute 16 1 3 6 (by decide),
    computeRow_16_1_3_0, computeRow_16_1_3_1, computeRow_16_1_3_2, computeRow_16_1_3_3, computeRow_16_1_3_4, computeRow_16_1_3_5, computeRow_16_1_3_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_16_1_5 : Y 16 1 5 = (78202406241711463127687271/83886080000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 16 1 5 0 (by decide),
    source_yRow_eq_rowCompute 16 1 5 1 (by decide),
    source_yRow_eq_rowCompute 16 1 5 2 (by decide),
    source_yRow_eq_rowCompute 16 1 5 3 (by decide),
    source_yRow_eq_rowCompute 16 1 5 4 (by decide),
    source_yRow_eq_rowCompute 16 1 5 5 (by decide),
    source_yRow_eq_rowCompute 16 1 5 6 (by decide),
    computeRow_16_1_5_0, computeRow_16_1_5_1, computeRow_16_1_5_2, computeRow_16_1_5_3, computeRow_16_1_5_4, computeRow_16_1_5_5, computeRow_16_1_5_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_16_1_7 : Y 16 1 7 = (23832834670493732956060989/209715200000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 16 1 7 0 (by decide),
    source_yRow_eq_rowCompute 16 1 7 1 (by decide),
    source_yRow_eq_rowCompute 16 1 7 2 (by decide),
    source_yRow_eq_rowCompute 16 1 7 3 (by decide),
    source_yRow_eq_rowCompute 16 1 7 4 (by decide),
    source_yRow_eq_rowCompute 16 1 7 5 (by decide),
    source_yRow_eq_rowCompute 16 1 7 6 (by decide),
    computeRow_16_1_7_0, computeRow_16_1_7_1, computeRow_16_1_7_2, computeRow_16_1_7_3, computeRow_16_1_7_4, computeRow_16_1_7_5, computeRow_16_1_7_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_16_1_9 : Y 16 1 9 = (22048584820368310367604441/52428800000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 16 1 9 0 (by decide),
    source_yRow_eq_rowCompute 16 1 9 1 (by decide),
    source_yRow_eq_rowCompute 16 1 9 2 (by decide),
    source_yRow_eq_rowCompute 16 1 9 3 (by decide),
    source_yRow_eq_rowCompute 16 1 9 4 (by decide),
    source_yRow_eq_rowCompute 16 1 9 5 (by decide),
    source_yRow_eq_rowCompute 16 1 9 6 (by decide),
    computeRow_16_1_9_0, computeRow_16_1_9_1, computeRow_16_1_9_2, computeRow_16_1_9_3, computeRow_16_1_9_4, computeRow_16_1_9_5, computeRow_16_1_9_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_16_1_11 : Y 16 1 11 = (2553473034802720354150827/26214400000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 16 1 11 0 (by decide),
    source_yRow_eq_rowCompute 16 1 11 1 (by decide),
    source_yRow_eq_rowCompute 16 1 11 2 (by decide),
    source_yRow_eq_rowCompute 16 1 11 3 (by decide),
    source_yRow_eq_rowCompute 16 1 11 4 (by decide),
    source_yRow_eq_rowCompute 16 1 11 5 (by decide),
    source_yRow_eq_rowCompute 16 1 11 6 (by decide),
    computeRow_16_1_11_0, computeRow_16_1_11_1, computeRow_16_1_11_2, computeRow_16_1_11_3, computeRow_16_1_11_4, computeRow_16_1_11_5, computeRow_16_1_11_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_16_1_13 : Y 16 1 13 = (108255415269241130506236621/26214400000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 16 1 13 0 (by decide),
    source_yRow_eq_rowCompute 16 1 13 1 (by decide),
    source_yRow_eq_rowCompute 16 1 13 2 (by decide),
    source_yRow_eq_rowCompute 16 1 13 3 (by decide),
    source_yRow_eq_rowCompute 16 1 13 4 (by decide),
    source_yRow_eq_rowCompute 16 1 13 5 (by decide),
    source_yRow_eq_rowCompute 16 1 13 6 (by decide),
    computeRow_16_1_13_0, computeRow_16_1_13_1, computeRow_16_1_13_2, computeRow_16_1_13_3, computeRow_16_1_13_4, computeRow_16_1_13_5, computeRow_16_1_13_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_16_1_15 : Y 16 1 15 = (-41435755574383986458435793/2621440000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 16 1 15 0 (by decide),
    source_yRow_eq_rowCompute 16 1 15 1 (by decide),
    source_yRow_eq_rowCompute 16 1 15 2 (by decide),
    source_yRow_eq_rowCompute 16 1 15 3 (by decide),
    source_yRow_eq_rowCompute 16 1 15 4 (by decide),
    source_yRow_eq_rowCompute 16 1 15 5 (by decide),
    source_yRow_eq_rowCompute 16 1 15 6 (by decide),
    computeRow_16_1_15_0, computeRow_16_1_15_1, computeRow_16_1_15_2, computeRow_16_1_15_3, computeRow_16_1_15_4, computeRow_16_1_15_5, computeRow_16_1_15_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_16_3_3 : Y 16 3 3 = (-374098046732570322778463991/1048576000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 16 3 3 0 (by decide),
    source_yRow_eq_rowCompute 16 3 3 1 (by decide),
    source_yRow_eq_rowCompute 16 3 3 2 (by decide),
    source_yRow_eq_rowCompute 16 3 3 3 (by decide),
    source_yRow_eq_rowCompute 16 3 3 4 (by decide),
    source_yRow_eq_rowCompute 16 3 3 5 (by decide),
    source_yRow_eq_rowCompute 16 3 3 6 (by decide),
    computeRow_16_3_3_0, computeRow_16_3_3_1, computeRow_16_3_3_2, computeRow_16_3_3_3, computeRow_16_3_3_4, computeRow_16_3_3_5, computeRow_16_3_3_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_16_3_5 : Y 16 3 5 = (2737552373685628655395239/41943040000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 16 3 5 0 (by decide),
    source_yRow_eq_rowCompute 16 3 5 1 (by decide),
    source_yRow_eq_rowCompute 16 3 5 2 (by decide),
    source_yRow_eq_rowCompute 16 3 5 3 (by decide),
    source_yRow_eq_rowCompute 16 3 5 4 (by decide),
    source_yRow_eq_rowCompute 16 3 5 5 (by decide),
    source_yRow_eq_rowCompute 16 3 5 6 (by decide),
    computeRow_16_3_5_0, computeRow_16_3_5_1, computeRow_16_3_5_2, computeRow_16_3_5_3, computeRow_16_3_5_4, computeRow_16_3_5_5, computeRow_16_3_5_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_16_3_7 : Y 16 3 7 = (22736583113602023500964129/524288000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 16 3 7 0 (by decide),
    source_yRow_eq_rowCompute 16 3 7 1 (by decide),
    source_yRow_eq_rowCompute 16 3 7 2 (by decide),
    source_yRow_eq_rowCompute 16 3 7 3 (by decide),
    source_yRow_eq_rowCompute 16 3 7 4 (by decide),
    source_yRow_eq_rowCompute 16 3 7 5 (by decide),
    source_yRow_eq_rowCompute 16 3 7 6 (by decide),
    computeRow_16_3_7_0, computeRow_16_3_7_1, computeRow_16_3_7_2, computeRow_16_3_7_3, computeRow_16_3_7_4, computeRow_16_3_7_5, computeRow_16_3_7_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_16_3_9 : Y 16 3 9 = (1851780972244557042321633/131072000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 16 3 9 0 (by decide),
    source_yRow_eq_rowCompute 16 3 9 1 (by decide),
    source_yRow_eq_rowCompute 16 3 9 2 (by decide),
    source_yRow_eq_rowCompute 16 3 9 3 (by decide),
    source_yRow_eq_rowCompute 16 3 9 4 (by decide),
    source_yRow_eq_rowCompute 16 3 9 5 (by decide),
    source_yRow_eq_rowCompute 16 3 9 6 (by decide),
    computeRow_16_3_9_0, computeRow_16_3_9_1, computeRow_16_3_9_2, computeRow_16_3_9_3, computeRow_16_3_9_4, computeRow_16_3_9_5, computeRow_16_3_9_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_16_3_11 : Y 16 3 11 = (507618379345280460543/1310720000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 16 3 11 0 (by decide),
    source_yRow_eq_rowCompute 16 3 11 1 (by decide),
    source_yRow_eq_rowCompute 16 3 11 2 (by decide),
    source_yRow_eq_rowCompute 16 3 11 3 (by decide),
    source_yRow_eq_rowCompute 16 3 11 4 (by decide),
    source_yRow_eq_rowCompute 16 3 11 5 (by decide),
    source_yRow_eq_rowCompute 16 3 11 6 (by decide),
    computeRow_16_3_11_0, computeRow_16_3_11_1, computeRow_16_3_11_2, computeRow_16_3_11_3, computeRow_16_3_11_4, computeRow_16_3_11_5, computeRow_16_3_11_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_16_3_13 : Y 16 3 13 = (32584839756386941473215337/65536000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 16 3 13 0 (by decide),
    source_yRow_eq_rowCompute 16 3 13 1 (by decide),
    source_yRow_eq_rowCompute 16 3 13 2 (by decide),
    source_yRow_eq_rowCompute 16 3 13 3 (by decide),
    source_yRow_eq_rowCompute 16 3 13 4 (by decide),
    source_yRow_eq_rowCompute 16 3 13 5 (by decide),
    source_yRow_eq_rowCompute 16 3 13 6 (by decide),
    computeRow_16_3_13_0, computeRow_16_3_13_1, computeRow_16_3_13_2, computeRow_16_3_13_3, computeRow_16_3_13_4, computeRow_16_3_13_5, computeRow_16_3_13_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_16_3_15 : Y 16 3 15 = (-12977256793584317385992841/6553600000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 16 3 15 0 (by decide),
    source_yRow_eq_rowCompute 16 3 15 1 (by decide),
    source_yRow_eq_rowCompute 16 3 15 2 (by decide),
    source_yRow_eq_rowCompute 16 3 15 3 (by decide),
    source_yRow_eq_rowCompute 16 3 15 4 (by decide),
    source_yRow_eq_rowCompute 16 3 15 5 (by decide),
    source_yRow_eq_rowCompute 16 3 15 6 (by decide),
    computeRow_16_3_15_0, computeRow_16_3_15_1, computeRow_16_3_15_2, computeRow_16_3_15_3, computeRow_16_3_15_4, computeRow_16_3_15_5, computeRow_16_3_15_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_16_5_5 : Y 16 5 5 = (-2533363535515609982834649/83886080000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 16 5 5 0 (by decide),
    source_yRow_eq_rowCompute 16 5 5 1 (by decide),
    source_yRow_eq_rowCompute 16 5 5 2 (by decide),
    source_yRow_eq_rowCompute 16 5 5 3 (by decide),
    source_yRow_eq_rowCompute 16 5 5 4 (by decide),
    source_yRow_eq_rowCompute 16 5 5 5 (by decide),
    source_yRow_eq_rowCompute 16 5 5 6 (by decide),
    computeRow_16_5_5_0, computeRow_16_5_5_1, computeRow_16_5_5_2, computeRow_16_5_5_3, computeRow_16_5_5_4, computeRow_16_5_5_5, computeRow_16_5_5_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_16_5_7 : Y 16 5 7 = (1549750421445905525422653/209715200000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 16 5 7 0 (by decide),
    source_yRow_eq_rowCompute 16 5 7 1 (by decide),
    source_yRow_eq_rowCompute 16 5 7 2 (by decide),
    source_yRow_eq_rowCompute 16 5 7 3 (by decide),
    source_yRow_eq_rowCompute 16 5 7 4 (by decide),
    source_yRow_eq_rowCompute 16 5 7 5 (by decide),
    source_yRow_eq_rowCompute 16 5 7 6 (by decide),
    computeRow_16_5_7_0, computeRow_16_5_7_1, computeRow_16_5_7_2, computeRow_16_5_7_3, computeRow_16_5_7_4, computeRow_16_5_7_5, computeRow_16_5_7_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_16_5_9 : Y 16 5 9 = (-611154627229412014141701/52428800000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 16 5 9 0 (by decide),
    source_yRow_eq_rowCompute 16 5 9 1 (by decide),
    source_yRow_eq_rowCompute 16 5 9 2 (by decide),
    source_yRow_eq_rowCompute 16 5 9 3 (by decide),
    source_yRow_eq_rowCompute 16 5 9 4 (by decide),
    source_yRow_eq_rowCompute 16 5 9 5 (by decide),
    source_yRow_eq_rowCompute 16 5 9 6 (by decide),
    computeRow_16_5_9_0, computeRow_16_5_9_1, computeRow_16_5_9_2, computeRow_16_5_9_3, computeRow_16_5_9_4, computeRow_16_5_9_5, computeRow_16_5_9_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_16_5_11 : Y 16 5 11 = (-578745616368603039939/41943040000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 16 5 11 0 (by decide),
    source_yRow_eq_rowCompute 16 5 11 1 (by decide),
    source_yRow_eq_rowCompute 16 5 11 2 (by decide),
    source_yRow_eq_rowCompute 16 5 11 3 (by decide),
    source_yRow_eq_rowCompute 16 5 11 4 (by decide),
    source_yRow_eq_rowCompute 16 5 11 5 (by decide),
    source_yRow_eq_rowCompute 16 5 11 6 (by decide),
    computeRow_16_5_11_0, computeRow_16_5_11_1, computeRow_16_5_11_2, computeRow_16_5_11_3, computeRow_16_5_11_4, computeRow_16_5_11_5, computeRow_16_5_11_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_16_5_13 : Y 16 5 13 = (-64505141078209101647091/1048576000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 16 5 13 0 (by decide),
    source_yRow_eq_rowCompute 16 5 13 1 (by decide),
    source_yRow_eq_rowCompute 16 5 13 2 (by decide),
    source_yRow_eq_rowCompute 16 5 13 3 (by decide),
    source_yRow_eq_rowCompute 16 5 13 4 (by decide),
    source_yRow_eq_rowCompute 16 5 13 5 (by decide),
    source_yRow_eq_rowCompute 16 5 13 6 (by decide),
    computeRow_16_5_13_0, computeRow_16_5_13_1, computeRow_16_5_13_2, computeRow_16_5_13_3, computeRow_16_5_13_4, computeRow_16_5_13_5, computeRow_16_5_13_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_16_5_15 : Y 16 5 15 = (-99002192076248555811717/524288000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 16 5 15 0 (by decide),
    source_yRow_eq_rowCompute 16 5 15 1 (by decide),
    source_yRow_eq_rowCompute 16 5 15 2 (by decide),
    source_yRow_eq_rowCompute 16 5 15 3 (by decide),
    source_yRow_eq_rowCompute 16 5 15 4 (by decide),
    source_yRow_eq_rowCompute 16 5 15 5 (by decide),
    source_yRow_eq_rowCompute 16 5 15 6 (by decide),
    computeRow_16_5_15_0, computeRow_16_5_15_1, computeRow_16_5_15_2, computeRow_16_5_15_3, computeRow_16_5_15_4, computeRow_16_5_15_5, computeRow_16_5_15_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_16_7_7 : Y 16 7 7 = (-11434119007650938281635057/524288000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 16 7 7 0 (by decide),
    source_yRow_eq_rowCompute 16 7 7 1 (by decide),
    source_yRow_eq_rowCompute 16 7 7 2 (by decide),
    source_yRow_eq_rowCompute 16 7 7 3 (by decide),
    source_yRow_eq_rowCompute 16 7 7 4 (by decide),
    source_yRow_eq_rowCompute 16 7 7 5 (by decide),
    source_yRow_eq_rowCompute 16 7 7 6 (by decide),
    computeRow_16_7_7_0, computeRow_16_7_7_1, computeRow_16_7_7_2, computeRow_16_7_7_3, computeRow_16_7_7_4, computeRow_16_7_7_5, computeRow_16_7_7_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_16_7_9 : Y 16 7 9 = (1484433801775108633948569/131072000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 16 7 9 0 (by decide),
    source_yRow_eq_rowCompute 16 7 9 1 (by decide),
    source_yRow_eq_rowCompute 16 7 9 2 (by decide),
    source_yRow_eq_rowCompute 16 7 9 3 (by decide),
    source_yRow_eq_rowCompute 16 7 9 4 (by decide),
    source_yRow_eq_rowCompute 16 7 9 5 (by decide),
    source_yRow_eq_rowCompute 16 7 9 6 (by decide),
    computeRow_16_7_9_0, computeRow_16_7_9_1, computeRow_16_7_9_2, computeRow_16_7_9_3, computeRow_16_7_9_4, computeRow_16_7_9_5, computeRow_16_7_9_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_16_7_11 : Y 16 7 11 = (207943103777772680639091/13107200000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 16 7 11 0 (by decide),
    source_yRow_eq_rowCompute 16 7 11 1 (by decide),
    source_yRow_eq_rowCompute 16 7 11 2 (by decide),
    source_yRow_eq_rowCompute 16 7 11 3 (by decide),
    source_yRow_eq_rowCompute 16 7 11 4 (by decide),
    source_yRow_eq_rowCompute 16 7 11 5 (by decide),
    source_yRow_eq_rowCompute 16 7 11 6 (by decide),
    computeRow_16_7_11_0, computeRow_16_7_11_1, computeRow_16_7_11_2, computeRow_16_7_11_3, computeRow_16_7_11_4, computeRow_16_7_11_5, computeRow_16_7_11_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_16_7_13 : Y 16 7 13 = (-8974467290230038089021529/65536000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 16 7 13 0 (by decide),
    source_yRow_eq_rowCompute 16 7 13 1 (by decide),
    source_yRow_eq_rowCompute 16 7 13 2 (by decide),
    source_yRow_eq_rowCompute 16 7 13 3 (by decide),
    source_yRow_eq_rowCompute 16 7 13 4 (by decide),
    source_yRow_eq_rowCompute 16 7 13 5 (by decide),
    source_yRow_eq_rowCompute 16 7 13 6 (by decide),
    computeRow_16_7_13_0, computeRow_16_7_13_1, computeRow_16_7_13_2, computeRow_16_7_13_3, computeRow_16_7_13_4, computeRow_16_7_13_5, computeRow_16_7_13_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_16_7_15 : Y 16 7 15 = (4777756237785689667105597/6553600000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 16 7 15 0 (by decide),
    source_yRow_eq_rowCompute 16 7 15 1 (by decide),
    source_yRow_eq_rowCompute 16 7 15 2 (by decide),
    source_yRow_eq_rowCompute 16 7 15 3 (by decide),
    source_yRow_eq_rowCompute 16 7 15 4 (by decide),
    source_yRow_eq_rowCompute 16 7 15 5 (by decide),
    source_yRow_eq_rowCompute 16 7 15 6 (by decide),
    computeRow_16_7_15_0, computeRow_16_7_15_1, computeRow_16_7_15_2, computeRow_16_7_15_3, computeRow_16_7_15_4, computeRow_16_7_15_5, computeRow_16_7_15_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_16_9_9 : Y 16 9 9 = (-621920505954394918130013/32768000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 16 9 9 0 (by decide),
    source_yRow_eq_rowCompute 16 9 9 1 (by decide),
    source_yRow_eq_rowCompute 16 9 9 2 (by decide),
    source_yRow_eq_rowCompute 16 9 9 3 (by decide),
    source_yRow_eq_rowCompute 16 9 9 4 (by decide),
    source_yRow_eq_rowCompute 16 9 9 5 (by decide),
    source_yRow_eq_rowCompute 16 9 9 6 (by decide),
    computeRow_16_9_9_0, computeRow_16_9_9_1, computeRow_16_9_9_2, computeRow_16_9_9_3, computeRow_16_9_9_4, computeRow_16_9_9_5, computeRow_16_9_9_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_16_9_11 : Y 16 9 11 = (-28769175431642817466911/3276800000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 16 9 11 0 (by decide),
    source_yRow_eq_rowCompute 16 9 11 1 (by decide),
    source_yRow_eq_rowCompute 16 9 11 2 (by decide),
    source_yRow_eq_rowCompute 16 9 11 3 (by decide),
    source_yRow_eq_rowCompute 16 9 11 4 (by decide),
    source_yRow_eq_rowCompute 16 9 11 5 (by decide),
    source_yRow_eq_rowCompute 16 9 11 6 (by decide),
    computeRow_16_9_11_0, computeRow_16_9_11_1, computeRow_16_9_11_2, computeRow_16_9_11_3, computeRow_16_9_11_4, computeRow_16_9_11_5, computeRow_16_9_11_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_16_9_13 : Y 16 9 13 = (1147904288009241919132977/16384000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 16 9 13 0 (by decide),
    source_yRow_eq_rowCompute 16 9 13 1 (by decide),
    source_yRow_eq_rowCompute 16 9 13 2 (by decide),
    source_yRow_eq_rowCompute 16 9 13 3 (by decide),
    source_yRow_eq_rowCompute 16 9 13 4 (by decide),
    source_yRow_eq_rowCompute 16 9 13 5 (by decide),
    source_yRow_eq_rowCompute 16 9 13 6 (by decide),
    computeRow_16_9_13_0, computeRow_16_9_13_1, computeRow_16_9_13_2, computeRow_16_9_13_3, computeRow_16_9_13_4, computeRow_16_9_13_5, computeRow_16_9_13_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_16_9_15 : Y 16 9 15 = (68877548037338038801803/1638400000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 16 9 15 0 (by decide),
    source_yRow_eq_rowCompute 16 9 15 1 (by decide),
    source_yRow_eq_rowCompute 16 9 15 2 (by decide),
    source_yRow_eq_rowCompute 16 9 15 3 (by decide),
    source_yRow_eq_rowCompute 16 9 15 4 (by decide),
    source_yRow_eq_rowCompute 16 9 15 5 (by decide),
    source_yRow_eq_rowCompute 16 9 15 6 (by decide),
    computeRow_16_9_15_0, computeRow_16_9_15_1, computeRow_16_9_15_2, computeRow_16_9_15_3, computeRow_16_9_15_4, computeRow_16_9_15_5, computeRow_16_9_15_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_16_11_11 : Y 16 11 11 = (-47586420975452552673183/1638400000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 16 11 11 0 (by decide),
    source_yRow_eq_rowCompute 16 11 11 1 (by decide),
    source_yRow_eq_rowCompute 16 11 11 2 (by decide),
    source_yRow_eq_rowCompute 16 11 11 3 (by decide),
    source_yRow_eq_rowCompute 16 11 11 4 (by decide),
    source_yRow_eq_rowCompute 16 11 11 5 (by decide),
    source_yRow_eq_rowCompute 16 11 11 6 (by decide),
    computeRow_16_11_11_0, computeRow_16_11_11_1, computeRow_16_11_11_2, computeRow_16_11_11_3, computeRow_16_11_11_4, computeRow_16_11_11_5, computeRow_16_11_11_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_16_11_13 : Y 16 11 13 = (189274484540778686288811/1638400000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 16 11 13 0 (by decide),
    source_yRow_eq_rowCompute 16 11 13 1 (by decide),
    source_yRow_eq_rowCompute 16 11 13 2 (by decide),
    source_yRow_eq_rowCompute 16 11 13 3 (by decide),
    source_yRow_eq_rowCompute 16 11 13 4 (by decide),
    source_yRow_eq_rowCompute 16 11 13 5 (by decide),
    source_yRow_eq_rowCompute 16 11 13 6 (by decide),
    computeRow_16_11_13_0, computeRow_16_11_13_1, computeRow_16_11_13_2, computeRow_16_11_13_3, computeRow_16_11_13_4, computeRow_16_11_13_5, computeRow_16_11_13_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_16_11_15 : Y 16 11 15 = (-71581303517955662317887/163840000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 16 11 15 0 (by decide),
    source_yRow_eq_rowCompute 16 11 15 1 (by decide),
    source_yRow_eq_rowCompute 16 11 15 2 (by decide),
    source_yRow_eq_rowCompute 16 11 15 3 (by decide),
    source_yRow_eq_rowCompute 16 11 15 4 (by decide),
    source_yRow_eq_rowCompute 16 11 15 5 (by decide),
    source_yRow_eq_rowCompute 16 11 15 6 (by decide),
    computeRow_16_11_15_0, computeRow_16_11_15_1, computeRow_16_11_15_2, computeRow_16_11_15_3, computeRow_16_11_15_4, computeRow_16_11_15_5, computeRow_16_11_15_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_16_13_13 : Y 16 13 13 = (-7689933670205658822668289/8192000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 16 13 13 0 (by decide),
    source_yRow_eq_rowCompute 16 13 13 1 (by decide),
    source_yRow_eq_rowCompute 16 13 13 2 (by decide),
    source_yRow_eq_rowCompute 16 13 13 3 (by decide),
    source_yRow_eq_rowCompute 16 13 13 4 (by decide),
    source_yRow_eq_rowCompute 16 13 13 5 (by decide),
    source_yRow_eq_rowCompute 16 13 13 6 (by decide),
    computeRow_16_13_13_0, computeRow_16_13_13_1, computeRow_16_13_13_2, computeRow_16_13_13_3, computeRow_16_13_13_4, computeRow_16_13_13_5, computeRow_16_13_13_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_16_13_15 : Y 16 13 15 = (384276867404942369454597/819200000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 16 13 15 0 (by decide),
    source_yRow_eq_rowCompute 16 13 15 1 (by decide),
    source_yRow_eq_rowCompute 16 13 15 2 (by decide),
    source_yRow_eq_rowCompute 16 13 15 3 (by decide),
    source_yRow_eq_rowCompute 16 13 15 4 (by decide),
    source_yRow_eq_rowCompute 16 13 15 5 (by decide),
    source_yRow_eq_rowCompute 16 13 15 6 (by decide),
    computeRow_16_13_15_0, computeRow_16_13_15_1, computeRow_16_13_15_2, computeRow_16_13_15_3, computeRow_16_13_15_4, computeRow_16_13_15_5, computeRow_16_13_15_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_16_15_15 : Y 16 15 15 = (-2280462391086995129495481/81920000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 16 15 15 0 (by decide),
    source_yRow_eq_rowCompute 16 15 15 1 (by decide),
    source_yRow_eq_rowCompute 16 15 15 2 (by decide),
    source_yRow_eq_rowCompute 16 15 15 3 (by decide),
    source_yRow_eq_rowCompute 16 15 15 4 (by decide),
    source_yRow_eq_rowCompute 16 15 15 5 (by decide),
    source_yRow_eq_rowCompute 16 15 15 6 (by decide),
    computeRow_16_15_15_0, computeRow_16_15_15_1, computeRow_16_15_15_2, computeRow_16_15_15_3, computeRow_16_15_15_4, computeRow_16_15_15_5, computeRow_16_15_15_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_gram_16_1_1 : Z 16 1 1 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_16_1_1

theorem source_gram_16_1_3 : Z 16 1 3 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_16_1_3

theorem source_gram_16_1_5 : Z 16 1 5 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_16_1_5

theorem source_gram_16_1_7 : Z 16 1 7 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_16_1_7

theorem source_gram_16_1_9 : Z 16 1 9 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_16_1_9

theorem source_gram_16_1_11 : Z 16 1 11 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_16_1_11

theorem source_gram_16_1_13 : Z 16 1 13 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_16_1_13

theorem source_gram_16_1_15 : Z 16 1 15 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_16_1_15

theorem source_gram_16_3_3 : Z 16 3 3 = (37362124800 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_16_3_3

theorem source_gram_16_3_5 : Z 16 3 5 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_16_3_5

theorem source_gram_16_3_7 : Z 16 3 7 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_16_3_7

theorem source_gram_16_3_9 : Z 16 3 9 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_16_3_9

theorem source_gram_16_3_11 : Z 16 3 11 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_16_3_11

theorem source_gram_16_3_13 : Z 16 3 13 = (-7005398400 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_16_3_13

theorem source_gram_16_3_15 : Z 16 3 15 = (102162060000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_16_3_15

theorem source_gram_16_5_5 : Z 16 5 5 = (4790016000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_16_5_5

theorem source_gram_16_5_7 : Z 16 5 7 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_16_5_7

theorem source_gram_16_5_9 : Z 16 5 9 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_16_5_9

theorem source_gram_16_5_11 : Z 16 5 11 = (-1496880000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_16_5_11

theorem source_gram_16_5_13 : Z 16 5 13 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_16_5_13

theorem source_gram_16_5_15 : Z 16 5 15 = (61297236000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_16_5_15

theorem source_gram_16_7_7 : Z 16 7 7 = (1828915200 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_16_7_7

theorem source_gram_16_7_9 : Z 16 7 9 = (-685843200 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_16_7_9

theorem source_gram_16_7_11 : Z 16 7 11 = (-1571724000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_16_7_11

theorem source_gram_16_7_13 : Z 16 7 13 = (4086482400 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_16_7_13

theorem source_gram_16_7_15 : Z 16 7 15 = (15324309000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_16_7_15

theorem source_gram_16_9_9 : Z 16 9 9 = (457228800 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_16_9_9

theorem source_gram_16_9_11 : Z 16 9 11 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_16_9_11

theorem source_gram_16_9_13 : Z 16 9 13 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_16_9_13

theorem source_gram_16_9_15 : Z 16 9 15 = (-10216206000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_16_9_15

theorem source_gram_16_11_11 : Z 16 11 11 = (3555090000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_16_11_11

theorem source_gram_16_11_13 : Z 16 11 13 = (-8027019000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_16_11_13

theorem source_gram_16_11_15 : Z 16 11 15 = (-19155386250 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_16_11_15

theorem source_gram_16_13_13 : Z 16 13 13 = (22183761600 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_16_13_13

theorem source_gram_16_13_15 : Z 16 13 15 = (-19155386250 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_16_13_15

theorem source_gram_16_15_15 : Z 16 15 15 = (2584061605125/2 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_16_15_15

theorem source_error_16_3_1 : Y 16 3 1 = (-39034614015379387104670971/13107200000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_16_1_3

theorem source_gram_16_3_1 : Z 16 3 1 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_16_1_3

theorem source_error_16_5_1 : Y 16 5 1 = (78202406241711463127687271/83886080000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_16_1_5

theorem source_gram_16_5_1 : Z 16 5 1 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_16_1_5

theorem source_error_16_5_3 : Y 16 5 3 = (2737552373685628655395239/41943040000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_16_3_5

theorem source_gram_16_5_3 : Z 16 5 3 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_16_3_5

theorem source_error_16_7_1 : Y 16 7 1 = (23832834670493732956060989/209715200000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_16_1_7

theorem source_gram_16_7_1 : Z 16 7 1 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_16_1_7

theorem source_error_16_7_3 : Y 16 7 3 = (22736583113602023500964129/524288000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_16_3_7

theorem source_gram_16_7_3 : Z 16 7 3 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_16_3_7

theorem source_error_16_7_5 : Y 16 7 5 = (1549750421445905525422653/209715200000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_16_5_7

theorem source_gram_16_7_5 : Z 16 7 5 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_16_5_7

theorem source_error_16_9_1 : Y 16 9 1 = (22048584820368310367604441/52428800000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_16_1_9

theorem source_gram_16_9_1 : Z 16 9 1 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_16_1_9

theorem source_error_16_9_3 : Y 16 9 3 = (1851780972244557042321633/131072000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_16_3_9

theorem source_gram_16_9_3 : Z 16 9 3 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_16_3_9

theorem source_error_16_9_5 : Y 16 9 5 = (-611154627229412014141701/52428800000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_16_5_9

theorem source_gram_16_9_5 : Z 16 9 5 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_16_5_9

theorem source_error_16_9_7 : Y 16 9 7 = (1484433801775108633948569/131072000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_16_7_9

theorem source_gram_16_9_7 : Z 16 9 7 = (-685843200 : ℚ) := by
  rw [Z_symm]
  exact source_gram_16_7_9

theorem source_error_16_11_1 : Y 16 11 1 = (2553473034802720354150827/26214400000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_16_1_11

theorem source_gram_16_11_1 : Z 16 11 1 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_16_1_11

theorem source_error_16_11_3 : Y 16 11 3 = (507618379345280460543/1310720000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_16_3_11

theorem source_gram_16_11_3 : Z 16 11 3 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_16_3_11

theorem source_error_16_11_5 : Y 16 11 5 = (-578745616368603039939/41943040000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_16_5_11

theorem source_gram_16_11_5 : Z 16 11 5 = (-1496880000 : ℚ) := by
  rw [Z_symm]
  exact source_gram_16_5_11

theorem source_error_16_11_7 : Y 16 11 7 = (207943103777772680639091/13107200000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_16_7_11

theorem source_gram_16_11_7 : Z 16 11 7 = (-1571724000 : ℚ) := by
  rw [Z_symm]
  exact source_gram_16_7_11

theorem source_error_16_11_9 : Y 16 11 9 = (-28769175431642817466911/3276800000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_16_9_11

theorem source_gram_16_11_9 : Z 16 11 9 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_16_9_11

theorem source_error_16_13_1 : Y 16 13 1 = (108255415269241130506236621/26214400000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_16_1_13

theorem source_gram_16_13_1 : Z 16 13 1 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_16_1_13

theorem source_error_16_13_3 : Y 16 13 3 = (32584839756386941473215337/65536000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_16_3_13

theorem source_gram_16_13_3 : Z 16 13 3 = (-7005398400 : ℚ) := by
  rw [Z_symm]
  exact source_gram_16_3_13

theorem source_error_16_13_5 : Y 16 13 5 = (-64505141078209101647091/1048576000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_16_5_13

theorem source_gram_16_13_5 : Z 16 13 5 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_16_5_13

theorem source_error_16_13_7 : Y 16 13 7 = (-8974467290230038089021529/65536000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_16_7_13

theorem source_gram_16_13_7 : Z 16 13 7 = (4086482400 : ℚ) := by
  rw [Z_symm]
  exact source_gram_16_7_13

theorem source_error_16_13_9 : Y 16 13 9 = (1147904288009241919132977/16384000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_16_9_13

theorem source_gram_16_13_9 : Z 16 13 9 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_16_9_13

theorem source_error_16_13_11 : Y 16 13 11 = (189274484540778686288811/1638400000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_16_11_13

theorem source_gram_16_13_11 : Z 16 13 11 = (-8027019000 : ℚ) := by
  rw [Z_symm]
  exact source_gram_16_11_13

theorem source_error_16_15_1 : Y 16 15 1 = (-41435755574383986458435793/2621440000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_16_1_15

theorem source_gram_16_15_1 : Z 16 15 1 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_16_1_15

theorem source_error_16_15_3 : Y 16 15 3 = (-12977256793584317385992841/6553600000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_16_3_15

theorem source_gram_16_15_3 : Z 16 15 3 = (102162060000 : ℚ) := by
  rw [Z_symm]
  exact source_gram_16_3_15

theorem source_error_16_15_5 : Y 16 15 5 = (-99002192076248555811717/524288000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_16_5_15

theorem source_gram_16_15_5 : Z 16 15 5 = (61297236000 : ℚ) := by
  rw [Z_symm]
  exact source_gram_16_5_15

theorem source_error_16_15_7 : Y 16 15 7 = (4777756237785689667105597/6553600000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_16_7_15

theorem source_gram_16_15_7 : Z 16 15 7 = (15324309000 : ℚ) := by
  rw [Z_symm]
  exact source_gram_16_7_15

theorem source_error_16_15_9 : Y 16 15 9 = (68877548037338038801803/1638400000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_16_9_15

theorem source_gram_16_15_9 : Z 16 15 9 = (-10216206000 : ℚ) := by
  rw [Z_symm]
  exact source_gram_16_9_15

theorem source_error_16_15_11 : Y 16 15 11 = (-71581303517955662317887/163840000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_16_11_15

theorem source_gram_16_15_11 : Z 16 15 11 = (-19155386250 : ℚ) := by
  rw [Z_symm]
  exact source_gram_16_11_15

theorem source_error_16_15_13 : Y 16 15 13 = (384276867404942369454597/819200000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_16_13_15

theorem source_gram_16_15_13 : Z 16 15 13 = (-19155386250 : ℚ) := by
  rw [Z_symm]
  exact source_gram_16_13_15

theorem error_16 : errorRational 16 = candidateY_16 := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact source_error_16_1_1
  · exact source_error_16_1_3
  · exact source_error_16_1_5
  · exact source_error_16_1_7
  · exact source_error_16_1_9
  · exact source_error_16_1_11
  · exact source_error_16_1_13
  · exact source_error_16_1_15
  · exact source_error_16_3_1
  · exact source_error_16_3_3
  · exact source_error_16_3_5
  · exact source_error_16_3_7
  · exact source_error_16_3_9
  · exact source_error_16_3_11
  · exact source_error_16_3_13
  · exact source_error_16_3_15
  · exact source_error_16_5_1
  · exact source_error_16_5_3
  · exact source_error_16_5_5
  · exact source_error_16_5_7
  · exact source_error_16_5_9
  · exact source_error_16_5_11
  · exact source_error_16_5_13
  · exact source_error_16_5_15
  · exact source_error_16_7_1
  · exact source_error_16_7_3
  · exact source_error_16_7_5
  · exact source_error_16_7_7
  · exact source_error_16_7_9
  · exact source_error_16_7_11
  · exact source_error_16_7_13
  · exact source_error_16_7_15
  · exact source_error_16_9_1
  · exact source_error_16_9_3
  · exact source_error_16_9_5
  · exact source_error_16_9_7
  · exact source_error_16_9_9
  · exact source_error_16_9_11
  · exact source_error_16_9_13
  · exact source_error_16_9_15
  · exact source_error_16_11_1
  · exact source_error_16_11_3
  · exact source_error_16_11_5
  · exact source_error_16_11_7
  · exact source_error_16_11_9
  · exact source_error_16_11_11
  · exact source_error_16_11_13
  · exact source_error_16_11_15
  · exact source_error_16_13_1
  · exact source_error_16_13_3
  · exact source_error_16_13_5
  · exact source_error_16_13_7
  · exact source_error_16_13_9
  · exact source_error_16_13_11
  · exact source_error_16_13_13
  · exact source_error_16_13_15
  · exact source_error_16_15_1
  · exact source_error_16_15_3
  · exact source_error_16_15_5
  · exact source_error_16_15_7
  · exact source_error_16_15_9
  · exact source_error_16_15_11
  · exact source_error_16_15_13
  · exact source_error_16_15_15

theorem gram_16 : gramRational 16 = candidateZ_16 := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact source_gram_16_1_1
  · exact source_gram_16_1_3
  · exact source_gram_16_1_5
  · exact source_gram_16_1_7
  · exact source_gram_16_1_9
  · exact source_gram_16_1_11
  · exact source_gram_16_1_13
  · exact source_gram_16_1_15
  · exact source_gram_16_3_1
  · exact source_gram_16_3_3
  · exact source_gram_16_3_5
  · exact source_gram_16_3_7
  · exact source_gram_16_3_9
  · exact source_gram_16_3_11
  · exact source_gram_16_3_13
  · exact source_gram_16_3_15
  · exact source_gram_16_5_1
  · exact source_gram_16_5_3
  · exact source_gram_16_5_5
  · exact source_gram_16_5_7
  · exact source_gram_16_5_9
  · exact source_gram_16_5_11
  · exact source_gram_16_5_13
  · exact source_gram_16_5_15
  · exact source_gram_16_7_1
  · exact source_gram_16_7_3
  · exact source_gram_16_7_5
  · exact source_gram_16_7_7
  · exact source_gram_16_7_9
  · exact source_gram_16_7_11
  · exact source_gram_16_7_13
  · exact source_gram_16_7_15
  · exact source_gram_16_9_1
  · exact source_gram_16_9_3
  · exact source_gram_16_9_5
  · exact source_gram_16_9_7
  · exact source_gram_16_9_9
  · exact source_gram_16_9_11
  · exact source_gram_16_9_13
  · exact source_gram_16_9_15
  · exact source_gram_16_11_1
  · exact source_gram_16_11_3
  · exact source_gram_16_11_5
  · exact source_gram_16_11_7
  · exact source_gram_16_11_9
  · exact source_gram_16_11_11
  · exact source_gram_16_11_13
  · exact source_gram_16_11_15
  · exact source_gram_16_13_1
  · exact source_gram_16_13_3
  · exact source_gram_16_13_5
  · exact source_gram_16_13_7
  · exact source_gram_16_13_9
  · exact source_gram_16_13_11
  · exact source_gram_16_13_13
  · exact source_gram_16_13_15
  · exact source_gram_16_15_1
  · exact source_gram_16_15_3
  · exact source_gram_16_15_5
  · exact source_gram_16_15_7
  · exact source_gram_16_15_9
  · exact source_gram_16_15_11
  · exact source_gram_16_15_13
  · exact source_gram_16_15_15

end Laughlin.Certificate

end OAI
