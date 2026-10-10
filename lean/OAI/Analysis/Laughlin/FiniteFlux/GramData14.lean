import OAI.Analysis.Laughlin.FiniteFlux.ComputeGram01Batch14
import OAI.Analysis.Laughlin.FiniteFlux.ComputeGram03Batch14
import OAI.Analysis.Laughlin.FiniteFlux.ComputeGram05Batch14
import OAI.Analysis.Laughlin.FiniteFlux.ComputeGram07Batch14
import OAI.Analysis.Laughlin.FiniteFlux.ComputeGram09Batch14
import OAI.Analysis.Laughlin.FiniteFlux.ComputeGram11Batch14
import OAI.Analysis.Laughlin.FiniteFlux.ComputeGram131314
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0101Batch14
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0103Batch14
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0105Batch14
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0107Batch14
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0109Batch14
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0111Batch14
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0113Batch14
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0303Batch14
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0305Batch14
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0307Batch14
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0309Batch14
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0311Batch14
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0313Batch14
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0505Batch14
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0507Batch14
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0509Batch14
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0511Batch14
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0513Batch14
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0707Batch14
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0709Batch14
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0711Batch14
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0713Batch14
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0909Batch14
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0911Batch14
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow0913Batch14
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow1111Batch14
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow1113Batch14
import OAI.Analysis.Laughlin.FiniteFlux.ComputeRow1313Batch14
import OAI.Analysis.Laughlin.FiniteFlux.Data14
import OAI.Analysis.Laughlin.FourBody.NumericBridge
import OAI.Analysis.Laughlin.FourBody.Symmetry

namespace OAI

namespace Laughlin.Certificate
theorem source_error_14_1_1 : Y 14 1 1 = (165377041672743964897444611/4194304000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 14 1 1 0 (by decide),
    source_yRow_eq_rowCompute 14 1 1 1 (by decide),
    source_yRow_eq_rowCompute 14 1 1 2 (by decide),
    source_yRow_eq_rowCompute 14 1 1 3 (by decide),
    source_yRow_eq_rowCompute 14 1 1 4 (by decide),
    source_yRow_eq_rowCompute 14 1 1 5 (by decide),
    source_yRow_eq_rowCompute 14 1 1 6 (by decide),
    computeRow_14_1_1_0, computeRow_14_1_1_1, computeRow_14_1_1_2, computeRow_14_1_1_3, computeRow_14_1_1_4, computeRow_14_1_1_5, computeRow_14_1_1_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_14_1_3 : Y 14 1 3 = (-99652836936417746642331957/4194304000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 14 1 3 0 (by decide),
    source_yRow_eq_rowCompute 14 1 3 1 (by decide),
    source_yRow_eq_rowCompute 14 1 3 2 (by decide),
    source_yRow_eq_rowCompute 14 1 3 3 (by decide),
    source_yRow_eq_rowCompute 14 1 3 4 (by decide),
    source_yRow_eq_rowCompute 14 1 3 5 (by decide),
    source_yRow_eq_rowCompute 14 1 3 6 (by decide),
    computeRow_14_1_3_0, computeRow_14_1_3_1, computeRow_14_1_3_2, computeRow_14_1_3_3, computeRow_14_1_3_4, computeRow_14_1_3_5, computeRow_14_1_3_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_14_1_5 : Y 14 1 5 = (198343656225197394663337443/8388608000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 14 1 5 0 (by decide),
    source_yRow_eq_rowCompute 14 1 5 1 (by decide),
    source_yRow_eq_rowCompute 14 1 5 2 (by decide),
    source_yRow_eq_rowCompute 14 1 5 3 (by decide),
    source_yRow_eq_rowCompute 14 1 5 4 (by decide),
    source_yRow_eq_rowCompute 14 1 5 5 (by decide),
    source_yRow_eq_rowCompute 14 1 5 6 (by decide),
    computeRow_14_1_5_0, computeRow_14_1_5_1, computeRow_14_1_5_2, computeRow_14_1_5_3, computeRow_14_1_5_4, computeRow_14_1_5_5, computeRow_14_1_5_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_14_1_7 : Y 14 1 7 = (-10805495312804179528323783/4194304000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 14 1 7 0 (by decide),
    source_yRow_eq_rowCompute 14 1 7 1 (by decide),
    source_yRow_eq_rowCompute 14 1 7 2 (by decide),
    source_yRow_eq_rowCompute 14 1 7 3 (by decide),
    source_yRow_eq_rowCompute 14 1 7 4 (by decide),
    source_yRow_eq_rowCompute 14 1 7 5 (by decide),
    source_yRow_eq_rowCompute 14 1 7 6 (by decide),
    computeRow_14_1_7_0, computeRow_14_1_7_1, computeRow_14_1_7_2, computeRow_14_1_7_3, computeRow_14_1_7_4, computeRow_14_1_7_5, computeRow_14_1_7_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_14_1_9 : Y 14 1 9 = (21398938288605875882996397/1048576000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 14 1 9 0 (by decide),
    source_yRow_eq_rowCompute 14 1 9 1 (by decide),
    source_yRow_eq_rowCompute 14 1 9 2 (by decide),
    source_yRow_eq_rowCompute 14 1 9 3 (by decide),
    source_yRow_eq_rowCompute 14 1 9 4 (by decide),
    source_yRow_eq_rowCompute 14 1 9 5 (by decide),
    source_yRow_eq_rowCompute 14 1 9 6 (by decide),
    computeRow_14_1_9_0, computeRow_14_1_9_1, computeRow_14_1_9_2, computeRow_14_1_9_3, computeRow_14_1_9_4, computeRow_14_1_9_5, computeRow_14_1_9_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_14_1_11 : Y 14 1 11 = (3160468299521670425437149/104857600000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 14 1 11 0 (by decide),
    source_yRow_eq_rowCompute 14 1 11 1 (by decide),
    source_yRow_eq_rowCompute 14 1 11 2 (by decide),
    source_yRow_eq_rowCompute 14 1 11 3 (by decide),
    source_yRow_eq_rowCompute 14 1 11 4 (by decide),
    source_yRow_eq_rowCompute 14 1 11 5 (by decide),
    source_yRow_eq_rowCompute 14 1 11 6 (by decide),
    computeRow_14_1_11_0, computeRow_14_1_11_1, computeRow_14_1_11_2, computeRow_14_1_11_3, computeRow_14_1_11_4, computeRow_14_1_11_5, computeRow_14_1_11_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_14_1_13 : Y 14 1 13 = (-12750872962864833675394659/524288000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 14 1 13 0 (by decide),
    source_yRow_eq_rowCompute 14 1 13 1 (by decide),
    source_yRow_eq_rowCompute 14 1 13 2 (by decide),
    source_yRow_eq_rowCompute 14 1 13 3 (by decide),
    source_yRow_eq_rowCompute 14 1 13 4 (by decide),
    source_yRow_eq_rowCompute 14 1 13 5 (by decide),
    source_yRow_eq_rowCompute 14 1 13 6 (by decide),
    computeRow_14_1_13_0, computeRow_14_1_13_1, computeRow_14_1_13_2, computeRow_14_1_13_3, computeRow_14_1_13_4, computeRow_14_1_13_5, computeRow_14_1_13_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_14_3_3 : Y 14 3 3 = (23310418524081657499377/524288000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 14 3 3 0 (by decide),
    source_yRow_eq_rowCompute 14 3 3 1 (by decide),
    source_yRow_eq_rowCompute 14 3 3 2 (by decide),
    source_yRow_eq_rowCompute 14 3 3 3 (by decide),
    source_yRow_eq_rowCompute 14 3 3 4 (by decide),
    source_yRow_eq_rowCompute 14 3 3 5 (by decide),
    source_yRow_eq_rowCompute 14 3 3 6 (by decide),
    computeRow_14_3_3_0, computeRow_14_3_3_1, computeRow_14_3_3_2, computeRow_14_3_3_3, computeRow_14_3_3_4, computeRow_14_3_3_5, computeRow_14_3_3_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_14_3_5 : Y 14 3 5 = (-347065711842922353039231/419430400000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 14 3 5 0 (by decide),
    source_yRow_eq_rowCompute 14 3 5 1 (by decide),
    source_yRow_eq_rowCompute 14 3 5 2 (by decide),
    source_yRow_eq_rowCompute 14 3 5 3 (by decide),
    source_yRow_eq_rowCompute 14 3 5 4 (by decide),
    source_yRow_eq_rowCompute 14 3 5 5 (by decide),
    source_yRow_eq_rowCompute 14 3 5 6 (by decide),
    computeRow_14_3_5_0, computeRow_14_3_5_1, computeRow_14_3_5_2, computeRow_14_3_5_3, computeRow_14_3_5_4, computeRow_14_3_5_5, computeRow_14_3_5_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_14_3_7 : Y 14 3 7 = (-138985253242272601987977/104857600000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 14 3 7 0 (by decide),
    source_yRow_eq_rowCompute 14 3 7 1 (by decide),
    source_yRow_eq_rowCompute 14 3 7 2 (by decide),
    source_yRow_eq_rowCompute 14 3 7 3 (by decide),
    source_yRow_eq_rowCompute 14 3 7 4 (by decide),
    source_yRow_eq_rowCompute 14 3 7 5 (by decide),
    source_yRow_eq_rowCompute 14 3 7 6 (by decide),
    computeRow_14_3_7_0, computeRow_14_3_7_1, computeRow_14_3_7_2, computeRow_14_3_7_3, computeRow_14_3_7_4, computeRow_14_3_7_5, computeRow_14_3_7_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_14_3_9 : Y 14 3 9 = (-567150585351068471238783/131072000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 14 3 9 0 (by decide),
    source_yRow_eq_rowCompute 14 3 9 1 (by decide),
    source_yRow_eq_rowCompute 14 3 9 2 (by decide),
    source_yRow_eq_rowCompute 14 3 9 3 (by decide),
    source_yRow_eq_rowCompute 14 3 9 4 (by decide),
    source_yRow_eq_rowCompute 14 3 9 5 (by decide),
    source_yRow_eq_rowCompute 14 3 9 6 (by decide),
    computeRow_14_3_9_0, computeRow_14_3_9_1, computeRow_14_3_9_2, computeRow_14_3_9_3, computeRow_14_3_9_4, computeRow_14_3_9_5, computeRow_14_3_9_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_14_3_11 : Y 14 3 11 = (-141724874857705188581763/32768000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 14 3 11 0 (by decide),
    source_yRow_eq_rowCompute 14 3 11 1 (by decide),
    source_yRow_eq_rowCompute 14 3 11 2 (by decide),
    source_yRow_eq_rowCompute 14 3 11 3 (by decide),
    source_yRow_eq_rowCompute 14 3 11 4 (by decide),
    source_yRow_eq_rowCompute 14 3 11 5 (by decide),
    source_yRow_eq_rowCompute 14 3 11 6 (by decide),
    computeRow_14_3_11_0, computeRow_14_3_11_1, computeRow_14_3_11_2, computeRow_14_3_11_3, computeRow_14_3_11_4, computeRow_14_3_11_5, computeRow_14_3_11_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_14_3_13 : Y 14 3 13 = (-841622022843306152134401/26214400000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 14 3 13 0 (by decide),
    source_yRow_eq_rowCompute 14 3 13 1 (by decide),
    source_yRow_eq_rowCompute 14 3 13 2 (by decide),
    source_yRow_eq_rowCompute 14 3 13 3 (by decide),
    source_yRow_eq_rowCompute 14 3 13 4 (by decide),
    source_yRow_eq_rowCompute 14 3 13 5 (by decide),
    source_yRow_eq_rowCompute 14 3 13 6 (by decide),
    computeRow_14_3_13_0, computeRow_14_3_13_1, computeRow_14_3_13_2, computeRow_14_3_13_3, computeRow_14_3_13_4, computeRow_14_3_13_5, computeRow_14_3_13_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_14_5_5 : Y 14 5 5 = (-948697485826720805007561/1677721600000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 14 5 5 0 (by decide),
    source_yRow_eq_rowCompute 14 5 5 1 (by decide),
    source_yRow_eq_rowCompute 14 5 5 2 (by decide),
    source_yRow_eq_rowCompute 14 5 5 3 (by decide),
    source_yRow_eq_rowCompute 14 5 5 4 (by decide),
    source_yRow_eq_rowCompute 14 5 5 5 (by decide),
    source_yRow_eq_rowCompute 14 5 5 6 (by decide),
    computeRow_14_5_5_0, computeRow_14_5_5_1, computeRow_14_5_5_2, computeRow_14_5_5_3, computeRow_14_5_5_4, computeRow_14_5_5_5, computeRow_14_5_5_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_14_5_7 : Y 14 5 7 = (1776603855966711095862153/4194304000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 14 5 7 0 (by decide),
    source_yRow_eq_rowCompute 14 5 7 1 (by decide),
    source_yRow_eq_rowCompute 14 5 7 2 (by decide),
    source_yRow_eq_rowCompute 14 5 7 3 (by decide),
    source_yRow_eq_rowCompute 14 5 7 4 (by decide),
    source_yRow_eq_rowCompute 14 5 7 5 (by decide),
    source_yRow_eq_rowCompute 14 5 7 6 (by decide),
    computeRow_14_5_7_0, computeRow_14_5_7_1, computeRow_14_5_7_2, computeRow_14_5_7_3, computeRow_14_5_7_4, computeRow_14_5_7_5, computeRow_14_5_7_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_14_5_9 : Y 14 5 9 = (932798387166894000074907/1048576000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 14 5 9 0 (by decide),
    source_yRow_eq_rowCompute 14 5 9 1 (by decide),
    source_yRow_eq_rowCompute 14 5 9 2 (by decide),
    source_yRow_eq_rowCompute 14 5 9 3 (by decide),
    source_yRow_eq_rowCompute 14 5 9 4 (by decide),
    source_yRow_eq_rowCompute 14 5 9 5 (by decide),
    source_yRow_eq_rowCompute 14 5 9 6 (by decide),
    computeRow_14_5_9_0, computeRow_14_5_9_1, computeRow_14_5_9_2, computeRow_14_5_9_3, computeRow_14_5_9_4, computeRow_14_5_9_5, computeRow_14_5_9_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_14_5_11 : Y 14 5 11 = (269131392507015595229211/524288000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 14 5 11 0 (by decide),
    source_yRow_eq_rowCompute 14 5 11 1 (by decide),
    source_yRow_eq_rowCompute 14 5 11 2 (by decide),
    source_yRow_eq_rowCompute 14 5 11 3 (by decide),
    source_yRow_eq_rowCompute 14 5 11 4 (by decide),
    source_yRow_eq_rowCompute 14 5 11 5 (by decide),
    source_yRow_eq_rowCompute 14 5 11 6 (by decide),
    computeRow_14_5_11_0, computeRow_14_5_11_1, computeRow_14_5_11_2, computeRow_14_5_11_3, computeRow_14_5_11_4, computeRow_14_5_11_5, computeRow_14_5_11_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_14_5_13 : Y 14 5 13 = (6370357421543107418633493/524288000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 14 5 13 0 (by decide),
    source_yRow_eq_rowCompute 14 5 13 1 (by decide),
    source_yRow_eq_rowCompute 14 5 13 2 (by decide),
    source_yRow_eq_rowCompute 14 5 13 3 (by decide),
    source_yRow_eq_rowCompute 14 5 13 4 (by decide),
    source_yRow_eq_rowCompute 14 5 13 5 (by decide),
    source_yRow_eq_rowCompute 14 5 13 6 (by decide),
    computeRow_14_5_13_0, computeRow_14_5_13_1, computeRow_14_5_13_2, computeRow_14_5_13_3, computeRow_14_5_13_4, computeRow_14_5_13_5, computeRow_14_5_13_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_14_7_7 : Y 14 7 7 = (-2225592748224580792706397/2097152000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 14 7 7 0 (by decide),
    source_yRow_eq_rowCompute 14 7 7 1 (by decide),
    source_yRow_eq_rowCompute 14 7 7 2 (by decide),
    source_yRow_eq_rowCompute 14 7 7 3 (by decide),
    source_yRow_eq_rowCompute 14 7 7 4 (by decide),
    source_yRow_eq_rowCompute 14 7 7 5 (by decide),
    source_yRow_eq_rowCompute 14 7 7 6 (by decide),
    computeRow_14_7_7_0, computeRow_14_7_7_1, computeRow_14_7_7_2, computeRow_14_7_7_3, computeRow_14_7_7_4, computeRow_14_7_7_5, computeRow_14_7_7_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_14_7_9 : Y 14 7 9 = (1701251773125333268329/20971520000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 14 7 9 0 (by decide),
    source_yRow_eq_rowCompute 14 7 9 1 (by decide),
    source_yRow_eq_rowCompute 14 7 9 2 (by decide),
    source_yRow_eq_rowCompute 14 7 9 3 (by decide),
    source_yRow_eq_rowCompute 14 7 9 4 (by decide),
    source_yRow_eq_rowCompute 14 7 9 5 (by decide),
    source_yRow_eq_rowCompute 14 7 9 6 (by decide),
    computeRow_14_7_9_0, computeRow_14_7_9_1, computeRow_14_7_9_2, computeRow_14_7_9_3, computeRow_14_7_9_4, computeRow_14_7_9_5, computeRow_14_7_9_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_14_7_11 : Y 14 7 11 = (-41108078112253038740007/52428800000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 14 7 11 0 (by decide),
    source_yRow_eq_rowCompute 14 7 11 1 (by decide),
    source_yRow_eq_rowCompute 14 7 11 2 (by decide),
    source_yRow_eq_rowCompute 14 7 11 3 (by decide),
    source_yRow_eq_rowCompute 14 7 11 4 (by decide),
    source_yRow_eq_rowCompute 14 7 11 5 (by decide),
    source_yRow_eq_rowCompute 14 7 11 6 (by decide),
    computeRow_14_7_11_0, computeRow_14_7_11_1, computeRow_14_7_11_2, computeRow_14_7_11_3, computeRow_14_7_11_4, computeRow_14_7_11_5, computeRow_14_7_11_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_14_7_13 : Y 14 7 13 = (-1332400286315383367619537/262144000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 14 7 13 0 (by decide),
    source_yRow_eq_rowCompute 14 7 13 1 (by decide),
    source_yRow_eq_rowCompute 14 7 13 2 (by decide),
    source_yRow_eq_rowCompute 14 7 13 3 (by decide),
    source_yRow_eq_rowCompute 14 7 13 4 (by decide),
    source_yRow_eq_rowCompute 14 7 13 5 (by decide),
    source_yRow_eq_rowCompute 14 7 13 6 (by decide),
    computeRow_14_7_13_0, computeRow_14_7_13_1, computeRow_14_7_13_2, computeRow_14_7_13_3, computeRow_14_7_13_4, computeRow_14_7_13_5, computeRow_14_7_13_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_14_9_9 : Y 14 9 9 = (1451654095595659568163/26214400000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 14 9 9 0 (by decide),
    source_yRow_eq_rowCompute 14 9 9 1 (by decide),
    source_yRow_eq_rowCompute 14 9 9 2 (by decide),
    source_yRow_eq_rowCompute 14 9 9 3 (by decide),
    source_yRow_eq_rowCompute 14 9 9 4 (by decide),
    source_yRow_eq_rowCompute 14 9 9 5 (by decide),
    source_yRow_eq_rowCompute 14 9 9 6 (by decide),
    computeRow_14_9_9_0, computeRow_14_9_9_1, computeRow_14_9_9_2, computeRow_14_9_9_3, computeRow_14_9_9_4, computeRow_14_9_9_5, computeRow_14_9_9_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_14_9_11 : Y 14 9 11 = (56731873890489317051103/65536000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 14 9 11 0 (by decide),
    source_yRow_eq_rowCompute 14 9 11 1 (by decide),
    source_yRow_eq_rowCompute 14 9 11 2 (by decide),
    source_yRow_eq_rowCompute 14 9 11 3 (by decide),
    source_yRow_eq_rowCompute 14 9 11 4 (by decide),
    source_yRow_eq_rowCompute 14 9 11 5 (by decide),
    source_yRow_eq_rowCompute 14 9 11 6 (by decide),
    computeRow_14_9_11_0, computeRow_14_9_11_1, computeRow_14_9_11_2, computeRow_14_9_11_3, computeRow_14_9_11_4, computeRow_14_9_11_5, computeRow_14_9_11_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_14_9_13 : Y 14 9 13 = (702921905295609015979677/65536000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 14 9 13 0 (by decide),
    source_yRow_eq_rowCompute 14 9 13 1 (by decide),
    source_yRow_eq_rowCompute 14 9 13 2 (by decide),
    source_yRow_eq_rowCompute 14 9 13 3 (by decide),
    source_yRow_eq_rowCompute 14 9 13 4 (by decide),
    source_yRow_eq_rowCompute 14 9 13 5 (by decide),
    source_yRow_eq_rowCompute 14 9 13 6 (by decide),
    computeRow_14_9_13_0, computeRow_14_9_13_1, computeRow_14_9_13_2, computeRow_14_9_13_3, computeRow_14_9_13_4, computeRow_14_9_13_5, computeRow_14_9_13_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_14_11_11 : Y 14 11 11 = (15883626629942625122019/32768000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 14 11 11 0 (by decide),
    source_yRow_eq_rowCompute 14 11 11 1 (by decide),
    source_yRow_eq_rowCompute 14 11 11 2 (by decide),
    source_yRow_eq_rowCompute 14 11 11 3 (by decide),
    source_yRow_eq_rowCompute 14 11 11 4 (by decide),
    source_yRow_eq_rowCompute 14 11 11 5 (by decide),
    source_yRow_eq_rowCompute 14 11 11 6 (by decide),
    computeRow_14_11_11_0, computeRow_14_11_11_1, computeRow_14_11_11_2, computeRow_14_11_11_3, computeRow_14_11_11_4, computeRow_14_11_11_5, computeRow_14_11_11_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_14_11_13 : Y 14 11 13 = (-304589521531696266272979/32768000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 14 11 13 0 (by decide),
    source_yRow_eq_rowCompute 14 11 13 1 (by decide),
    source_yRow_eq_rowCompute 14 11 13 2 (by decide),
    source_yRow_eq_rowCompute 14 11 13 3 (by decide),
    source_yRow_eq_rowCompute 14 11 13 4 (by decide),
    source_yRow_eq_rowCompute 14 11 13 5 (by decide),
    source_yRow_eq_rowCompute 14 11 13 6 (by decide),
    computeRow_14_11_13_0, computeRow_14_11_13_1, computeRow_14_11_13_2, computeRow_14_11_13_3, computeRow_14_11_13_4, computeRow_14_11_13_5, computeRow_14_11_13_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_14_13_13 : Y 14 13 13 = (-10250896235928348183825213/32768000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 14 13 13 0 (by decide),
    source_yRow_eq_rowCompute 14 13 13 1 (by decide),
    source_yRow_eq_rowCompute 14 13 13 2 (by decide),
    source_yRow_eq_rowCompute 14 13 13 3 (by decide),
    source_yRow_eq_rowCompute 14 13 13 4 (by decide),
    source_yRow_eq_rowCompute 14 13 13 5 (by decide),
    source_yRow_eq_rowCompute 14 13 13 6 (by decide),
    computeRow_14_13_13_0, computeRow_14_13_13_1, computeRow_14_13_13_2, computeRow_14_13_13_3, computeRow_14_13_13_4, computeRow_14_13_13_5, computeRow_14_13_13_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_gram_14_1_1 : Z 14 1 1 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_14_1_1

theorem source_gram_14_1_3 : Z 14 1 3 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_14_1_3

theorem source_gram_14_1_5 : Z 14 1 5 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_14_1_5

theorem source_gram_14_1_7 : Z 14 1 7 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_14_1_7

theorem source_gram_14_1_9 : Z 14 1 9 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_14_1_9

theorem source_gram_14_1_11 : Z 14 1 11 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_14_1_11

theorem source_gram_14_1_13 : Z 14 1 13 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_14_1_13

theorem source_gram_14_3_3 : Z 14 3 3 = (239500800 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_14_3_3

theorem source_gram_14_3_5 : Z 14 3 5 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_14_3_5

theorem source_gram_14_3_7 : Z 14 3 7 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_14_3_7

theorem source_gram_14_3_9 : Z 14 3 9 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_14_3_9

theorem source_gram_14_3_11 : Z 14 3 11 = (-74844000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_14_3_11

theorem source_gram_14_3_13 : Z 14 3 13 = (778377600 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_14_3_13

theorem source_gram_14_5_5 : Z 14 5 5 = (43545600 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_14_5_5

theorem source_gram_14_5_7 : Z 14 5 7 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_14_5_7

theorem source_gram_14_5_9 : Z 14 5 9 = (-21772800 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_14_5_9

theorem source_gram_14_5_11 : Z 14 5 11 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_14_5_11

theorem source_gram_14_5_13 : Z 14 5 13 = (389188800 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_14_5_13

theorem source_gram_14_7_7 : Z 14 7 7 = (11113200 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_14_7_7

theorem source_gram_14_7_9 : Z 14 7 9 = (-19051200 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_14_7_9

theorem source_gram_14_7_11 : Z 14 7 11 = (26195400 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_14_7_11

theorem source_gram_14_7_13 : Z 14 7 13 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_14_7_13

theorem source_gram_14_9_9 : Z 14 9 9 = (43545600 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_14_9_9

theorem source_gram_14_9_11 : Z 14 9 11 = (-44906400 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_14_9_11

theorem source_gram_14_9_13 : Z 14 9 13 = (-194594400 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_14_9_13

theorem source_gram_14_11_11 : Z 14 11 11 = (85135050 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_14_11_11

theorem source_gram_14_11_13 : Z 14 11 13 = (-243243000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_14_11_13

theorem source_gram_14_13_13 : Z 14 13 13 = (6008102100 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_14_13_13

theorem source_error_14_3_1 : Y 14 3 1 = (-99652836936417746642331957/4194304000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_14_1_3

theorem source_gram_14_3_1 : Z 14 3 1 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_14_1_3

theorem source_error_14_5_1 : Y 14 5 1 = (198343656225197394663337443/8388608000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_14_1_5

theorem source_gram_14_5_1 : Z 14 5 1 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_14_1_5

theorem source_error_14_5_3 : Y 14 5 3 = (-347065711842922353039231/419430400000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_14_3_5

theorem source_gram_14_5_3 : Z 14 5 3 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_14_3_5

theorem source_error_14_7_1 : Y 14 7 1 = (-10805495312804179528323783/4194304000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_14_1_7

theorem source_gram_14_7_1 : Z 14 7 1 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_14_1_7

theorem source_error_14_7_3 : Y 14 7 3 = (-138985253242272601987977/104857600000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_14_3_7

theorem source_gram_14_7_3 : Z 14 7 3 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_14_3_7

theorem source_error_14_7_5 : Y 14 7 5 = (1776603855966711095862153/4194304000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_14_5_7

theorem source_gram_14_7_5 : Z 14 7 5 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_14_5_7

theorem source_error_14_9_1 : Y 14 9 1 = (21398938288605875882996397/1048576000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_14_1_9

theorem source_gram_14_9_1 : Z 14 9 1 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_14_1_9

theorem source_error_14_9_3 : Y 14 9 3 = (-567150585351068471238783/131072000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_14_3_9

theorem source_gram_14_9_3 : Z 14 9 3 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_14_3_9

theorem source_error_14_9_5 : Y 14 9 5 = (932798387166894000074907/1048576000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_14_5_9

theorem source_gram_14_9_5 : Z 14 9 5 = (-21772800 : ℚ) := by
  rw [Z_symm]
  exact source_gram_14_5_9

theorem source_error_14_9_7 : Y 14 9 7 = (1701251773125333268329/20971520000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_14_7_9

theorem source_gram_14_9_7 : Z 14 9 7 = (-19051200 : ℚ) := by
  rw [Z_symm]
  exact source_gram_14_7_9

theorem source_error_14_11_1 : Y 14 11 1 = (3160468299521670425437149/104857600000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_14_1_11

theorem source_gram_14_11_1 : Z 14 11 1 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_14_1_11

theorem source_error_14_11_3 : Y 14 11 3 = (-141724874857705188581763/32768000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_14_3_11

theorem source_gram_14_11_3 : Z 14 11 3 = (-74844000 : ℚ) := by
  rw [Z_symm]
  exact source_gram_14_3_11

theorem source_error_14_11_5 : Y 14 11 5 = (269131392507015595229211/524288000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_14_5_11

theorem source_gram_14_11_5 : Z 14 11 5 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_14_5_11

theorem source_error_14_11_7 : Y 14 11 7 = (-41108078112253038740007/52428800000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_14_7_11

theorem source_gram_14_11_7 : Z 14 11 7 = (26195400 : ℚ) := by
  rw [Z_symm]
  exact source_gram_14_7_11

theorem source_error_14_11_9 : Y 14 11 9 = (56731873890489317051103/65536000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_14_9_11

theorem source_gram_14_11_9 : Z 14 11 9 = (-44906400 : ℚ) := by
  rw [Z_symm]
  exact source_gram_14_9_11

theorem source_error_14_13_1 : Y 14 13 1 = (-12750872962864833675394659/524288000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_14_1_13

theorem source_gram_14_13_1 : Z 14 13 1 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_14_1_13

theorem source_error_14_13_3 : Y 14 13 3 = (-841622022843306152134401/26214400000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_14_3_13

theorem source_gram_14_13_3 : Z 14 13 3 = (778377600 : ℚ) := by
  rw [Z_symm]
  exact source_gram_14_3_13

theorem source_error_14_13_5 : Y 14 13 5 = (6370357421543107418633493/524288000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_14_5_13

theorem source_gram_14_13_5 : Z 14 13 5 = (389188800 : ℚ) := by
  rw [Z_symm]
  exact source_gram_14_5_13

theorem source_error_14_13_7 : Y 14 13 7 = (-1332400286315383367619537/262144000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_14_7_13

theorem source_gram_14_13_7 : Z 14 13 7 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_14_7_13

theorem source_error_14_13_9 : Y 14 13 9 = (702921905295609015979677/65536000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_14_9_13

theorem source_gram_14_13_9 : Z 14 13 9 = (-194594400 : ℚ) := by
  rw [Z_symm]
  exact source_gram_14_9_13

theorem source_error_14_13_11 : Y 14 13 11 = (-304589521531696266272979/32768000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_14_11_13

theorem source_gram_14_13_11 : Z 14 13 11 = (-243243000 : ℚ) := by
  rw [Z_symm]
  exact source_gram_14_11_13

theorem error_14 : errorRational 14 = candidateY_14 := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact source_error_14_1_1
  · exact source_error_14_1_3
  · exact source_error_14_1_5
  · exact source_error_14_1_7
  · exact source_error_14_1_9
  · exact source_error_14_1_11
  · exact source_error_14_1_13
  · exact source_error_14_3_1
  · exact source_error_14_3_3
  · exact source_error_14_3_5
  · exact source_error_14_3_7
  · exact source_error_14_3_9
  · exact source_error_14_3_11
  · exact source_error_14_3_13
  · exact source_error_14_5_1
  · exact source_error_14_5_3
  · exact source_error_14_5_5
  · exact source_error_14_5_7
  · exact source_error_14_5_9
  · exact source_error_14_5_11
  · exact source_error_14_5_13
  · exact source_error_14_7_1
  · exact source_error_14_7_3
  · exact source_error_14_7_5
  · exact source_error_14_7_7
  · exact source_error_14_7_9
  · exact source_error_14_7_11
  · exact source_error_14_7_13
  · exact source_error_14_9_1
  · exact source_error_14_9_3
  · exact source_error_14_9_5
  · exact source_error_14_9_7
  · exact source_error_14_9_9
  · exact source_error_14_9_11
  · exact source_error_14_9_13
  · exact source_error_14_11_1
  · exact source_error_14_11_3
  · exact source_error_14_11_5
  · exact source_error_14_11_7
  · exact source_error_14_11_9
  · exact source_error_14_11_11
  · exact source_error_14_11_13
  · exact source_error_14_13_1
  · exact source_error_14_13_3
  · exact source_error_14_13_5
  · exact source_error_14_13_7
  · exact source_error_14_13_9
  · exact source_error_14_13_11
  · exact source_error_14_13_13

theorem gram_14 : gramRational 14 = candidateZ_14 := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact source_gram_14_1_1
  · exact source_gram_14_1_3
  · exact source_gram_14_1_5
  · exact source_gram_14_1_7
  · exact source_gram_14_1_9
  · exact source_gram_14_1_11
  · exact source_gram_14_1_13
  · exact source_gram_14_3_1
  · exact source_gram_14_3_3
  · exact source_gram_14_3_5
  · exact source_gram_14_3_7
  · exact source_gram_14_3_9
  · exact source_gram_14_3_11
  · exact source_gram_14_3_13
  · exact source_gram_14_5_1
  · exact source_gram_14_5_3
  · exact source_gram_14_5_5
  · exact source_gram_14_5_7
  · exact source_gram_14_5_9
  · exact source_gram_14_5_11
  · exact source_gram_14_5_13
  · exact source_gram_14_7_1
  · exact source_gram_14_7_3
  · exact source_gram_14_7_5
  · exact source_gram_14_7_7
  · exact source_gram_14_7_9
  · exact source_gram_14_7_11
  · exact source_gram_14_7_13
  · exact source_gram_14_9_1
  · exact source_gram_14_9_3
  · exact source_gram_14_9_5
  · exact source_gram_14_9_7
  · exact source_gram_14_9_9
  · exact source_gram_14_9_11
  · exact source_gram_14_9_13
  · exact source_gram_14_11_1
  · exact source_gram_14_11_3
  · exact source_gram_14_11_5
  · exact source_gram_14_11_7
  · exact source_gram_14_11_9
  · exact source_gram_14_11_11
  · exact source_gram_14_11_13
  · exact source_gram_14_13_1
  · exact source_gram_14_13_3
  · exact source_gram_14_13_5
  · exact source_gram_14_13_7
  · exact source_gram_14_13_9
  · exact source_gram_14_13_11
  · exact source_gram_14_13_13

end Laughlin.Certificate

end OAI
