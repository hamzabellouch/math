import OAI.Combinatorics.HoneycombChords.YangBaxterPolynomialsPositive
import OAI.Combinatorics.HoneycombChords.YangBaxterPolynomialsZero
import OAI.Combinatorics.HoneycombChords.YangBaxterPolynomialsNegative
import OAI.Combinatorics.HoneycombChords.YangBaxterSupport
import Mathlib.Tactic.FinCases

namespace OAI

/-! Yang–Baxter components with first spin negative.

This development follows the finite strip transfer calculation for critical honeycomb
walks in the companion paper on uniform marked polygon estimates. -/


namespace CriticalHoneycomb.Transfer.YangBaxter
open scoped BigOperators

section Algebra
variable (C A S x y z w ii : ℂ)
variable (hC : C = (2*S+1)*A) (hA : A^2 = (1-S)/2)
  (hS : S^2 = 1/2) (hy : y^2+x^2=1) (hw : w^2+z^2=1) (hi : ii^2+1=0)

include hC hA hS hy hw hi in
lemma component_200002 :
    leftComponent C A S x y z w ii 2 0 0 0 0 2 =
    rightComponent C A S x y z w ii 2 0 0 0 0 2 := by
  simp only [leftComponent, rightComponent, Fin.sum_univ_three, numerator, Fin.val_zero, Fin.val_one, finThreeTwo, mul_zero, zero_mul, zero_add, add_zero]
  have hp := polynomial_200002 C A S x y z w ii hC hA hS hy hw hi
  dsimp only [poly_200002_0, complexAdd, complexMul, complexPow] at hp
  linear_combination hp

include hC hA hS hy hw hi in
lemma component_200011 :
    leftComponent C A S x y z w ii 2 0 0 0 1 1 =
    rightComponent C A S x y z w ii 2 0 0 0 1 1 := by
  simp only [leftComponent, rightComponent, Fin.sum_univ_three, numerator, Fin.val_zero, Fin.val_one, finThreeTwo, mul_zero, zero_mul, zero_add, add_zero]
  have hp := polynomial_200011 C A S x y z w ii hC hA hS hy hw hi
  dsimp only [poly_200011_0, complexAdd, complexMul, complexPow] at hp
  linear_combination hp

include hC hA hS hy hw hi in
lemma component_201012 :
    leftComponent C A S x y z w ii 2 0 1 0 1 2 =
    rightComponent C A S x y z w ii 2 0 1 0 1 2 := by
  simp only [leftComponent, rightComponent, Fin.sum_univ_three, numerator, Fin.val_zero, Fin.val_one, finThreeTwo, mul_zero, zero_mul, zero_add, add_zero]
  have hp := polynomial_201012 C A S x y z w ii hC hA hS hy hw hi
  dsimp only [poly_201012_0, complexAdd, complexMul, complexPow] at hp
  linear_combination hp

include hC hA hS hy hw hi in
lemma component_200020 :
    leftComponent C A S x y z w ii 2 0 0 0 2 0 =
    rightComponent C A S x y z w ii 2 0 0 0 2 0 := by
  simp only [leftComponent, rightComponent, Fin.sum_univ_three, numerator, Fin.val_zero, Fin.val_one, finThreeTwo, mul_zero, zero_mul, zero_add, add_zero]
  have hp := polynomial_002020 C A S x y z w ii hC hA hS hy hw hi
  dsimp only [poly_002020_0, complexAdd, complexMul, complexPow] at hp
  linear_combination (-1:ℂ)/1*hp

include hC hA hS hy hw in
lemma component_200101 :
    leftComponent C A S x y z w ii 2 0 0 1 0 1 =
    rightComponent C A S x y z w ii 2 0 0 1 0 1 := by
  simp only [leftComponent, rightComponent, Fin.sum_univ_three, numerator, Fin.val_zero, Fin.val_one, finThreeTwo, mul_zero, zero_mul, zero_add, add_zero]
  have hp := polynomial_121022 C A S x y z w ii hC hA hS hy hw
  dsimp only [poly_121022_0, complexAdd, complexMul, complexPow] at hp
  linear_combination (-1:ℂ)/1*hp

include hC hA hS hy hw in
lemma component_200110 :
    leftComponent C A S x y z w ii 2 0 0 1 1 0 =
    rightComponent C A S x y z w ii 2 0 0 1 1 0 := by
  simp only [leftComponent, rightComponent, Fin.sum_univ_three, numerator, Fin.val_zero, Fin.val_one, finThreeTwo, mul_zero, zero_mul, zero_add, add_zero]
  have hp := polynomial_112022 C A S x y z w ii hC hA hS hy hw
  dsimp only [poly_112022_0, complexAdd, complexMul, complexPow] at hp
  linear_combination (-1:ℂ)/1*hp

include hC hA hS hy hw hi in
lemma component_201102 :
    leftComponent C A S x y z w ii 2 0 1 1 0 2 =
    rightComponent C A S x y z w ii 2 0 1 1 0 2 := by
  simp only [leftComponent, rightComponent, Fin.sum_univ_three, numerator, Fin.val_zero, Fin.val_one, finThreeTwo, mul_zero, zero_mul, zero_add, add_zero]
  have hp := polynomial_120021 C A S x y z w ii hC hA hS hy hw hi
  dsimp only [poly_120021_0, complexAdd, complexMul, complexPow] at hp
  linear_combination (-1:ℂ)/1*hp

include hC hA hS hy hw hi in
lemma component_201111 :
    leftComponent C A S x y z w ii 2 0 1 1 1 1 =
    rightComponent C A S x y z w ii 2 0 1 1 1 1 := by
  simp only [leftComponent, rightComponent, Fin.sum_univ_three, numerator, Fin.val_zero, Fin.val_one, finThreeTwo, mul_zero, zero_mul, zero_add, add_zero]
  have hp := polynomial_111021 C A S x y z w ii hC hA hS hy hw hi
  dsimp only [poly_111021_0, complexAdd, complexMul, complexPow] at hp
  linear_combination (-1:ℂ)/1*hp

include hC hA hS hy hw hi in
lemma component_201120 :
    leftComponent C A S x y z w ii 2 0 1 1 2 0 =
    rightComponent C A S x y z w ii 2 0 1 1 2 0 := by
  simp only [leftComponent, rightComponent, Fin.sum_univ_three, numerator, Fin.val_zero, Fin.val_one, finThreeTwo, mul_zero, zero_mul, zero_add, add_zero]
  have hp := polynomial_021102 C A S x y z w ii hC hA hS hy hw hi
  dsimp only [poly_021102_0, complexAdd, complexMul, complexPow] at hp
  linear_combination (1:ℂ)/1*hp

include hC hA hS hy hw hi in
lemma component_201210 :
    leftComponent C A S x y z w ii 2 0 1 2 1 0 =
    rightComponent C A S x y z w ii 2 0 1 2 1 0 := by
  simp only [leftComponent, rightComponent, Fin.sum_univ_three, numerator, Fin.val_zero, Fin.val_one, finThreeTwo, mul_zero, zero_mul, zero_add, add_zero]
  have hp := polynomial_012021 C A S x y z w ii hC hA hS hy hw hi
  dsimp only [poly_012021_0, complexAdd, complexMul, complexPow] at hp
  linear_combination (-1:ℂ)/1*hp

include hC hA hS hy hw hi in
lemma component_202022 :
    leftComponent C A S x y z w ii 2 0 2 0 2 2 =
    rightComponent C A S x y z w ii 2 0 2 0 2 2 := by
  simp only [leftComponent, rightComponent, Fin.sum_univ_three, numerator, Fin.val_zero, Fin.val_one, finThreeTwo, mul_zero, zero_mul, zero_add, add_zero]
  have hp := polynomial_002020 C A S x y z w ii hC hA hS hy hw hi
  dsimp only [poly_002020_0, complexAdd, complexMul, complexPow] at hp
  linear_combination (1:ℂ)/1*hp

include hC hA hS hy hw hi in
lemma component_202112 :
    leftComponent C A S x y z w ii 2 0 2 1 1 2 =
    rightComponent C A S x y z w ii 2 0 2 1 1 2 := by
  simp only [leftComponent, rightComponent, Fin.sum_univ_three, numerator, Fin.val_zero, Fin.val_one, finThreeTwo, mul_zero, zero_mul, zero_add, add_zero]
  have hp := polynomial_110020 C A S x y z w ii hC hA hS hy hw hi
  dsimp only [poly_110020_0, complexAdd, complexMul, complexPow] at hp
  linear_combination (-1:ℂ)/1*hp

include hC hA hS hy hw hi in
lemma component_202121 :
    leftComponent C A S x y z w ii 2 0 2 1 2 1 =
    rightComponent C A S x y z w ii 2 0 2 1 2 1 := by
  simp only [leftComponent, rightComponent, Fin.sum_univ_three, numerator, Fin.val_zero, Fin.val_one, finThreeTwo, mul_zero, zero_mul, zero_add, add_zero]
  have hp := polynomial_101020 C A S x y z w ii hC hA hS hy hw hi
  dsimp only [poly_101020_0, complexAdd, complexMul, complexPow] at hp
  linear_combination (-1:ℂ)/1*hp

include hC hA hS hy hw hi in
lemma component_202202 :
    leftComponent C A S x y z w ii 2 0 2 2 0 2 =
    rightComponent C A S x y z w ii 2 0 2 2 0 2 := by
  simp only [leftComponent, rightComponent, Fin.sum_univ_three, numerator, Fin.val_zero, Fin.val_one, finThreeTwo, mul_zero, zero_mul, zero_add, add_zero]
  have hp := polynomial_020020 C A S x y z w ii hC hA hS hy hw hi
  dsimp only [poly_020020_0, complexAdd, complexMul, complexPow] at hp
  linear_combination (-1:ℂ)/1*hp

include hC hA hS hy hw hi in
lemma component_202211 :
    leftComponent C A S x y z w ii 2 0 2 2 1 1 =
    rightComponent C A S x y z w ii 2 0 2 2 1 1 := by
  simp only [leftComponent, rightComponent, Fin.sum_univ_three, numerator, Fin.val_zero, Fin.val_one, finThreeTwo, mul_zero, zero_mul, zero_add, add_zero]
  have hp := polynomial_011020 C A S x y z w ii hC hA hS hy hw hi
  dsimp only [poly_011020_0, complexAdd, complexMul, complexPow] at hp
  linear_combination (-1:ℂ)/1*hp

include hC hA hS hy hw hi in
lemma component_202220 :
    leftComponent C A S x y z w ii 2 0 2 2 2 0 =
    rightComponent C A S x y z w ii 2 0 2 2 2 0 := by
  simp only [leftComponent, rightComponent, Fin.sum_univ_three, numerator, Fin.val_zero, Fin.val_one, finThreeTwo, mul_zero, zero_mul, zero_add, add_zero]
  have hp := polynomial_002020 C A S x y z w ii hC hA hS hy hw hi
  dsimp only [poly_002020_0, complexAdd, complexMul, complexPow] at hp
  linear_combination (-1:ℂ)/1*hp

include hC hA hS hy hw hi in
lemma component_210021 :
    leftComponent C A S x y z w ii 2 1 0 0 2 1 =
    rightComponent C A S x y z w ii 2 1 0 0 2 1 := by
  simp only [leftComponent, rightComponent, Fin.sum_univ_three, numerator, Fin.val_zero, Fin.val_one, finThreeTwo, mul_zero, zero_mul, zero_add, add_zero]
  have hp := polynomial_201012 C A S x y z w ii hC hA hS hy hw hi
  dsimp only [poly_201012_0, complexAdd, complexMul, complexPow] at hp
  linear_combination (-1:ℂ)/1*hp

include hC hA hS hy hw hi in
lemma component_210102 :
    leftComponent C A S x y z w ii 2 1 0 1 0 2 =
    rightComponent C A S x y z w ii 2 1 0 1 0 2 := by
  simp only [leftComponent, rightComponent, Fin.sum_univ_three, numerator, Fin.val_zero, Fin.val_one, finThreeTwo, mul_zero, zero_mul, zero_add, add_zero]
  have hp := polynomial_120012 C A S x y z w ii hC hA hS hy hw hi
  dsimp only [poly_120012_0, complexAdd, complexMul, complexPow] at hp
  linear_combination (-1:ℂ)/1*hp

include hC hA hS hy hw in
lemma component_210111 :
    leftComponent C A S x y z w ii 2 1 0 1 1 1 =
    rightComponent C A S x y z w ii 2 1 0 1 1 1 := by
  simp only [leftComponent, rightComponent, Fin.sum_univ_three, numerator, Fin.val_zero, Fin.val_one, finThreeTwo, mul_zero, zero_mul, zero_add, add_zero]
  have hp := polynomial_111012 C A S x y z w ii hC hA hS hy hw
  dsimp only [poly_111012_0, complexAdd, complexMul, complexPow] at hp
  linear_combination (-1:ℂ)/1*hp

include hC hA hS hy hw hi in
lemma component_210120 :
    leftComponent C A S x y z w ii 2 1 0 1 2 0 =
    rightComponent C A S x y z w ii 2 1 0 1 2 0 := by
  simp only [leftComponent, rightComponent, Fin.sum_univ_three, numerator, Fin.val_zero, Fin.val_one, finThreeTwo, mul_zero, zero_mul, zero_add, add_zero]
  have hp := polynomial_012102 C A S x y z w ii hC hA hS hy hw hi
  dsimp only [poly_012102_0, complexAdd, complexMul, complexPow] at hp
  linear_combination (1:ℂ)/1*hp

include hC hA hS hy hw hi in
lemma component_210201 :
    leftComponent C A S x y z w ii 2 1 0 2 0 1 =
    rightComponent C A S x y z w ii 2 1 0 2 0 1 := by
  simp only [leftComponent, rightComponent, Fin.sum_univ_three, numerator, Fin.val_zero, Fin.val_one, finThreeTwo, mul_zero, zero_mul, zero_add, add_zero]
  have hp := polynomial_012021 C A S x y z w ii hC hA hS hy hw hi
  dsimp only [poly_012021_0, complexAdd, complexMul, complexPow] at hp
  linear_combination (1:ℂ)/1*hp

include hC hA hS hy hw hi in
lemma component_211022 :
    leftComponent C A S x y z w ii 2 1 1 0 2 2 =
    rightComponent C A S x y z w ii 2 1 1 0 2 2 := by
  simp only [leftComponent, rightComponent, Fin.sum_univ_three, numerator, Fin.val_zero, Fin.val_one, finThreeTwo, mul_zero, zero_mul, zero_add, add_zero]
  have hp := polynomial_200011 C A S x y z w ii hC hA hS hy hw hi
  dsimp only [poly_200011_0, complexAdd, complexMul, complexPow] at hp
  linear_combination (-1:ℂ)/1*hp

include hC hA hS hy hw hi in
lemma component_211112 :
    leftComponent C A S x y z w ii 2 1 1 1 1 2 =
    rightComponent C A S x y z w ii 2 1 1 1 1 2 := by
  simp only [leftComponent, rightComponent, Fin.sum_univ_three, numerator, Fin.val_zero, Fin.val_one, finThreeTwo, mul_zero, zero_mul, zero_add, add_zero]
  have hp := polynomial_110011 C A S x y z w ii hC hA hS hy hw hi
  dsimp only [poly_110011_0, complexAdd, complexMul, complexPow] at hp
  linear_combination (-1:ℂ)/1*hp

include hC hA hS hy hw hi in
lemma component_211121 :
    leftComponent C A S x y z w ii 2 1 1 1 2 1 =
    rightComponent C A S x y z w ii 2 1 1 1 2 1 := by
  simp only [leftComponent, rightComponent, Fin.sum_univ_three, numerator, Fin.val_zero, Fin.val_one, finThreeTwo, mul_zero, zero_mul, zero_add, add_zero]
  have hp := polynomial_011101 C A S x y z w ii hC hA hS hy hw hi
  dsimp only [poly_011101_0, complexAdd, complexMul, complexPow] at hp
  linear_combination (1:ℂ)/1*hp

include hC hA hS hy hw hi in
lemma component_211202 :
    leftComponent C A S x y z w ii 2 1 1 2 0 2 =
    rightComponent C A S x y z w ii 2 1 1 2 0 2 := by
  simp only [leftComponent, rightComponent, Fin.sum_univ_three, numerator, Fin.val_zero, Fin.val_one, finThreeTwo, mul_zero, zero_mul, zero_add, add_zero]
  have hp := polynomial_020011 C A S x y z w ii hC hA hS hy hw hi
  dsimp only [poly_020011_0, complexAdd, complexMul, complexPow] at hp
  linear_combination (-1:ℂ)/1*hp

include hC hA hS hy hw in
lemma component_211220 :
    leftComponent C A S x y z w ii 2 1 1 2 2 0 =
    rightComponent C A S x y z w ii 2 1 1 2 2 0 := by
  simp only [leftComponent, rightComponent, Fin.sum_univ_three, numerator, Fin.val_zero, Fin.val_one, finThreeTwo, mul_zero, zero_mul, zero_add, add_zero]
  have hp := polynomial_002011 C A S x y z w ii hC hA hS hy hw
  dsimp only [poly_002011_0, complexAdd, complexMul, complexPow] at hp
  linear_combination (-1:ℂ)/1*hp

include hy in
lemma component_212221 :
    leftComponent C A S x y z w ii 2 1 2 2 2 1 =
    rightComponent C A S x y z w ii 2 1 2 2 2 1 := by
  simp only [leftComponent, rightComponent, Fin.sum_univ_three, numerator, Fin.val_zero, Fin.val_one, finThreeTwo, mul_zero, zero_mul, zero_add, add_zero]
  have hp := polynomial_001010 C A S x y z w ii hy
  dsimp only [poly_001010_0, complexAdd, complexMul, complexPow] at hp
  linear_combination (-1:ℂ)/1*hp

include hC hA hS hy hw hi in
lemma component_220022 :
    leftComponent C A S x y z w ii 2 2 0 0 2 2 =
    rightComponent C A S x y z w ii 2 2 0 0 2 2 := by
  simp only [leftComponent, rightComponent, Fin.sum_univ_three, numerator, Fin.val_zero, Fin.val_one, finThreeTwo, mul_zero, zero_mul, zero_add, add_zero]
  have hp := polynomial_200002 C A S x y z w ii hC hA hS hy hw hi
  dsimp only [poly_200002_0, complexAdd, complexMul, complexPow] at hp
  linear_combination (-1:ℂ)/1*hp

include hC hA hS hy hw hi in
lemma component_220112 :
    leftComponent C A S x y z w ii 2 2 0 1 1 2 =
    rightComponent C A S x y z w ii 2 2 0 1 1 2 := by
  simp only [leftComponent, rightComponent, Fin.sum_univ_three, numerator, Fin.val_zero, Fin.val_one, finThreeTwo, mul_zero, zero_mul, zero_add, add_zero]
  have hp := polynomial_110002 C A S x y z w ii hC hA hS hy hw hi
  dsimp only [poly_110002_0, complexAdd, complexMul, complexPow] at hp
  linear_combination (-1:ℂ)/1*hp

include hC hA hS hy hw in
lemma component_220121 :
    leftComponent C A S x y z w ii 2 2 0 1 2 1 =
    rightComponent C A S x y z w ii 2 2 0 1 2 1 := by
  simp only [leftComponent, rightComponent, Fin.sum_univ_three, numerator, Fin.val_zero, Fin.val_one, finThreeTwo, mul_zero, zero_mul, zero_add, add_zero]
  have hp := polynomial_101002 C A S x y z w ii hC hA hS hy hw
  dsimp only [poly_101002_0, complexAdd, complexMul, complexPow] at hp
  linear_combination (-1:ℂ)/1*hp

include hC hA hS hy hw hi in
lemma component_220202 :
    leftComponent C A S x y z w ii 2 2 0 2 0 2 =
    rightComponent C A S x y z w ii 2 2 0 2 0 2 := by
  simp only [leftComponent, rightComponent, Fin.sum_univ_three, numerator, Fin.val_zero, Fin.val_one, finThreeTwo, mul_zero, zero_mul, zero_add, add_zero]
  have hp := polynomial_002020 C A S x y z w ii hC hA hS hy hw hi
  dsimp only [poly_002020_0, complexAdd, complexMul, complexPow] at hp
  linear_combination (1:ℂ)/1*hp

include hC hA hS hy hw in
lemma component_220211 :
    leftComponent C A S x y z w ii 2 2 0 2 1 1 =
    rightComponent C A S x y z w ii 2 2 0 2 1 1 := by
  simp only [leftComponent, rightComponent, Fin.sum_univ_three, numerator, Fin.val_zero, Fin.val_one, finThreeTwo, mul_zero, zero_mul, zero_add, add_zero]
  have hp := polynomial_011002 C A S x y z w ii hC hA hS hy hw
  dsimp only [poly_011002_0, complexAdd, complexMul, complexPow] at hp
  linear_combination (-1:ℂ)/1*hp

include hC hA hS hy hw in
lemma component_221122 :
    leftComponent C A S x y z w ii 2 2 1 1 2 2 =
    rightComponent C A S x y z w ii 2 2 1 1 2 2 := by
  simp only [leftComponent, rightComponent, Fin.sum_univ_three, numerator, Fin.val_zero, Fin.val_one, finThreeTwo, mul_zero, zero_mul, zero_add, add_zero]
  have hp := polynomial_001100 C A S x y z w ii hC hA hS hy hw
  dsimp only [poly_001100_0, complexAdd, complexMul, complexPow] at hp
  linear_combination (1:ℂ)/1*hp

include hy in
lemma component_221212 :
    leftComponent C A S x y z w ii 2 2 1 2 1 2 =
    rightComponent C A S x y z w ii 2 2 1 2 1 2 := by
  simp only [leftComponent, rightComponent, Fin.sum_univ_three, numerator, Fin.val_zero, Fin.val_one, finThreeTwo, mul_zero, zero_mul, zero_add, add_zero]
  have hp := polynomial_001010 C A S x y z w ii hy
  dsimp only [poly_001010_0, complexAdd, complexMul, complexPow] at hp
  linear_combination (1:ℂ)/1*hp

lemma component_200000 :
    leftComponent C A S x y z w ii 2 0 0 0 0 0 =
    rightComponent C A S x y z w ii 2 0 0 0 0 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 0 0 0 0 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 0 0 0 0 0 (by decide)]

lemma component_200001 :
    leftComponent C A S x y z w ii 2 0 0 0 0 1 =
    rightComponent C A S x y z w ii 2 0 0 0 0 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 0 0 0 0 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 0 0 0 0 1 (by decide)]

lemma component_200010 :
    leftComponent C A S x y z w ii 2 0 0 0 1 0 =
    rightComponent C A S x y z w ii 2 0 0 0 1 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 0 0 0 1 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 0 0 0 1 0 (by decide)]

lemma component_200012 :
    leftComponent C A S x y z w ii 2 0 0 0 1 2 =
    rightComponent C A S x y z w ii 2 0 0 0 1 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 0 0 0 1 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 0 0 0 1 2 (by decide)]

lemma component_200021 :
    leftComponent C A S x y z w ii 2 0 0 0 2 1 =
    rightComponent C A S x y z w ii 2 0 0 0 2 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 0 0 0 2 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 0 0 0 2 1 (by decide)]

lemma component_200022 :
    leftComponent C A S x y z w ii 2 0 0 0 2 2 =
    rightComponent C A S x y z w ii 2 0 0 0 2 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 0 0 0 2 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 0 0 0 2 2 (by decide)]

lemma component_200100 :
    leftComponent C A S x y z w ii 2 0 0 1 0 0 =
    rightComponent C A S x y z w ii 2 0 0 1 0 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 0 0 1 0 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 0 0 1 0 0 (by decide)]

lemma component_200102 :
    leftComponent C A S x y z w ii 2 0 0 1 0 2 =
    rightComponent C A S x y z w ii 2 0 0 1 0 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 0 0 1 0 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 0 0 1 0 2 (by decide)]

lemma component_200111 :
    leftComponent C A S x y z w ii 2 0 0 1 1 1 =
    rightComponent C A S x y z w ii 2 0 0 1 1 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 0 0 1 1 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 0 0 1 1 1 (by decide)]

lemma component_200112 :
    leftComponent C A S x y z w ii 2 0 0 1 1 2 =
    rightComponent C A S x y z w ii 2 0 0 1 1 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 0 0 1 1 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 0 0 1 1 2 (by decide)]

lemma component_200120 :
    leftComponent C A S x y z w ii 2 0 0 1 2 0 =
    rightComponent C A S x y z w ii 2 0 0 1 2 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 0 0 1 2 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 0 0 1 2 0 (by decide)]

lemma component_200121 :
    leftComponent C A S x y z w ii 2 0 0 1 2 1 =
    rightComponent C A S x y z w ii 2 0 0 1 2 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 0 0 1 2 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 0 0 1 2 1 (by decide)]

lemma component_200122 :
    leftComponent C A S x y z w ii 2 0 0 1 2 2 =
    rightComponent C A S x y z w ii 2 0 0 1 2 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 0 0 1 2 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 0 0 1 2 2 (by decide)]

lemma component_200200 :
    leftComponent C A S x y z w ii 2 0 0 2 0 0 =
    rightComponent C A S x y z w ii 2 0 0 2 0 0 := by
  simp only [leftComponent, rightComponent, Fin.sum_univ_three, numerator, Fin.val_zero, Fin.val_one, finThreeTwo, mul_zero, zero_mul, zero_add, add_zero]
  ; ring

lemma component_200201 :
    leftComponent C A S x y z w ii 2 0 0 2 0 1 =
    rightComponent C A S x y z w ii 2 0 0 2 0 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 0 0 2 0 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 0 0 2 0 1 (by decide)]

lemma component_200202 :
    leftComponent C A S x y z w ii 2 0 0 2 0 2 =
    rightComponent C A S x y z w ii 2 0 0 2 0 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 0 0 2 0 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 0 0 2 0 2 (by decide)]

lemma component_200210 :
    leftComponent C A S x y z w ii 2 0 0 2 1 0 =
    rightComponent C A S x y z w ii 2 0 0 2 1 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 0 0 2 1 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 0 0 2 1 0 (by decide)]

lemma component_200211 :
    leftComponent C A S x y z w ii 2 0 0 2 1 1 =
    rightComponent C A S x y z w ii 2 0 0 2 1 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 0 0 2 1 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 0 0 2 1 1 (by decide)]

lemma component_200212 :
    leftComponent C A S x y z w ii 2 0 0 2 1 2 =
    rightComponent C A S x y z w ii 2 0 0 2 1 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 0 0 2 1 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 0 0 2 1 2 (by decide)]

lemma component_200220 :
    leftComponent C A S x y z w ii 2 0 0 2 2 0 =
    rightComponent C A S x y z w ii 2 0 0 2 2 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 0 0 2 2 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 0 0 2 2 0 (by decide)]

lemma component_200221 :
    leftComponent C A S x y z w ii 2 0 0 2 2 1 =
    rightComponent C A S x y z w ii 2 0 0 2 2 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 0 0 2 2 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 0 0 2 2 1 (by decide)]

lemma component_200222 :
    leftComponent C A S x y z w ii 2 0 0 2 2 2 =
    rightComponent C A S x y z w ii 2 0 0 2 2 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 0 0 2 2 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 0 0 2 2 2 (by decide)]

lemma component_201000 :
    leftComponent C A S x y z w ii 2 0 1 0 0 0 =
    rightComponent C A S x y z w ii 2 0 1 0 0 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 0 1 0 0 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 0 1 0 0 0 (by decide)]

lemma component_201001 :
    leftComponent C A S x y z w ii 2 0 1 0 0 1 =
    rightComponent C A S x y z w ii 2 0 1 0 0 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 0 1 0 0 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 0 1 0 0 1 (by decide)]

lemma component_201002 :
    leftComponent C A S x y z w ii 2 0 1 0 0 2 =
    rightComponent C A S x y z w ii 2 0 1 0 0 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 0 1 0 0 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 0 1 0 0 2 (by decide)]

lemma component_201010 :
    leftComponent C A S x y z w ii 2 0 1 0 1 0 =
    rightComponent C A S x y z w ii 2 0 1 0 1 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 0 1 0 1 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 0 1 0 1 0 (by decide)]

lemma component_201011 :
    leftComponent C A S x y z w ii 2 0 1 0 1 1 =
    rightComponent C A S x y z w ii 2 0 1 0 1 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 0 1 0 1 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 0 1 0 1 1 (by decide)]

lemma component_201020 :
    leftComponent C A S x y z w ii 2 0 1 0 2 0 =
    rightComponent C A S x y z w ii 2 0 1 0 2 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 0 1 0 2 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 0 1 0 2 0 (by decide)]

lemma component_201021 :
    leftComponent C A S x y z w ii 2 0 1 0 2 1 =
    rightComponent C A S x y z w ii 2 0 1 0 2 1 := by
  simp only [leftComponent, rightComponent, Fin.sum_univ_three, numerator, Fin.val_zero, Fin.val_one, finThreeTwo, mul_zero, zero_mul, zero_add, add_zero]
  ; ring

lemma component_201022 :
    leftComponent C A S x y z w ii 2 0 1 0 2 2 =
    rightComponent C A S x y z w ii 2 0 1 0 2 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 0 1 0 2 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 0 1 0 2 2 (by decide)]

lemma component_201100 :
    leftComponent C A S x y z w ii 2 0 1 1 0 0 =
    rightComponent C A S x y z w ii 2 0 1 1 0 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 0 1 1 0 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 0 1 1 0 0 (by decide)]

lemma component_201101 :
    leftComponent C A S x y z w ii 2 0 1 1 0 1 =
    rightComponent C A S x y z w ii 2 0 1 1 0 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 0 1 1 0 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 0 1 1 0 1 (by decide)]

lemma component_201110 :
    leftComponent C A S x y z w ii 2 0 1 1 1 0 =
    rightComponent C A S x y z w ii 2 0 1 1 1 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 0 1 1 1 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 0 1 1 1 0 (by decide)]

lemma component_201112 :
    leftComponent C A S x y z w ii 2 0 1 1 1 2 =
    rightComponent C A S x y z w ii 2 0 1 1 1 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 0 1 1 1 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 0 1 1 1 2 (by decide)]

lemma component_201121 :
    leftComponent C A S x y z w ii 2 0 1 1 2 1 =
    rightComponent C A S x y z w ii 2 0 1 1 2 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 0 1 1 2 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 0 1 1 2 1 (by decide)]

lemma component_201122 :
    leftComponent C A S x y z w ii 2 0 1 1 2 2 =
    rightComponent C A S x y z w ii 2 0 1 1 2 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 0 1 1 2 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 0 1 1 2 2 (by decide)]

lemma component_201200 :
    leftComponent C A S x y z w ii 2 0 1 2 0 0 =
    rightComponent C A S x y z w ii 2 0 1 2 0 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 0 1 2 0 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 0 1 2 0 0 (by decide)]

lemma component_201201 :
    leftComponent C A S x y z w ii 2 0 1 2 0 1 =
    rightComponent C A S x y z w ii 2 0 1 2 0 1 := by
  simp only [leftComponent, rightComponent, Fin.sum_univ_three, numerator, Fin.val_zero, Fin.val_one, finThreeTwo, mul_zero, zero_mul, zero_add, add_zero]
  ; ring

lemma component_201202 :
    leftComponent C A S x y z w ii 2 0 1 2 0 2 =
    rightComponent C A S x y z w ii 2 0 1 2 0 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 0 1 2 0 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 0 1 2 0 2 (by decide)]

lemma component_201211 :
    leftComponent C A S x y z w ii 2 0 1 2 1 1 =
    rightComponent C A S x y z w ii 2 0 1 2 1 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 0 1 2 1 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 0 1 2 1 1 (by decide)]

lemma component_201212 :
    leftComponent C A S x y z w ii 2 0 1 2 1 2 =
    rightComponent C A S x y z w ii 2 0 1 2 1 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 0 1 2 1 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 0 1 2 1 2 (by decide)]

lemma component_201220 :
    leftComponent C A S x y z w ii 2 0 1 2 2 0 =
    rightComponent C A S x y z w ii 2 0 1 2 2 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 0 1 2 2 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 0 1 2 2 0 (by decide)]

lemma component_201221 :
    leftComponent C A S x y z w ii 2 0 1 2 2 1 =
    rightComponent C A S x y z w ii 2 0 1 2 2 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 0 1 2 2 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 0 1 2 2 1 (by decide)]

lemma component_201222 :
    leftComponent C A S x y z w ii 2 0 1 2 2 2 =
    rightComponent C A S x y z w ii 2 0 1 2 2 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 0 1 2 2 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 0 1 2 2 2 (by decide)]

lemma component_202000 :
    leftComponent C A S x y z w ii 2 0 2 0 0 0 =
    rightComponent C A S x y z w ii 2 0 2 0 0 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 0 2 0 0 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 0 2 0 0 0 (by decide)]

lemma component_202001 :
    leftComponent C A S x y z w ii 2 0 2 0 0 1 =
    rightComponent C A S x y z w ii 2 0 2 0 0 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 0 2 0 0 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 0 2 0 0 1 (by decide)]

lemma component_202002 :
    leftComponent C A S x y z w ii 2 0 2 0 0 2 =
    rightComponent C A S x y z w ii 2 0 2 0 0 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 0 2 0 0 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 0 2 0 0 2 (by decide)]

lemma component_202010 :
    leftComponent C A S x y z w ii 2 0 2 0 1 0 =
    rightComponent C A S x y z w ii 2 0 2 0 1 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 0 2 0 1 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 0 2 0 1 0 (by decide)]

lemma component_202011 :
    leftComponent C A S x y z w ii 2 0 2 0 1 1 =
    rightComponent C A S x y z w ii 2 0 2 0 1 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 0 2 0 1 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 0 2 0 1 1 (by decide)]

lemma component_202012 :
    leftComponent C A S x y z w ii 2 0 2 0 1 2 =
    rightComponent C A S x y z w ii 2 0 2 0 1 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 0 2 0 1 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 0 2 0 1 2 (by decide)]

lemma component_202020 :
    leftComponent C A S x y z w ii 2 0 2 0 2 0 =
    rightComponent C A S x y z w ii 2 0 2 0 2 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 0 2 0 2 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 0 2 0 2 0 (by decide)]

lemma component_202021 :
    leftComponent C A S x y z w ii 2 0 2 0 2 1 =
    rightComponent C A S x y z w ii 2 0 2 0 2 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 0 2 0 2 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 0 2 0 2 1 (by decide)]

lemma component_202100 :
    leftComponent C A S x y z w ii 2 0 2 1 0 0 =
    rightComponent C A S x y z w ii 2 0 2 1 0 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 0 2 1 0 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 0 2 1 0 0 (by decide)]

lemma component_202101 :
    leftComponent C A S x y z w ii 2 0 2 1 0 1 =
    rightComponent C A S x y z w ii 2 0 2 1 0 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 0 2 1 0 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 0 2 1 0 1 (by decide)]

lemma component_202102 :
    leftComponent C A S x y z w ii 2 0 2 1 0 2 =
    rightComponent C A S x y z w ii 2 0 2 1 0 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 0 2 1 0 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 0 2 1 0 2 (by decide)]

lemma component_202110 :
    leftComponent C A S x y z w ii 2 0 2 1 1 0 =
    rightComponent C A S x y z w ii 2 0 2 1 1 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 0 2 1 1 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 0 2 1 1 0 (by decide)]

lemma component_202111 :
    leftComponent C A S x y z w ii 2 0 2 1 1 1 =
    rightComponent C A S x y z w ii 2 0 2 1 1 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 0 2 1 1 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 0 2 1 1 1 (by decide)]

lemma component_202120 :
    leftComponent C A S x y z w ii 2 0 2 1 2 0 =
    rightComponent C A S x y z w ii 2 0 2 1 2 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 0 2 1 2 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 0 2 1 2 0 (by decide)]

lemma component_202122 :
    leftComponent C A S x y z w ii 2 0 2 1 2 2 =
    rightComponent C A S x y z w ii 2 0 2 1 2 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 0 2 1 2 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 0 2 1 2 2 (by decide)]

lemma component_202200 :
    leftComponent C A S x y z w ii 2 0 2 2 0 0 =
    rightComponent C A S x y z w ii 2 0 2 2 0 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 0 2 2 0 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 0 2 2 0 0 (by decide)]

lemma component_202201 :
    leftComponent C A S x y z w ii 2 0 2 2 0 1 =
    rightComponent C A S x y z w ii 2 0 2 2 0 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 0 2 2 0 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 0 2 2 0 1 (by decide)]

lemma component_202210 :
    leftComponent C A S x y z w ii 2 0 2 2 1 0 =
    rightComponent C A S x y z w ii 2 0 2 2 1 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 0 2 2 1 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 0 2 2 1 0 (by decide)]

lemma component_202212 :
    leftComponent C A S x y z w ii 2 0 2 2 1 2 =
    rightComponent C A S x y z w ii 2 0 2 2 1 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 0 2 2 1 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 0 2 2 1 2 (by decide)]

lemma component_202221 :
    leftComponent C A S x y z w ii 2 0 2 2 2 1 =
    rightComponent C A S x y z w ii 2 0 2 2 2 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 0 2 2 2 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 0 2 2 2 1 (by decide)]

lemma component_202222 :
    leftComponent C A S x y z w ii 2 0 2 2 2 2 =
    rightComponent C A S x y z w ii 2 0 2 2 2 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 0 2 2 2 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 0 2 2 2 2 (by decide)]

lemma component_210000 :
    leftComponent C A S x y z w ii 2 1 0 0 0 0 =
    rightComponent C A S x y z w ii 2 1 0 0 0 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 1 0 0 0 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 1 0 0 0 0 (by decide)]

lemma component_210001 :
    leftComponent C A S x y z w ii 2 1 0 0 0 1 =
    rightComponent C A S x y z w ii 2 1 0 0 0 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 1 0 0 0 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 1 0 0 0 1 (by decide)]

lemma component_210002 :
    leftComponent C A S x y z w ii 2 1 0 0 0 2 =
    rightComponent C A S x y z w ii 2 1 0 0 0 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 1 0 0 0 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 1 0 0 0 2 (by decide)]

lemma component_210010 :
    leftComponent C A S x y z w ii 2 1 0 0 1 0 =
    rightComponent C A S x y z w ii 2 1 0 0 1 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 1 0 0 1 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 1 0 0 1 0 (by decide)]

lemma component_210011 :
    leftComponent C A S x y z w ii 2 1 0 0 1 1 =
    rightComponent C A S x y z w ii 2 1 0 0 1 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 1 0 0 1 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 1 0 0 1 1 (by decide)]

lemma component_210012 :
    leftComponent C A S x y z w ii 2 1 0 0 1 2 =
    rightComponent C A S x y z w ii 2 1 0 0 1 2 := by
  simp only [leftComponent, rightComponent, Fin.sum_univ_three, numerator, Fin.val_zero, Fin.val_one, finThreeTwo, mul_zero, zero_mul, zero_add, add_zero]
  ; ring

lemma component_210020 :
    leftComponent C A S x y z w ii 2 1 0 0 2 0 =
    rightComponent C A S x y z w ii 2 1 0 0 2 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 1 0 0 2 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 1 0 0 2 0 (by decide)]

lemma component_210022 :
    leftComponent C A S x y z w ii 2 1 0 0 2 2 =
    rightComponent C A S x y z w ii 2 1 0 0 2 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 1 0 0 2 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 1 0 0 2 2 (by decide)]

lemma component_210100 :
    leftComponent C A S x y z w ii 2 1 0 1 0 0 =
    rightComponent C A S x y z w ii 2 1 0 1 0 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 1 0 1 0 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 1 0 1 0 0 (by decide)]

lemma component_210101 :
    leftComponent C A S x y z w ii 2 1 0 1 0 1 =
    rightComponent C A S x y z w ii 2 1 0 1 0 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 1 0 1 0 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 1 0 1 0 1 (by decide)]

lemma component_210110 :
    leftComponent C A S x y z w ii 2 1 0 1 1 0 =
    rightComponent C A S x y z w ii 2 1 0 1 1 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 1 0 1 1 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 1 0 1 1 0 (by decide)]

lemma component_210112 :
    leftComponent C A S x y z w ii 2 1 0 1 1 2 =
    rightComponent C A S x y z w ii 2 1 0 1 1 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 1 0 1 1 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 1 0 1 1 2 (by decide)]

lemma component_210121 :
    leftComponent C A S x y z w ii 2 1 0 1 2 1 =
    rightComponent C A S x y z w ii 2 1 0 1 2 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 1 0 1 2 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 1 0 1 2 1 (by decide)]

lemma component_210122 :
    leftComponent C A S x y z w ii 2 1 0 1 2 2 =
    rightComponent C A S x y z w ii 2 1 0 1 2 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 1 0 1 2 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 1 0 1 2 2 (by decide)]

lemma component_210200 :
    leftComponent C A S x y z w ii 2 1 0 2 0 0 =
    rightComponent C A S x y z w ii 2 1 0 2 0 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 1 0 2 0 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 1 0 2 0 0 (by decide)]

lemma component_210202 :
    leftComponent C A S x y z w ii 2 1 0 2 0 2 =
    rightComponent C A S x y z w ii 2 1 0 2 0 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 1 0 2 0 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 1 0 2 0 2 (by decide)]

lemma component_210210 :
    leftComponent C A S x y z w ii 2 1 0 2 1 0 =
    rightComponent C A S x y z w ii 2 1 0 2 1 0 := by
  simp only [leftComponent, rightComponent, Fin.sum_univ_three, numerator, Fin.val_zero, Fin.val_one, finThreeTwo, mul_zero, zero_mul, zero_add, add_zero]
  ; ring

lemma component_210211 :
    leftComponent C A S x y z w ii 2 1 0 2 1 1 =
    rightComponent C A S x y z w ii 2 1 0 2 1 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 1 0 2 1 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 1 0 2 1 1 (by decide)]

lemma component_210212 :
    leftComponent C A S x y z w ii 2 1 0 2 1 2 =
    rightComponent C A S x y z w ii 2 1 0 2 1 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 1 0 2 1 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 1 0 2 1 2 (by decide)]

lemma component_210220 :
    leftComponent C A S x y z w ii 2 1 0 2 2 0 =
    rightComponent C A S x y z w ii 2 1 0 2 2 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 1 0 2 2 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 1 0 2 2 0 (by decide)]

lemma component_210221 :
    leftComponent C A S x y z w ii 2 1 0 2 2 1 =
    rightComponent C A S x y z w ii 2 1 0 2 2 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 1 0 2 2 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 1 0 2 2 1 (by decide)]

lemma component_210222 :
    leftComponent C A S x y z w ii 2 1 0 2 2 2 =
    rightComponent C A S x y z w ii 2 1 0 2 2 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 1 0 2 2 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 1 0 2 2 2 (by decide)]

lemma component_211000 :
    leftComponent C A S x y z w ii 2 1 1 0 0 0 =
    rightComponent C A S x y z w ii 2 1 1 0 0 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 1 1 0 0 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 1 1 0 0 0 (by decide)]

lemma component_211001 :
    leftComponent C A S x y z w ii 2 1 1 0 0 1 =
    rightComponent C A S x y z w ii 2 1 1 0 0 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 1 1 0 0 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 1 1 0 0 1 (by decide)]

lemma component_211002 :
    leftComponent C A S x y z w ii 2 1 1 0 0 2 =
    rightComponent C A S x y z w ii 2 1 1 0 0 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 1 1 0 0 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 1 1 0 0 2 (by decide)]

lemma component_211010 :
    leftComponent C A S x y z w ii 2 1 1 0 1 0 =
    rightComponent C A S x y z w ii 2 1 1 0 1 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 1 1 0 1 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 1 1 0 1 0 (by decide)]

lemma component_211011 :
    leftComponent C A S x y z w ii 2 1 1 0 1 1 =
    rightComponent C A S x y z w ii 2 1 1 0 1 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 1 1 0 1 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 1 1 0 1 1 (by decide)]

lemma component_211012 :
    leftComponent C A S x y z w ii 2 1 1 0 1 2 =
    rightComponent C A S x y z w ii 2 1 1 0 1 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 1 1 0 1 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 1 1 0 1 2 (by decide)]

lemma component_211020 :
    leftComponent C A S x y z w ii 2 1 1 0 2 0 =
    rightComponent C A S x y z w ii 2 1 1 0 2 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 1 1 0 2 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 1 1 0 2 0 (by decide)]

lemma component_211021 :
    leftComponent C A S x y z w ii 2 1 1 0 2 1 =
    rightComponent C A S x y z w ii 2 1 1 0 2 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 1 1 0 2 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 1 1 0 2 1 (by decide)]

lemma component_211100 :
    leftComponent C A S x y z w ii 2 1 1 1 0 0 =
    rightComponent C A S x y z w ii 2 1 1 1 0 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 1 1 1 0 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 1 1 1 0 0 (by decide)]

lemma component_211101 :
    leftComponent C A S x y z w ii 2 1 1 1 0 1 =
    rightComponent C A S x y z w ii 2 1 1 1 0 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 1 1 1 0 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 1 1 1 0 1 (by decide)]

lemma component_211102 :
    leftComponent C A S x y z w ii 2 1 1 1 0 2 =
    rightComponent C A S x y z w ii 2 1 1 1 0 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 1 1 1 0 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 1 1 1 0 2 (by decide)]

lemma component_211110 :
    leftComponent C A S x y z w ii 2 1 1 1 1 0 =
    rightComponent C A S x y z w ii 2 1 1 1 1 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 1 1 1 1 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 1 1 1 1 0 (by decide)]

lemma component_211111 :
    leftComponent C A S x y z w ii 2 1 1 1 1 1 =
    rightComponent C A S x y z w ii 2 1 1 1 1 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 1 1 1 1 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 1 1 1 1 1 (by decide)]

lemma component_211120 :
    leftComponent C A S x y z w ii 2 1 1 1 2 0 =
    rightComponent C A S x y z w ii 2 1 1 1 2 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 1 1 1 2 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 1 1 1 2 0 (by decide)]

lemma component_211122 :
    leftComponent C A S x y z w ii 2 1 1 1 2 2 =
    rightComponent C A S x y z w ii 2 1 1 1 2 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 1 1 1 2 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 1 1 1 2 2 (by decide)]

lemma component_211200 :
    leftComponent C A S x y z w ii 2 1 1 2 0 0 =
    rightComponent C A S x y z w ii 2 1 1 2 0 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 1 1 2 0 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 1 1 2 0 0 (by decide)]

lemma component_211201 :
    leftComponent C A S x y z w ii 2 1 1 2 0 1 =
    rightComponent C A S x y z w ii 2 1 1 2 0 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 1 1 2 0 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 1 1 2 0 1 (by decide)]

lemma component_211210 :
    leftComponent C A S x y z w ii 2 1 1 2 1 0 =
    rightComponent C A S x y z w ii 2 1 1 2 1 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 1 1 2 1 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 1 1 2 1 0 (by decide)]

lemma component_211211 :
    leftComponent C A S x y z w ii 2 1 1 2 1 1 =
    rightComponent C A S x y z w ii 2 1 1 2 1 1 := by
  simp only [leftComponent, rightComponent, Fin.sum_univ_three, numerator, Fin.val_zero, Fin.val_one, finThreeTwo, mul_zero, zero_mul, zero_add, add_zero]
  ; ring

lemma component_211212 :
    leftComponent C A S x y z w ii 2 1 1 2 1 2 =
    rightComponent C A S x y z w ii 2 1 1 2 1 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 1 1 2 1 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 1 1 2 1 2 (by decide)]

lemma component_211221 :
    leftComponent C A S x y z w ii 2 1 1 2 2 1 =
    rightComponent C A S x y z w ii 2 1 1 2 2 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 1 1 2 2 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 1 1 2 2 1 (by decide)]

lemma component_211222 :
    leftComponent C A S x y z w ii 2 1 1 2 2 2 =
    rightComponent C A S x y z w ii 2 1 1 2 2 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 1 1 2 2 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 1 1 2 2 2 (by decide)]

lemma component_212000 :
    leftComponent C A S x y z w ii 2 1 2 0 0 0 =
    rightComponent C A S x y z w ii 2 1 2 0 0 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 1 2 0 0 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 1 2 0 0 0 (by decide)]

lemma component_212001 :
    leftComponent C A S x y z w ii 2 1 2 0 0 1 =
    rightComponent C A S x y z w ii 2 1 2 0 0 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 1 2 0 0 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 1 2 0 0 1 (by decide)]

lemma component_212002 :
    leftComponent C A S x y z w ii 2 1 2 0 0 2 =
    rightComponent C A S x y z w ii 2 1 2 0 0 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 1 2 0 0 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 1 2 0 0 2 (by decide)]

lemma component_212010 :
    leftComponent C A S x y z w ii 2 1 2 0 1 0 =
    rightComponent C A S x y z w ii 2 1 2 0 1 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 1 2 0 1 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 1 2 0 1 0 (by decide)]

lemma component_212011 :
    leftComponent C A S x y z w ii 2 1 2 0 1 1 =
    rightComponent C A S x y z w ii 2 1 2 0 1 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 1 2 0 1 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 1 2 0 1 1 (by decide)]

lemma component_212012 :
    leftComponent C A S x y z w ii 2 1 2 0 1 2 =
    rightComponent C A S x y z w ii 2 1 2 0 1 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 1 2 0 1 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 1 2 0 1 2 (by decide)]

lemma component_212020 :
    leftComponent C A S x y z w ii 2 1 2 0 2 0 =
    rightComponent C A S x y z w ii 2 1 2 0 2 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 1 2 0 2 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 1 2 0 2 0 (by decide)]

lemma component_212021 :
    leftComponent C A S x y z w ii 2 1 2 0 2 1 =
    rightComponent C A S x y z w ii 2 1 2 0 2 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 1 2 0 2 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 1 2 0 2 1 (by decide)]

lemma component_212022 :
    leftComponent C A S x y z w ii 2 1 2 0 2 2 =
    rightComponent C A S x y z w ii 2 1 2 0 2 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 1 2 0 2 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 1 2 0 2 2 (by decide)]

lemma component_212100 :
    leftComponent C A S x y z w ii 2 1 2 1 0 0 =
    rightComponent C A S x y z w ii 2 1 2 1 0 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 1 2 1 0 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 1 2 1 0 0 (by decide)]

lemma component_212101 :
    leftComponent C A S x y z w ii 2 1 2 1 0 1 =
    rightComponent C A S x y z w ii 2 1 2 1 0 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 1 2 1 0 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 1 2 1 0 1 (by decide)]

lemma component_212102 :
    leftComponent C A S x y z w ii 2 1 2 1 0 2 =
    rightComponent C A S x y z w ii 2 1 2 1 0 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 1 2 1 0 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 1 2 1 0 2 (by decide)]

lemma component_212110 :
    leftComponent C A S x y z w ii 2 1 2 1 1 0 =
    rightComponent C A S x y z w ii 2 1 2 1 1 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 1 2 1 1 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 1 2 1 1 0 (by decide)]

lemma component_212111 :
    leftComponent C A S x y z w ii 2 1 2 1 1 1 =
    rightComponent C A S x y z w ii 2 1 2 1 1 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 1 2 1 1 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 1 2 1 1 1 (by decide)]

lemma component_212112 :
    leftComponent C A S x y z w ii 2 1 2 1 1 2 =
    rightComponent C A S x y z w ii 2 1 2 1 1 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 1 2 1 1 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 1 2 1 1 2 (by decide)]

lemma component_212120 :
    leftComponent C A S x y z w ii 2 1 2 1 2 0 =
    rightComponent C A S x y z w ii 2 1 2 1 2 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 1 2 1 2 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 1 2 1 2 0 (by decide)]

lemma component_212121 :
    leftComponent C A S x y z w ii 2 1 2 1 2 1 =
    rightComponent C A S x y z w ii 2 1 2 1 2 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 1 2 1 2 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 1 2 1 2 1 (by decide)]

lemma component_212122 :
    leftComponent C A S x y z w ii 2 1 2 1 2 2 =
    rightComponent C A S x y z w ii 2 1 2 1 2 2 := by
  simp only [leftComponent, rightComponent, Fin.sum_univ_three, numerator, Fin.val_zero, Fin.val_one, finThreeTwo, mul_zero, zero_mul, zero_add, add_zero]
  ; ring

lemma component_212200 :
    leftComponent C A S x y z w ii 2 1 2 2 0 0 =
    rightComponent C A S x y z w ii 2 1 2 2 0 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 1 2 2 0 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 1 2 2 0 0 (by decide)]

lemma component_212201 :
    leftComponent C A S x y z w ii 2 1 2 2 0 1 =
    rightComponent C A S x y z w ii 2 1 2 2 0 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 1 2 2 0 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 1 2 2 0 1 (by decide)]

lemma component_212202 :
    leftComponent C A S x y z w ii 2 1 2 2 0 2 =
    rightComponent C A S x y z w ii 2 1 2 2 0 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 1 2 2 0 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 1 2 2 0 2 (by decide)]

lemma component_212210 :
    leftComponent C A S x y z w ii 2 1 2 2 1 0 =
    rightComponent C A S x y z w ii 2 1 2 2 1 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 1 2 2 1 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 1 2 2 1 0 (by decide)]

lemma component_212211 :
    leftComponent C A S x y z w ii 2 1 2 2 1 1 =
    rightComponent C A S x y z w ii 2 1 2 2 1 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 1 2 2 1 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 1 2 2 1 1 (by decide)]

lemma component_212212 :
    leftComponent C A S x y z w ii 2 1 2 2 1 2 =
    rightComponent C A S x y z w ii 2 1 2 2 1 2 := by
  simp only [leftComponent, rightComponent, Fin.sum_univ_three, numerator, Fin.val_zero, Fin.val_one, finThreeTwo, mul_zero, zero_mul, zero_add, add_zero]
  ; ring

lemma component_212220 :
    leftComponent C A S x y z w ii 2 1 2 2 2 0 =
    rightComponent C A S x y z w ii 2 1 2 2 2 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 1 2 2 2 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 1 2 2 2 0 (by decide)]

lemma component_212222 :
    leftComponent C A S x y z w ii 2 1 2 2 2 2 =
    rightComponent C A S x y z w ii 2 1 2 2 2 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 1 2 2 2 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 1 2 2 2 2 (by decide)]

lemma component_220000 :
    leftComponent C A S x y z w ii 2 2 0 0 0 0 =
    rightComponent C A S x y z w ii 2 2 0 0 0 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 2 0 0 0 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 2 0 0 0 0 (by decide)]

lemma component_220001 :
    leftComponent C A S x y z w ii 2 2 0 0 0 1 =
    rightComponent C A S x y z w ii 2 2 0 0 0 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 2 0 0 0 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 2 0 0 0 1 (by decide)]

lemma component_220002 :
    leftComponent C A S x y z w ii 2 2 0 0 0 2 =
    rightComponent C A S x y z w ii 2 2 0 0 0 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 2 0 0 0 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 2 0 0 0 2 (by decide)]

lemma component_220010 :
    leftComponent C A S x y z w ii 2 2 0 0 1 0 =
    rightComponent C A S x y z w ii 2 2 0 0 1 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 2 0 0 1 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 2 0 0 1 0 (by decide)]

lemma component_220011 :
    leftComponent C A S x y z w ii 2 2 0 0 1 1 =
    rightComponent C A S x y z w ii 2 2 0 0 1 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 2 0 0 1 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 2 0 0 1 1 (by decide)]

lemma component_220012 :
    leftComponent C A S x y z w ii 2 2 0 0 1 2 =
    rightComponent C A S x y z w ii 2 2 0 0 1 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 2 0 0 1 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 2 0 0 1 2 (by decide)]

lemma component_220020 :
    leftComponent C A S x y z w ii 2 2 0 0 2 0 =
    rightComponent C A S x y z w ii 2 2 0 0 2 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 2 0 0 2 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 2 0 0 2 0 (by decide)]

lemma component_220021 :
    leftComponent C A S x y z w ii 2 2 0 0 2 1 =
    rightComponent C A S x y z w ii 2 2 0 0 2 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 2 0 0 2 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 2 0 0 2 1 (by decide)]

lemma component_220100 :
    leftComponent C A S x y z w ii 2 2 0 1 0 0 =
    rightComponent C A S x y z w ii 2 2 0 1 0 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 2 0 1 0 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 2 0 1 0 0 (by decide)]

lemma component_220101 :
    leftComponent C A S x y z w ii 2 2 0 1 0 1 =
    rightComponent C A S x y z w ii 2 2 0 1 0 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 2 0 1 0 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 2 0 1 0 1 (by decide)]

lemma component_220102 :
    leftComponent C A S x y z w ii 2 2 0 1 0 2 =
    rightComponent C A S x y z w ii 2 2 0 1 0 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 2 0 1 0 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 2 0 1 0 2 (by decide)]

lemma component_220110 :
    leftComponent C A S x y z w ii 2 2 0 1 1 0 =
    rightComponent C A S x y z w ii 2 2 0 1 1 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 2 0 1 1 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 2 0 1 1 0 (by decide)]

lemma component_220111 :
    leftComponent C A S x y z w ii 2 2 0 1 1 1 =
    rightComponent C A S x y z w ii 2 2 0 1 1 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 2 0 1 1 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 2 0 1 1 1 (by decide)]

lemma component_220120 :
    leftComponent C A S x y z w ii 2 2 0 1 2 0 =
    rightComponent C A S x y z w ii 2 2 0 1 2 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 2 0 1 2 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 2 0 1 2 0 (by decide)]

lemma component_220122 :
    leftComponent C A S x y z w ii 2 2 0 1 2 2 =
    rightComponent C A S x y z w ii 2 2 0 1 2 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 2 0 1 2 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 2 0 1 2 2 (by decide)]

lemma component_220200 :
    leftComponent C A S x y z w ii 2 2 0 2 0 0 =
    rightComponent C A S x y z w ii 2 2 0 2 0 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 2 0 2 0 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 2 0 2 0 0 (by decide)]

lemma component_220201 :
    leftComponent C A S x y z w ii 2 2 0 2 0 1 =
    rightComponent C A S x y z w ii 2 2 0 2 0 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 2 0 2 0 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 2 0 2 0 1 (by decide)]

lemma component_220210 :
    leftComponent C A S x y z w ii 2 2 0 2 1 0 =
    rightComponent C A S x y z w ii 2 2 0 2 1 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 2 0 2 1 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 2 0 2 1 0 (by decide)]

lemma component_220212 :
    leftComponent C A S x y z w ii 2 2 0 2 1 2 =
    rightComponent C A S x y z w ii 2 2 0 2 1 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 2 0 2 1 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 2 0 2 1 2 (by decide)]

lemma component_220220 :
    leftComponent C A S x y z w ii 2 2 0 2 2 0 =
    rightComponent C A S x y z w ii 2 2 0 2 2 0 := by
  simp only [leftComponent, rightComponent, Fin.sum_univ_three, numerator, Fin.val_zero, Fin.val_one, finThreeTwo, mul_zero, zero_mul, zero_add, add_zero]
  ; ring

lemma component_220221 :
    leftComponent C A S x y z w ii 2 2 0 2 2 1 =
    rightComponent C A S x y z w ii 2 2 0 2 2 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 2 0 2 2 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 2 0 2 2 1 (by decide)]

lemma component_220222 :
    leftComponent C A S x y z w ii 2 2 0 2 2 2 =
    rightComponent C A S x y z w ii 2 2 0 2 2 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 2 0 2 2 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 2 0 2 2 2 (by decide)]

lemma component_221000 :
    leftComponent C A S x y z w ii 2 2 1 0 0 0 =
    rightComponent C A S x y z w ii 2 2 1 0 0 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 2 1 0 0 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 2 1 0 0 0 (by decide)]

lemma component_221001 :
    leftComponent C A S x y z w ii 2 2 1 0 0 1 =
    rightComponent C A S x y z w ii 2 2 1 0 0 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 2 1 0 0 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 2 1 0 0 1 (by decide)]

lemma component_221002 :
    leftComponent C A S x y z w ii 2 2 1 0 0 2 =
    rightComponent C A S x y z w ii 2 2 1 0 0 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 2 1 0 0 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 2 1 0 0 2 (by decide)]

lemma component_221010 :
    leftComponent C A S x y z w ii 2 2 1 0 1 0 =
    rightComponent C A S x y z w ii 2 2 1 0 1 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 2 1 0 1 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 2 1 0 1 0 (by decide)]

lemma component_221011 :
    leftComponent C A S x y z w ii 2 2 1 0 1 1 =
    rightComponent C A S x y z w ii 2 2 1 0 1 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 2 1 0 1 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 2 1 0 1 1 (by decide)]

lemma component_221012 :
    leftComponent C A S x y z w ii 2 2 1 0 1 2 =
    rightComponent C A S x y z w ii 2 2 1 0 1 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 2 1 0 1 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 2 1 0 1 2 (by decide)]

lemma component_221020 :
    leftComponent C A S x y z w ii 2 2 1 0 2 0 =
    rightComponent C A S x y z w ii 2 2 1 0 2 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 2 1 0 2 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 2 1 0 2 0 (by decide)]

lemma component_221021 :
    leftComponent C A S x y z w ii 2 2 1 0 2 1 =
    rightComponent C A S x y z w ii 2 2 1 0 2 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 2 1 0 2 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 2 1 0 2 1 (by decide)]

lemma component_221022 :
    leftComponent C A S x y z w ii 2 2 1 0 2 2 =
    rightComponent C A S x y z w ii 2 2 1 0 2 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 2 1 0 2 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 2 1 0 2 2 (by decide)]

lemma component_221100 :
    leftComponent C A S x y z w ii 2 2 1 1 0 0 =
    rightComponent C A S x y z w ii 2 2 1 1 0 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 2 1 1 0 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 2 1 1 0 0 (by decide)]

lemma component_221101 :
    leftComponent C A S x y z w ii 2 2 1 1 0 1 =
    rightComponent C A S x y z w ii 2 2 1 1 0 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 2 1 1 0 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 2 1 1 0 1 (by decide)]

lemma component_221102 :
    leftComponent C A S x y z w ii 2 2 1 1 0 2 =
    rightComponent C A S x y z w ii 2 2 1 1 0 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 2 1 1 0 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 2 1 1 0 2 (by decide)]

lemma component_221110 :
    leftComponent C A S x y z w ii 2 2 1 1 1 0 =
    rightComponent C A S x y z w ii 2 2 1 1 1 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 2 1 1 1 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 2 1 1 1 0 (by decide)]

lemma component_221111 :
    leftComponent C A S x y z w ii 2 2 1 1 1 1 =
    rightComponent C A S x y z w ii 2 2 1 1 1 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 2 1 1 1 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 2 1 1 1 1 (by decide)]

lemma component_221112 :
    leftComponent C A S x y z w ii 2 2 1 1 1 2 =
    rightComponent C A S x y z w ii 2 2 1 1 1 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 2 1 1 1 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 2 1 1 1 2 (by decide)]

lemma component_221120 :
    leftComponent C A S x y z w ii 2 2 1 1 2 0 =
    rightComponent C A S x y z w ii 2 2 1 1 2 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 2 1 1 2 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 2 1 1 2 0 (by decide)]

lemma component_221121 :
    leftComponent C A S x y z w ii 2 2 1 1 2 1 =
    rightComponent C A S x y z w ii 2 2 1 1 2 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 2 1 1 2 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 2 1 1 2 1 (by decide)]

lemma component_221200 :
    leftComponent C A S x y z w ii 2 2 1 2 0 0 =
    rightComponent C A S x y z w ii 2 2 1 2 0 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 2 1 2 0 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 2 1 2 0 0 (by decide)]

lemma component_221201 :
    leftComponent C A S x y z w ii 2 2 1 2 0 1 =
    rightComponent C A S x y z w ii 2 2 1 2 0 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 2 1 2 0 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 2 1 2 0 1 (by decide)]

lemma component_221202 :
    leftComponent C A S x y z w ii 2 2 1 2 0 2 =
    rightComponent C A S x y z w ii 2 2 1 2 0 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 2 1 2 0 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 2 1 2 0 2 (by decide)]

lemma component_221210 :
    leftComponent C A S x y z w ii 2 2 1 2 1 0 =
    rightComponent C A S x y z w ii 2 2 1 2 1 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 2 1 2 1 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 2 1 2 1 0 (by decide)]

lemma component_221211 :
    leftComponent C A S x y z w ii 2 2 1 2 1 1 =
    rightComponent C A S x y z w ii 2 2 1 2 1 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 2 1 2 1 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 2 1 2 1 1 (by decide)]

lemma component_221220 :
    leftComponent C A S x y z w ii 2 2 1 2 2 0 =
    rightComponent C A S x y z w ii 2 2 1 2 2 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 2 1 2 2 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 2 1 2 2 0 (by decide)]

lemma component_221221 :
    leftComponent C A S x y z w ii 2 2 1 2 2 1 =
    rightComponent C A S x y z w ii 2 2 1 2 2 1 := by
  simp only [leftComponent, rightComponent, Fin.sum_univ_three, numerator, Fin.val_zero, Fin.val_one, finThreeTwo, mul_zero, zero_mul, zero_add, add_zero]
  ; ring

lemma component_221222 :
    leftComponent C A S x y z w ii 2 2 1 2 2 2 =
    rightComponent C A S x y z w ii 2 2 1 2 2 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 2 1 2 2 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 2 1 2 2 2 (by decide)]

lemma component_222000 :
    leftComponent C A S x y z w ii 2 2 2 0 0 0 =
    rightComponent C A S x y z w ii 2 2 2 0 0 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 2 2 0 0 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 2 2 0 0 0 (by decide)]

lemma component_222001 :
    leftComponent C A S x y z w ii 2 2 2 0 0 1 =
    rightComponent C A S x y z w ii 2 2 2 0 0 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 2 2 0 0 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 2 2 0 0 1 (by decide)]

lemma component_222002 :
    leftComponent C A S x y z w ii 2 2 2 0 0 2 =
    rightComponent C A S x y z w ii 2 2 2 0 0 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 2 2 0 0 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 2 2 0 0 2 (by decide)]

lemma component_222010 :
    leftComponent C A S x y z w ii 2 2 2 0 1 0 =
    rightComponent C A S x y z w ii 2 2 2 0 1 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 2 2 0 1 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 2 2 0 1 0 (by decide)]

lemma component_222011 :
    leftComponent C A S x y z w ii 2 2 2 0 1 1 =
    rightComponent C A S x y z w ii 2 2 2 0 1 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 2 2 0 1 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 2 2 0 1 1 (by decide)]

lemma component_222012 :
    leftComponent C A S x y z w ii 2 2 2 0 1 2 =
    rightComponent C A S x y z w ii 2 2 2 0 1 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 2 2 0 1 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 2 2 0 1 2 (by decide)]

lemma component_222020 :
    leftComponent C A S x y z w ii 2 2 2 0 2 0 =
    rightComponent C A S x y z w ii 2 2 2 0 2 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 2 2 0 2 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 2 2 0 2 0 (by decide)]

lemma component_222021 :
    leftComponent C A S x y z w ii 2 2 2 0 2 1 =
    rightComponent C A S x y z w ii 2 2 2 0 2 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 2 2 0 2 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 2 2 0 2 1 (by decide)]

lemma component_222022 :
    leftComponent C A S x y z w ii 2 2 2 0 2 2 =
    rightComponent C A S x y z w ii 2 2 2 0 2 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 2 2 0 2 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 2 2 0 2 2 (by decide)]

lemma component_222100 :
    leftComponent C A S x y z w ii 2 2 2 1 0 0 =
    rightComponent C A S x y z w ii 2 2 2 1 0 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 2 2 1 0 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 2 2 1 0 0 (by decide)]

lemma component_222101 :
    leftComponent C A S x y z w ii 2 2 2 1 0 1 =
    rightComponent C A S x y z w ii 2 2 2 1 0 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 2 2 1 0 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 2 2 1 0 1 (by decide)]

lemma component_222102 :
    leftComponent C A S x y z w ii 2 2 2 1 0 2 =
    rightComponent C A S x y z w ii 2 2 2 1 0 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 2 2 1 0 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 2 2 1 0 2 (by decide)]

lemma component_222110 :
    leftComponent C A S x y z w ii 2 2 2 1 1 0 =
    rightComponent C A S x y z w ii 2 2 2 1 1 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 2 2 1 1 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 2 2 1 1 0 (by decide)]

lemma component_222111 :
    leftComponent C A S x y z w ii 2 2 2 1 1 1 =
    rightComponent C A S x y z w ii 2 2 2 1 1 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 2 2 1 1 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 2 2 1 1 1 (by decide)]

lemma component_222112 :
    leftComponent C A S x y z w ii 2 2 2 1 1 2 =
    rightComponent C A S x y z w ii 2 2 2 1 1 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 2 2 1 1 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 2 2 1 1 2 (by decide)]

lemma component_222120 :
    leftComponent C A S x y z w ii 2 2 2 1 2 0 =
    rightComponent C A S x y z w ii 2 2 2 1 2 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 2 2 1 2 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 2 2 1 2 0 (by decide)]

lemma component_222121 :
    leftComponent C A S x y z w ii 2 2 2 1 2 1 =
    rightComponent C A S x y z w ii 2 2 2 1 2 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 2 2 1 2 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 2 2 1 2 1 (by decide)]

lemma component_222122 :
    leftComponent C A S x y z w ii 2 2 2 1 2 2 =
    rightComponent C A S x y z w ii 2 2 2 1 2 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 2 2 1 2 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 2 2 1 2 2 (by decide)]

lemma component_222200 :
    leftComponent C A S x y z w ii 2 2 2 2 0 0 =
    rightComponent C A S x y z w ii 2 2 2 2 0 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 2 2 2 0 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 2 2 2 0 0 (by decide)]

lemma component_222201 :
    leftComponent C A S x y z w ii 2 2 2 2 0 1 =
    rightComponent C A S x y z w ii 2 2 2 2 0 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 2 2 2 0 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 2 2 2 0 1 (by decide)]

lemma component_222202 :
    leftComponent C A S x y z w ii 2 2 2 2 0 2 =
    rightComponent C A S x y z w ii 2 2 2 2 0 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 2 2 2 0 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 2 2 2 0 2 (by decide)]

lemma component_222210 :
    leftComponent C A S x y z w ii 2 2 2 2 1 0 =
    rightComponent C A S x y z w ii 2 2 2 2 1 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 2 2 2 1 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 2 2 2 1 0 (by decide)]

lemma component_222211 :
    leftComponent C A S x y z w ii 2 2 2 2 1 1 =
    rightComponent C A S x y z w ii 2 2 2 2 1 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 2 2 2 1 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 2 2 2 1 1 (by decide)]

lemma component_222212 :
    leftComponent C A S x y z w ii 2 2 2 2 1 2 =
    rightComponent C A S x y z w ii 2 2 2 2 1 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 2 2 2 1 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 2 2 2 1 2 (by decide)]

lemma component_222220 :
    leftComponent C A S x y z w ii 2 2 2 2 2 0 =
    rightComponent C A S x y z w ii 2 2 2 2 2 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 2 2 2 2 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 2 2 2 2 0 (by decide)]

lemma component_222221 :
    leftComponent C A S x y z w ii 2 2 2 2 2 1 =
    rightComponent C A S x y z w ii 2 2 2 2 2 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 2 2 2 2 2 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 2 2 2 2 2 1 (by decide)]

lemma component_222222 :
    leftComponent C A S x y z w ii 2 2 2 2 2 2 =
    rightComponent C A S x y z w ii 2 2 2 2 2 2 := by
  simp only [leftComponent, rightComponent, Fin.sum_univ_three, numerator, Fin.val_zero, Fin.val_one, finThreeTwo, mul_zero, zero_mul, zero_add, add_zero]
  ; ring

include hC hA hS hy hw hi in
lemma block_200 (d e f : Fin 3) :
    leftComponent C A S x y z w ii 2 0 0 d e f =
    rightComponent C A S x y z w ii 2 0 0 d e f := by
  fin_cases d <;> fin_cases e <;> fin_cases f
  · exact component_200000 C A S x y z w ii
  · exact component_200001 C A S x y z w ii
  · exact component_200002 C A S x y z w ii hC hA hS hy hw hi
  · exact component_200010 C A S x y z w ii
  · exact component_200011 C A S x y z w ii hC hA hS hy hw hi
  · exact component_200012 C A S x y z w ii
  · exact component_200020 C A S x y z w ii hC hA hS hy hw hi
  · exact component_200021 C A S x y z w ii
  · exact component_200022 C A S x y z w ii
  · exact component_200100 C A S x y z w ii
  · exact component_200101 C A S x y z w ii hC hA hS hy hw
  · exact component_200102 C A S x y z w ii
  · exact component_200110 C A S x y z w ii hC hA hS hy hw
  · exact component_200111 C A S x y z w ii
  · exact component_200112 C A S x y z w ii
  · exact component_200120 C A S x y z w ii
  · exact component_200121 C A S x y z w ii
  · exact component_200122 C A S x y z w ii
  · exact component_200200 C A S x y z w ii
  · exact component_200201 C A S x y z w ii
  · exact component_200202 C A S x y z w ii
  · exact component_200210 C A S x y z w ii
  · exact component_200211 C A S x y z w ii
  · exact component_200212 C A S x y z w ii
  · exact component_200220 C A S x y z w ii
  · exact component_200221 C A S x y z w ii
  · exact component_200222 C A S x y z w ii

include hC hA hS hy hw hi in
lemma block_201 (d e f : Fin 3) :
    leftComponent C A S x y z w ii 2 0 1 d e f =
    rightComponent C A S x y z w ii 2 0 1 d e f := by
  fin_cases d <;> fin_cases e <;> fin_cases f
  · exact component_201000 C A S x y z w ii
  · exact component_201001 C A S x y z w ii
  · exact component_201002 C A S x y z w ii
  · exact component_201010 C A S x y z w ii
  · exact component_201011 C A S x y z w ii
  · exact component_201012 C A S x y z w ii hC hA hS hy hw hi
  · exact component_201020 C A S x y z w ii
  · exact component_201021 C A S x y z w ii
  · exact component_201022 C A S x y z w ii
  · exact component_201100 C A S x y z w ii
  · exact component_201101 C A S x y z w ii
  · exact component_201102 C A S x y z w ii hC hA hS hy hw hi
  · exact component_201110 C A S x y z w ii
  · exact component_201111 C A S x y z w ii hC hA hS hy hw hi
  · exact component_201112 C A S x y z w ii
  · exact component_201120 C A S x y z w ii hC hA hS hy hw hi
  · exact component_201121 C A S x y z w ii
  · exact component_201122 C A S x y z w ii
  · exact component_201200 C A S x y z w ii
  · exact component_201201 C A S x y z w ii
  · exact component_201202 C A S x y z w ii
  · exact component_201210 C A S x y z w ii hC hA hS hy hw hi
  · exact component_201211 C A S x y z w ii
  · exact component_201212 C A S x y z w ii
  · exact component_201220 C A S x y z w ii
  · exact component_201221 C A S x y z w ii
  · exact component_201222 C A S x y z w ii

include hC hA hS hy hw hi in
lemma block_202 (d e f : Fin 3) :
    leftComponent C A S x y z w ii 2 0 2 d e f =
    rightComponent C A S x y z w ii 2 0 2 d e f := by
  fin_cases d <;> fin_cases e <;> fin_cases f
  · exact component_202000 C A S x y z w ii
  · exact component_202001 C A S x y z w ii
  · exact component_202002 C A S x y z w ii
  · exact component_202010 C A S x y z w ii
  · exact component_202011 C A S x y z w ii
  · exact component_202012 C A S x y z w ii
  · exact component_202020 C A S x y z w ii
  · exact component_202021 C A S x y z w ii
  · exact component_202022 C A S x y z w ii hC hA hS hy hw hi
  · exact component_202100 C A S x y z w ii
  · exact component_202101 C A S x y z w ii
  · exact component_202102 C A S x y z w ii
  · exact component_202110 C A S x y z w ii
  · exact component_202111 C A S x y z w ii
  · exact component_202112 C A S x y z w ii hC hA hS hy hw hi
  · exact component_202120 C A S x y z w ii
  · exact component_202121 C A S x y z w ii hC hA hS hy hw hi
  · exact component_202122 C A S x y z w ii
  · exact component_202200 C A S x y z w ii
  · exact component_202201 C A S x y z w ii
  · exact component_202202 C A S x y z w ii hC hA hS hy hw hi
  · exact component_202210 C A S x y z w ii
  · exact component_202211 C A S x y z w ii hC hA hS hy hw hi
  · exact component_202212 C A S x y z w ii
  · exact component_202220 C A S x y z w ii hC hA hS hy hw hi
  · exact component_202221 C A S x y z w ii
  · exact component_202222 C A S x y z w ii

include hC hA hS hy hw hi in
lemma block_210 (d e f : Fin 3) :
    leftComponent C A S x y z w ii 2 1 0 d e f =
    rightComponent C A S x y z w ii 2 1 0 d e f := by
  fin_cases d <;> fin_cases e <;> fin_cases f
  · exact component_210000 C A S x y z w ii
  · exact component_210001 C A S x y z w ii
  · exact component_210002 C A S x y z w ii
  · exact component_210010 C A S x y z w ii
  · exact component_210011 C A S x y z w ii
  · exact component_210012 C A S x y z w ii
  · exact component_210020 C A S x y z w ii
  · exact component_210021 C A S x y z w ii hC hA hS hy hw hi
  · exact component_210022 C A S x y z w ii
  · exact component_210100 C A S x y z w ii
  · exact component_210101 C A S x y z w ii
  · exact component_210102 C A S x y z w ii hC hA hS hy hw hi
  · exact component_210110 C A S x y z w ii
  · exact component_210111 C A S x y z w ii hC hA hS hy hw
  · exact component_210112 C A S x y z w ii
  · exact component_210120 C A S x y z w ii hC hA hS hy hw hi
  · exact component_210121 C A S x y z w ii
  · exact component_210122 C A S x y z w ii
  · exact component_210200 C A S x y z w ii
  · exact component_210201 C A S x y z w ii hC hA hS hy hw hi
  · exact component_210202 C A S x y z w ii
  · exact component_210210 C A S x y z w ii
  · exact component_210211 C A S x y z w ii
  · exact component_210212 C A S x y z w ii
  · exact component_210220 C A S x y z w ii
  · exact component_210221 C A S x y z w ii
  · exact component_210222 C A S x y z w ii

include hC hA hS hy hw hi in
lemma block_211 (d e f : Fin 3) :
    leftComponent C A S x y z w ii 2 1 1 d e f =
    rightComponent C A S x y z w ii 2 1 1 d e f := by
  fin_cases d <;> fin_cases e <;> fin_cases f
  · exact component_211000 C A S x y z w ii
  · exact component_211001 C A S x y z w ii
  · exact component_211002 C A S x y z w ii
  · exact component_211010 C A S x y z w ii
  · exact component_211011 C A S x y z w ii
  · exact component_211012 C A S x y z w ii
  · exact component_211020 C A S x y z w ii
  · exact component_211021 C A S x y z w ii
  · exact component_211022 C A S x y z w ii hC hA hS hy hw hi
  · exact component_211100 C A S x y z w ii
  · exact component_211101 C A S x y z w ii
  · exact component_211102 C A S x y z w ii
  · exact component_211110 C A S x y z w ii
  · exact component_211111 C A S x y z w ii
  · exact component_211112 C A S x y z w ii hC hA hS hy hw hi
  · exact component_211120 C A S x y z w ii
  · exact component_211121 C A S x y z w ii hC hA hS hy hw hi
  · exact component_211122 C A S x y z w ii
  · exact component_211200 C A S x y z w ii
  · exact component_211201 C A S x y z w ii
  · exact component_211202 C A S x y z w ii hC hA hS hy hw hi
  · exact component_211210 C A S x y z w ii
  · exact component_211211 C A S x y z w ii
  · exact component_211212 C A S x y z w ii
  · exact component_211220 C A S x y z w ii hC hA hS hy hw
  · exact component_211221 C A S x y z w ii
  · exact component_211222 C A S x y z w ii

include hy in
lemma block_212 (d e f : Fin 3) :
    leftComponent C A S x y z w ii 2 1 2 d e f =
    rightComponent C A S x y z w ii 2 1 2 d e f := by
  fin_cases d <;> fin_cases e <;> fin_cases f
  · exact component_212000 C A S x y z w ii
  · exact component_212001 C A S x y z w ii
  · exact component_212002 C A S x y z w ii
  · exact component_212010 C A S x y z w ii
  · exact component_212011 C A S x y z w ii
  · exact component_212012 C A S x y z w ii
  · exact component_212020 C A S x y z w ii
  · exact component_212021 C A S x y z w ii
  · exact component_212022 C A S x y z w ii
  · exact component_212100 C A S x y z w ii
  · exact component_212101 C A S x y z w ii
  · exact component_212102 C A S x y z w ii
  · exact component_212110 C A S x y z w ii
  · exact component_212111 C A S x y z w ii
  · exact component_212112 C A S x y z w ii
  · exact component_212120 C A S x y z w ii
  · exact component_212121 C A S x y z w ii
  · exact component_212122 C A S x y z w ii
  · exact component_212200 C A S x y z w ii
  · exact component_212201 C A S x y z w ii
  · exact component_212202 C A S x y z w ii
  · exact component_212210 C A S x y z w ii
  · exact component_212211 C A S x y z w ii
  · exact component_212212 C A S x y z w ii
  · exact component_212220 C A S x y z w ii
  · exact component_212221 C A S x y z w ii hy
  · exact component_212222 C A S x y z w ii

include hC hA hS hy hw hi in
lemma block_220 (d e f : Fin 3) :
    leftComponent C A S x y z w ii 2 2 0 d e f =
    rightComponent C A S x y z w ii 2 2 0 d e f := by
  fin_cases d <;> fin_cases e <;> fin_cases f
  · exact component_220000 C A S x y z w ii
  · exact component_220001 C A S x y z w ii
  · exact component_220002 C A S x y z w ii
  · exact component_220010 C A S x y z w ii
  · exact component_220011 C A S x y z w ii
  · exact component_220012 C A S x y z w ii
  · exact component_220020 C A S x y z w ii
  · exact component_220021 C A S x y z w ii
  · exact component_220022 C A S x y z w ii hC hA hS hy hw hi
  · exact component_220100 C A S x y z w ii
  · exact component_220101 C A S x y z w ii
  · exact component_220102 C A S x y z w ii
  · exact component_220110 C A S x y z w ii
  · exact component_220111 C A S x y z w ii
  · exact component_220112 C A S x y z w ii hC hA hS hy hw hi
  · exact component_220120 C A S x y z w ii
  · exact component_220121 C A S x y z w ii hC hA hS hy hw
  · exact component_220122 C A S x y z w ii
  · exact component_220200 C A S x y z w ii
  · exact component_220201 C A S x y z w ii
  · exact component_220202 C A S x y z w ii hC hA hS hy hw hi
  · exact component_220210 C A S x y z w ii
  · exact component_220211 C A S x y z w ii hC hA hS hy hw
  · exact component_220212 C A S x y z w ii
  · exact component_220220 C A S x y z w ii
  · exact component_220221 C A S x y z w ii
  · exact component_220222 C A S x y z w ii

include hC hA hS hy hw in
lemma block_221 (d e f : Fin 3) :
    leftComponent C A S x y z w ii 2 2 1 d e f =
    rightComponent C A S x y z w ii 2 2 1 d e f := by
  fin_cases d <;> fin_cases e <;> fin_cases f
  · exact component_221000 C A S x y z w ii
  · exact component_221001 C A S x y z w ii
  · exact component_221002 C A S x y z w ii
  · exact component_221010 C A S x y z w ii
  · exact component_221011 C A S x y z w ii
  · exact component_221012 C A S x y z w ii
  · exact component_221020 C A S x y z w ii
  · exact component_221021 C A S x y z w ii
  · exact component_221022 C A S x y z w ii
  · exact component_221100 C A S x y z w ii
  · exact component_221101 C A S x y z w ii
  · exact component_221102 C A S x y z w ii
  · exact component_221110 C A S x y z w ii
  · exact component_221111 C A S x y z w ii
  · exact component_221112 C A S x y z w ii
  · exact component_221120 C A S x y z w ii
  · exact component_221121 C A S x y z w ii
  · exact component_221122 C A S x y z w ii hC hA hS hy hw
  · exact component_221200 C A S x y z w ii
  · exact component_221201 C A S x y z w ii
  · exact component_221202 C A S x y z w ii
  · exact component_221210 C A S x y z w ii
  · exact component_221211 C A S x y z w ii
  · exact component_221212 C A S x y z w ii hy
  · exact component_221220 C A S x y z w ii
  · exact component_221221 C A S x y z w ii
  · exact component_221222 C A S x y z w ii

lemma block_222 (d e f : Fin 3) :
    leftComponent C A S x y z w ii 2 2 2 d e f =
    rightComponent C A S x y z w ii 2 2 2 d e f := by
  fin_cases d <;> fin_cases e <;> fin_cases f
  · exact component_222000 C A S x y z w ii
  · exact component_222001 C A S x y z w ii
  · exact component_222002 C A S x y z w ii
  · exact component_222010 C A S x y z w ii
  · exact component_222011 C A S x y z w ii
  · exact component_222012 C A S x y z w ii
  · exact component_222020 C A S x y z w ii
  · exact component_222021 C A S x y z w ii
  · exact component_222022 C A S x y z w ii
  · exact component_222100 C A S x y z w ii
  · exact component_222101 C A S x y z w ii
  · exact component_222102 C A S x y z w ii
  · exact component_222110 C A S x y z w ii
  · exact component_222111 C A S x y z w ii
  · exact component_222112 C A S x y z w ii
  · exact component_222120 C A S x y z w ii
  · exact component_222121 C A S x y z w ii
  · exact component_222122 C A S x y z w ii
  · exact component_222200 C A S x y z w ii
  · exact component_222201 C A S x y z w ii
  · exact component_222202 C A S x y z w ii
  · exact component_222210 C A S x y z w ii
  · exact component_222211 C A S x y z w ii
  · exact component_222212 C A S x y z w ii
  · exact component_222220 C A S x y z w ii
  · exact component_222221 C A S x y z w ii
  · exact component_222222 C A S x y z w ii

end Algebra
end CriticalHoneycomb.Transfer.YangBaxter

end OAI
