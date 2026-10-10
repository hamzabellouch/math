import OAI.Combinatorics.HoneycombChords.YangBaxterPolynomialsPositive
import OAI.Combinatorics.HoneycombChords.YangBaxterPolynomialsZero
import OAI.Combinatorics.HoneycombChords.YangBaxterSupport
import Mathlib.Tactic.FinCases

namespace OAI

/-! Yang–Baxter components with first spin zero.

This development follows the finite strip transfer calculation for critical honeycomb
walks in the companion paper on uniform marked polygon estimates. -/


namespace CriticalHoneycomb.Transfer.YangBaxter
open scoped BigOperators

section Algebra
variable (C A S x y z w ii : ℂ)
variable (hC : C = (2*S+1)*A) (hA : A^2 = (1-S)/2)
  (hS : S^2 = 1/2) (hy : y^2+x^2=1) (hw : w^2+z^2=1) (hi : ii^2+1=0)

include hC hA hS hy hw in
lemma component_101002 :
    leftComponent C A S x y z w ii 1 0 1 0 0 2 =
    rightComponent C A S x y z w ii 1 0 1 0 0 2 := by
  simp only [leftComponent, rightComponent, Fin.sum_univ_three, numerator, Fin.val_zero, Fin.val_one, finThreeTwo, mul_zero, zero_mul, zero_add, add_zero]
  have hp := polynomial_101002 C A S x y z w ii hC hA hS hy hw
  dsimp only [poly_101002_0, complexAdd, complexMul, complexPow] at hp
  linear_combination hp

include hC hA hS hy hw hi in
lemma component_101020 :
    leftComponent C A S x y z w ii 1 0 1 0 2 0 =
    rightComponent C A S x y z w ii 1 0 1 0 2 0 := by
  simp only [leftComponent, rightComponent, Fin.sum_univ_three, numerator, Fin.val_zero, Fin.val_one, finThreeTwo, mul_zero, zero_mul, zero_add, add_zero]
  have hp := polynomial_101020 C A S x y z w ii hC hA hS hy hw hi
  dsimp only [poly_101020_0, complexAdd, complexMul, complexPow] at hp
  linear_combination hp

include hC hA hS hy hw hi in
lemma component_101110 :
    leftComponent C A S x y z w ii 1 0 1 1 1 0 =
    rightComponent C A S x y z w ii 1 0 1 1 1 0 := by
  simp only [leftComponent, rightComponent, Fin.sum_univ_three, numerator, Fin.val_zero, Fin.val_one, finThreeTwo, mul_zero, zero_mul, zero_add, add_zero]
  have hp := polynomial_101110 C A S x y z w ii hC hA hS hy hw hi
  dsimp only [poly_101110_0, complexAdd, complexMul, complexPow] at hp
  linear_combination hp

include hC hA hS hy hw hi in
lemma component_102111 :
    leftComponent C A S x y z w ii 1 0 2 1 1 1 =
    rightComponent C A S x y z w ii 1 0 2 1 1 1 := by
  simp only [leftComponent, rightComponent, Fin.sum_univ_three, numerator, Fin.val_zero, Fin.val_one, finThreeTwo, mul_zero, zero_mul, zero_add, add_zero]
  have hp := polynomial_102111 C A S x y z w ii hC hA hS hy hw hi
  dsimp only [poly_102111_0, complexAdd, complexMul, complexPow] at hp
  linear_combination hp

include hC hA hS hy hw hi in
lemma component_110002 :
    leftComponent C A S x y z w ii 1 1 0 0 0 2 =
    rightComponent C A S x y z w ii 1 1 0 0 0 2 := by
  simp only [leftComponent, rightComponent, Fin.sum_univ_three, numerator, Fin.val_zero, Fin.val_one, finThreeTwo, mul_zero, zero_mul, zero_add, add_zero]
  have hp := polynomial_110002 C A S x y z w ii hC hA hS hy hw hi
  dsimp only [poly_110002_0, complexAdd, complexMul, complexPow] at hp
  linear_combination hp

include hC hA hS hy hw hi in
lemma component_110011 :
    leftComponent C A S x y z w ii 1 1 0 0 1 1 =
    rightComponent C A S x y z w ii 1 1 0 0 1 1 := by
  simp only [leftComponent, rightComponent, Fin.sum_univ_three, numerator, Fin.val_zero, Fin.val_one, finThreeTwo, mul_zero, zero_mul, zero_add, add_zero]
  have hp := polynomial_110011 C A S x y z w ii hC hA hS hy hw hi
  dsimp only [poly_110011_0, complexAdd, complexMul, complexPow] at hp
  linear_combination hp

include hC hA hS hy hw hi in
lemma component_110020 :
    leftComponent C A S x y z w ii 1 1 0 0 2 0 =
    rightComponent C A S x y z w ii 1 1 0 0 2 0 := by
  simp only [leftComponent, rightComponent, Fin.sum_univ_three, numerator, Fin.val_zero, Fin.val_one, finThreeTwo, mul_zero, zero_mul, zero_add, add_zero]
  have hp := polynomial_110020 C A S x y z w ii hC hA hS hy hw hi
  dsimp only [poly_110020_0, complexAdd, complexMul, complexPow] at hp
  linear_combination hp

include hC hA hS hy hw in
lemma component_111012 :
    leftComponent C A S x y z w ii 1 1 1 0 1 2 =
    rightComponent C A S x y z w ii 1 1 1 0 1 2 := by
  simp only [leftComponent, rightComponent, Fin.sum_univ_three, numerator, Fin.val_zero, Fin.val_one, finThreeTwo, mul_zero, zero_mul, zero_add, add_zero]
  have hp := polynomial_111012 C A S x y z w ii hC hA hS hy hw
  dsimp only [poly_111012_0, complexAdd, complexMul, complexPow] at hp
  linear_combination hp

include hC hA hS hy hw hi in
lemma component_111021 :
    leftComponent C A S x y z w ii 1 1 1 0 2 1 =
    rightComponent C A S x y z w ii 1 1 1 0 2 1 := by
  simp only [leftComponent, rightComponent, Fin.sum_univ_three, numerator, Fin.val_zero, Fin.val_one, finThreeTwo, mul_zero, zero_mul, zero_add, add_zero]
  have hp := polynomial_111021 C A S x y z w ii hC hA hS hy hw hi
  dsimp only [poly_111021_0, complexAdd, complexMul, complexPow] at hp
  linear_combination hp

include hC hA hS hy hw hi in
lemma component_111102 :
    leftComponent C A S x y z w ii 1 1 1 1 0 2 =
    rightComponent C A S x y z w ii 1 1 1 1 0 2 := by
  simp only [leftComponent, rightComponent, Fin.sum_univ_three, numerator, Fin.val_zero, Fin.val_one, finThreeTwo, mul_zero, zero_mul, zero_add, add_zero]
  have hp := polynomial_111102 C A S x y z w ii hC hA hS hy hw hi
  dsimp only [poly_111102_0, complexAdd, complexMul, complexPow] at hp
  linear_combination hp

include hC hA hS hy hw in
lemma component_112022 :
    leftComponent C A S x y z w ii 1 1 2 0 2 2 =
    rightComponent C A S x y z w ii 1 1 2 0 2 2 := by
  simp only [leftComponent, rightComponent, Fin.sum_univ_three, numerator, Fin.val_zero, Fin.val_one, finThreeTwo, mul_zero, zero_mul, zero_add, add_zero]
  have hp := polynomial_112022 C A S x y z w ii hC hA hS hy hw
  dsimp only [poly_112022_0, complexAdd, complexMul, complexPow] at hp
  linear_combination hp

include hC hA hS hy hw hi in
lemma component_120012 :
    leftComponent C A S x y z w ii 1 2 0 0 1 2 =
    rightComponent C A S x y z w ii 1 2 0 0 1 2 := by
  simp only [leftComponent, rightComponent, Fin.sum_univ_three, numerator, Fin.val_zero, Fin.val_one, finThreeTwo, mul_zero, zero_mul, zero_add, add_zero]
  have hp := polynomial_120012 C A S x y z w ii hC hA hS hy hw hi
  dsimp only [poly_120012_0, complexAdd, complexMul, complexPow] at hp
  linear_combination hp

include hC hA hS hy hw hi in
lemma component_120021 :
    leftComponent C A S x y z w ii 1 2 0 0 2 1 =
    rightComponent C A S x y z w ii 1 2 0 0 2 1 := by
  simp only [leftComponent, rightComponent, Fin.sum_univ_three, numerator, Fin.val_zero, Fin.val_one, finThreeTwo, mul_zero, zero_mul, zero_add, add_zero]
  have hp := polynomial_120021 C A S x y z w ii hC hA hS hy hw hi
  dsimp only [poly_120021_0, complexAdd, complexMul, complexPow] at hp
  linear_combination hp

include hC hA hS hy hw in
lemma component_121022 :
    leftComponent C A S x y z w ii 1 2 1 0 2 2 =
    rightComponent C A S x y z w ii 1 2 1 0 2 2 := by
  simp only [leftComponent, rightComponent, Fin.sum_univ_three, numerator, Fin.val_zero, Fin.val_one, finThreeTwo, mul_zero, zero_mul, zero_add, add_zero]
  have hp := polynomial_121022 C A S x y z w ii hC hA hS hy hw
  dsimp only [poly_121022_0, complexAdd, complexMul, complexPow] at hp
  linear_combination hp

include hC hA hS hy hw in
lemma component_100001 :
    leftComponent C A S x y z w ii 1 0 0 0 0 1 =
    rightComponent C A S x y z w ii 1 0 0 0 0 1 := by
  simp only [leftComponent, rightComponent, Fin.sum_univ_three, numerator, Fin.val_zero, Fin.val_one, finThreeTwo, mul_zero, zero_mul, zero_add, add_zero]
  have hp := polynomial_001100 C A S x y z w ii hC hA hS hy hw
  dsimp only [poly_001100_0, complexAdd, complexMul, complexPow] at hp
  linear_combination (-1:ℂ)/1*hp

include hC hA hS hy hw hi in
lemma component_101011 :
    leftComponent C A S x y z w ii 1 0 1 0 1 1 =
    rightComponent C A S x y z w ii 1 0 1 0 1 1 := by
  simp only [leftComponent, rightComponent, Fin.sum_univ_three, numerator, Fin.val_zero, Fin.val_one, finThreeTwo, mul_zero, zero_mul, zero_add, add_zero]
  have hp := polynomial_011101 C A S x y z w ii hC hA hS hy hw hi
  dsimp only [poly_011101_0, complexAdd, complexMul, complexPow] at hp
  linear_combination (-1:ℂ)/1*hp

include hC hA hS hy hw in
lemma component_101200 :
    leftComponent C A S x y z w ii 1 0 1 2 0 0 =
    rightComponent C A S x y z w ii 1 0 1 2 0 0 := by
  simp only [leftComponent, rightComponent, Fin.sum_univ_three, numerator, Fin.val_zero, Fin.val_one, finThreeTwo, mul_zero, zero_mul, zero_add, add_zero]
  have hp := polynomial_022121 C A S x y z w ii hC hA hS hy hw
  dsimp only [poly_022121_0, complexAdd, complexMul, complexPow] at hp
  linear_combination (-1:ℂ)/1*hp

include hC hA hS hy hw hi in
lemma component_102012 :
    leftComponent C A S x y z w ii 1 0 2 0 1 2 =
    rightComponent C A S x y z w ii 1 0 2 0 1 2 := by
  simp only [leftComponent, rightComponent, Fin.sum_univ_three, numerator, Fin.val_zero, Fin.val_one, finThreeTwo, mul_zero, zero_mul, zero_add, add_zero]
  have hp := polynomial_012102 C A S x y z w ii hC hA hS hy hw hi
  dsimp only [poly_012102_0, complexAdd, complexMul, complexPow] at hp
  linear_combination (-1:ℂ)/1*hp

include hC hA hS hy hw hi in
lemma component_102021 :
    leftComponent C A S x y z w ii 1 0 2 0 2 1 =
    rightComponent C A S x y z w ii 1 0 2 0 2 1 := by
  simp only [leftComponent, rightComponent, Fin.sum_univ_three, numerator, Fin.val_zero, Fin.val_one, finThreeTwo, mul_zero, zero_mul, zero_add, add_zero]
  have hp := polynomial_021102 C A S x y z w ii hC hA hS hy hw hi
  dsimp only [poly_021102_0, complexAdd, complexMul, complexPow] at hp
  linear_combination (-1:ℂ)/1*hp

include hC hA hS hy hw hi in
lemma component_102201 :
    leftComponent C A S x y z w ii 1 0 2 2 0 1 =
    rightComponent C A S x y z w ii 1 0 2 2 0 1 := by
  simp only [leftComponent, rightComponent, Fin.sum_univ_three, numerator, Fin.val_zero, Fin.val_one, finThreeTwo, mul_zero, zero_mul, zero_add, add_zero]
  have hp := polynomial_021120 C A S x y z w ii hC hA hS hy hw hi
  dsimp only [poly_021120_0, complexAdd, complexMul, complexPow] at hp
  linear_combination (-1:ℂ)/1*hp

include hC hA hS hy hw hi in
lemma component_102210 :
    leftComponent C A S x y z w ii 1 0 2 2 1 0 =
    rightComponent C A S x y z w ii 1 0 2 2 1 0 := by
  simp only [leftComponent, rightComponent, Fin.sum_univ_three, numerator, Fin.val_zero, Fin.val_one, finThreeTwo, mul_zero, zero_mul, zero_add, add_zero]
  have hp := polynomial_012120 C A S x y z w ii hC hA hS hy hw hi
  dsimp only [poly_012120_0, complexAdd, complexMul, complexPow] at hp
  linear_combination (-1:ℂ)/1*hp

include hC hA hS hy hw hi in
lemma component_110101 :
    leftComponent C A S x y z w ii 1 1 0 1 0 1 =
    rightComponent C A S x y z w ii 1 1 0 1 0 1 := by
  simp only [leftComponent, rightComponent, Fin.sum_univ_three, numerator, Fin.val_zero, Fin.val_one, finThreeTwo, mul_zero, zero_mul, zero_add, add_zero]
  have hp := polynomial_101110 C A S x y z w ii hC hA hS hy hw hi
  dsimp only [poly_101110_0, complexAdd, complexMul, complexPow] at hp
  linear_combination (-1:ℂ)/1*hp

include hC hA hS hy hw in
lemma component_110200 :
    leftComponent C A S x y z w ii 1 1 0 2 0 0 =
    rightComponent C A S x y z w ii 1 1 0 2 0 0 := by
  simp only [leftComponent, rightComponent, Fin.sum_univ_three, numerator, Fin.val_zero, Fin.val_one, finThreeTwo, mul_zero, zero_mul, zero_add, add_zero]
  have hp := polynomial_022112 C A S x y z w ii hC hA hS hy hw
  dsimp only [poly_022112_0, complexAdd, complexMul, complexPow] at hp
  linear_combination (-1:ℂ)/1*hp

include hC hA hS hy hw hi in
lemma component_111120 :
    leftComponent C A S x y z w ii 1 1 1 1 2 0 =
    rightComponent C A S x y z w ii 1 1 1 1 2 0 := by
  simp only [leftComponent, rightComponent, Fin.sum_univ_three, numerator, Fin.val_zero, Fin.val_one, finThreeTwo, mul_zero, zero_mul, zero_add, add_zero]
  have hp := polynomial_102111 C A S x y z w ii hC hA hS hy hw hi
  dsimp only [poly_102111_0, complexAdd, complexMul, complexPow] at hp
  linear_combination (-1:ℂ)/1*hp

include hC hA hS hy hw hi in
lemma component_111201 :
    leftComponent C A S x y z w ii 1 1 1 2 0 1 =
    rightComponent C A S x y z w ii 1 1 1 2 0 1 := by
  simp only [leftComponent, rightComponent, Fin.sum_univ_three, numerator, Fin.val_zero, Fin.val_one, finThreeTwo, mul_zero, zero_mul, zero_add, add_zero]
  have hp := polynomial_021111 C A S x y z w ii hC hA hS hy hw hi
  dsimp only [poly_021111_0, complexAdd, complexMul, complexPow] at hp
  linear_combination (-1:ℂ)/1*hp

include hC hA hS hy hw in
lemma component_111210 :
    leftComponent C A S x y z w ii 1 1 1 2 1 0 =
    rightComponent C A S x y z w ii 1 1 1 2 1 0 := by
  simp only [leftComponent, rightComponent, Fin.sum_univ_three, numerator, Fin.val_zero, Fin.val_one, finThreeTwo, mul_zero, zero_mul, zero_add, add_zero]
  have hp := polynomial_012111 C A S x y z w ii hC hA hS hy hw
  dsimp only [poly_012111_0, complexAdd, complexMul, complexPow] at hp
  linear_combination (-1:ℂ)/1*hp

include hC hA hS hy hw hi in
lemma component_112121 :
    leftComponent C A S x y z w ii 1 1 2 1 2 1 =
    rightComponent C A S x y z w ii 1 1 2 1 2 1 := by
  simp only [leftComponent, rightComponent, Fin.sum_univ_three, numerator, Fin.val_zero, Fin.val_one, finThreeTwo, mul_zero, zero_mul, zero_add, add_zero]
  have hp := polynomial_101110 C A S x y z w ii hC hA hS hy hw hi
  dsimp only [poly_101110_0, complexAdd, complexMul, complexPow] at hp
  linear_combination (-1:ℂ)/1*hp

include hC hA hS hy hw hi in
lemma component_112202 :
    leftComponent C A S x y z w ii 1 1 2 2 0 2 =
    rightComponent C A S x y z w ii 1 1 2 2 0 2 := by
  simp only [leftComponent, rightComponent, Fin.sum_univ_three, numerator, Fin.val_zero, Fin.val_one, finThreeTwo, mul_zero, zero_mul, zero_add, add_zero]
  have hp := polynomial_020110 C A S x y z w ii hC hA hS hy hw hi
  dsimp only [poly_020110_0, complexAdd, complexMul, complexPow] at hp
  linear_combination (-1:ℂ)/1*hp

include hC hA hS hy hw hi in
lemma component_112211 :
    leftComponent C A S x y z w ii 1 1 2 2 1 1 =
    rightComponent C A S x y z w ii 1 1 2 2 1 1 := by
  simp only [leftComponent, rightComponent, Fin.sum_univ_three, numerator, Fin.val_zero, Fin.val_one, finThreeTwo, mul_zero, zero_mul, zero_add, add_zero]
  have hp := polynomial_011110 C A S x y z w ii hC hA hS hy hw hi
  dsimp only [poly_011110_0, complexAdd, complexMul, complexPow] at hp
  linear_combination (-1:ℂ)/1*hp

include hC hA hS hy hw hi in
lemma component_112220 :
    leftComponent C A S x y z w ii 1 1 2 2 2 0 =
    rightComponent C A S x y z w ii 1 1 2 2 2 0 := by
  simp only [leftComponent, rightComponent, Fin.sum_univ_three, numerator, Fin.val_zero, Fin.val_one, finThreeTwo, mul_zero, zero_mul, zero_add, add_zero]
  have hp := polynomial_002110 C A S x y z w ii hC hA hS hy hw hi
  dsimp only [poly_002110_0, complexAdd, complexMul, complexPow] at hp
  linear_combination (-1:ℂ)/1*hp

include hC hA hS hy hw hi in
lemma component_120111 :
    leftComponent C A S x y z w ii 1 2 0 1 1 1 =
    rightComponent C A S x y z w ii 1 2 0 1 1 1 := by
  simp only [leftComponent, rightComponent, Fin.sum_univ_three, numerator, Fin.val_zero, Fin.val_one, finThreeTwo, mul_zero, zero_mul, zero_add, add_zero]
  have hp := polynomial_111102 C A S x y z w ii hC hA hS hy hw hi
  dsimp only [poly_111102_0, complexAdd, complexMul, complexPow] at hp
  linear_combination (-1:ℂ)/1*hp

include hC hA hS hy hw hi in
lemma component_120201 :
    leftComponent C A S x y z w ii 1 2 0 2 0 1 =
    rightComponent C A S x y z w ii 1 2 0 2 0 1 := by
  simp only [leftComponent, rightComponent, Fin.sum_univ_three, numerator, Fin.val_zero, Fin.val_one, finThreeTwo, mul_zero, zero_mul, zero_add, add_zero]
  have hp := polynomial_021102 C A S x y z w ii hC hA hS hy hw hi
  dsimp only [poly_021102_0, complexAdd, complexMul, complexPow] at hp
  linear_combination (-1:ℂ)/1*hp

include hC hA hS hy hw hi in
lemma component_120210 :
    leftComponent C A S x y z w ii 1 2 0 2 1 0 =
    rightComponent C A S x y z w ii 1 2 0 2 1 0 := by
  simp only [leftComponent, rightComponent, Fin.sum_univ_three, numerator, Fin.val_zero, Fin.val_one, finThreeTwo, mul_zero, zero_mul, zero_add, add_zero]
  have hp := polynomial_012102 C A S x y z w ii hC hA hS hy hw hi
  dsimp only [poly_012102_0, complexAdd, complexMul, complexPow] at hp
  linear_combination (-1:ℂ)/1*hp

include hC hA hS hy hw hi in
lemma component_121112 :
    leftComponent C A S x y z w ii 1 2 1 1 1 2 =
    rightComponent C A S x y z w ii 1 2 1 1 1 2 := by
  simp only [leftComponent, rightComponent, Fin.sum_univ_three, numerator, Fin.val_zero, Fin.val_one, finThreeTwo, mul_zero, zero_mul, zero_add, add_zero]
  have hp := polynomial_101110 C A S x y z w ii hC hA hS hy hw hi
  dsimp only [poly_101110_0, complexAdd, complexMul, complexPow] at hp
  linear_combination (1:ℂ)/1*hp

include hC hA hS hy hw hi in
lemma component_121202 :
    leftComponent C A S x y z w ii 1 2 1 2 0 2 =
    rightComponent C A S x y z w ii 1 2 1 2 0 2 := by
  simp only [leftComponent, rightComponent, Fin.sum_univ_three, numerator, Fin.val_zero, Fin.val_one, finThreeTwo, mul_zero, zero_mul, zero_add, add_zero]
  have hp := polynomial_020101 C A S x y z w ii hC hA hS hy hw hi
  dsimp only [poly_020101_0, complexAdd, complexMul, complexPow] at hp
  linear_combination (-1:ℂ)/1*hp

include hC hA hS hy hw hi in
lemma component_121211 :
    leftComponent C A S x y z w ii 1 2 1 2 1 1 =
    rightComponent C A S x y z w ii 1 2 1 2 1 1 := by
  simp only [leftComponent, rightComponent, Fin.sum_univ_three, numerator, Fin.val_zero, Fin.val_one, finThreeTwo, mul_zero, zero_mul, zero_add, add_zero]
  have hp := polynomial_011101 C A S x y z w ii hC hA hS hy hw hi
  dsimp only [poly_011101_0, complexAdd, complexMul, complexPow] at hp
  linear_combination (-1:ℂ)/1*hp

include hC hA hS hy hw in
lemma component_121220 :
    leftComponent C A S x y z w ii 1 2 1 2 2 0 =
    rightComponent C A S x y z w ii 1 2 1 2 2 0 := by
  simp only [leftComponent, rightComponent, Fin.sum_univ_three, numerator, Fin.val_zero, Fin.val_one, finThreeTwo, mul_zero, zero_mul, zero_add, add_zero]
  have hp := polynomial_002101 C A S x y z w ii hC hA hS hy hw
  dsimp only [poly_002101_0, complexAdd, complexMul, complexPow] at hp
  linear_combination (-1:ℂ)/1*hp

include hC hA hS hy hw in
lemma component_122221 :
    leftComponent C A S x y z w ii 1 2 2 2 2 1 =
    rightComponent C A S x y z w ii 1 2 2 2 2 1 := by
  simp only [leftComponent, rightComponent, Fin.sum_univ_three, numerator, Fin.val_zero, Fin.val_one, finThreeTwo, mul_zero, zero_mul, zero_add, add_zero]
  have hp := polynomial_001100 C A S x y z w ii hC hA hS hy hw
  dsimp only [poly_001100_0, complexAdd, complexMul, complexPow] at hp
  linear_combination (-1:ℂ)/1*hp

lemma component_100000 :
    leftComponent C A S x y z w ii 1 0 0 0 0 0 =
    rightComponent C A S x y z w ii 1 0 0 0 0 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 0 0 0 0 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 0 0 0 0 0 (by decide)]

lemma component_100002 :
    leftComponent C A S x y z w ii 1 0 0 0 0 2 =
    rightComponent C A S x y z w ii 1 0 0 0 0 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 0 0 0 0 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 0 0 0 0 2 (by decide)]

lemma component_100010 :
    leftComponent C A S x y z w ii 1 0 0 0 1 0 =
    rightComponent C A S x y z w ii 1 0 0 0 1 0 := by
  simp only [leftComponent, rightComponent, Fin.sum_univ_three, numerator, Fin.val_zero, Fin.val_one, finThreeTwo, mul_zero, zero_mul, zero_add, add_zero]
  ; ring

lemma component_100011 :
    leftComponent C A S x y z w ii 1 0 0 0 1 1 =
    rightComponent C A S x y z w ii 1 0 0 0 1 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 0 0 0 1 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 0 0 0 1 1 (by decide)]

lemma component_100012 :
    leftComponent C A S x y z w ii 1 0 0 0 1 2 =
    rightComponent C A S x y z w ii 1 0 0 0 1 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 0 0 0 1 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 0 0 0 1 2 (by decide)]

lemma component_100020 :
    leftComponent C A S x y z w ii 1 0 0 0 2 0 =
    rightComponent C A S x y z w ii 1 0 0 0 2 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 0 0 0 2 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 0 0 0 2 0 (by decide)]

lemma component_100021 :
    leftComponent C A S x y z w ii 1 0 0 0 2 1 =
    rightComponent C A S x y z w ii 1 0 0 0 2 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 0 0 0 2 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 0 0 0 2 1 (by decide)]

lemma component_100022 :
    leftComponent C A S x y z w ii 1 0 0 0 2 2 =
    rightComponent C A S x y z w ii 1 0 0 0 2 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 0 0 0 2 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 0 0 0 2 2 (by decide)]

lemma component_100100 :
    leftComponent C A S x y z w ii 1 0 0 1 0 0 =
    rightComponent C A S x y z w ii 1 0 0 1 0 0 := by
  simp only [leftComponent, rightComponent, Fin.sum_univ_three, numerator, Fin.val_zero, Fin.val_one, finThreeTwo, mul_zero, zero_mul, zero_add, add_zero]
  ; ring

lemma component_100101 :
    leftComponent C A S x y z w ii 1 0 0 1 0 1 =
    rightComponent C A S x y z w ii 1 0 0 1 0 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 0 0 1 0 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 0 0 1 0 1 (by decide)]

lemma component_100102 :
    leftComponent C A S x y z w ii 1 0 0 1 0 2 =
    rightComponent C A S x y z w ii 1 0 0 1 0 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 0 0 1 0 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 0 0 1 0 2 (by decide)]

lemma component_100110 :
    leftComponent C A S x y z w ii 1 0 0 1 1 0 =
    rightComponent C A S x y z w ii 1 0 0 1 1 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 0 0 1 1 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 0 0 1 1 0 (by decide)]

lemma component_100111 :
    leftComponent C A S x y z w ii 1 0 0 1 1 1 =
    rightComponent C A S x y z w ii 1 0 0 1 1 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 0 0 1 1 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 0 0 1 1 1 (by decide)]

lemma component_100112 :
    leftComponent C A S x y z w ii 1 0 0 1 1 2 =
    rightComponent C A S x y z w ii 1 0 0 1 1 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 0 0 1 1 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 0 0 1 1 2 (by decide)]

lemma component_100120 :
    leftComponent C A S x y z w ii 1 0 0 1 2 0 =
    rightComponent C A S x y z w ii 1 0 0 1 2 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 0 0 1 2 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 0 0 1 2 0 (by decide)]

lemma component_100121 :
    leftComponent C A S x y z w ii 1 0 0 1 2 1 =
    rightComponent C A S x y z w ii 1 0 0 1 2 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 0 0 1 2 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 0 0 1 2 1 (by decide)]

lemma component_100122 :
    leftComponent C A S x y z w ii 1 0 0 1 2 2 =
    rightComponent C A S x y z w ii 1 0 0 1 2 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 0 0 1 2 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 0 0 1 2 2 (by decide)]

lemma component_100200 :
    leftComponent C A S x y z w ii 1 0 0 2 0 0 =
    rightComponent C A S x y z w ii 1 0 0 2 0 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 0 0 2 0 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 0 0 2 0 0 (by decide)]

lemma component_100201 :
    leftComponent C A S x y z w ii 1 0 0 2 0 1 =
    rightComponent C A S x y z w ii 1 0 0 2 0 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 0 0 2 0 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 0 0 2 0 1 (by decide)]

lemma component_100202 :
    leftComponent C A S x y z w ii 1 0 0 2 0 2 =
    rightComponent C A S x y z w ii 1 0 0 2 0 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 0 0 2 0 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 0 0 2 0 2 (by decide)]

lemma component_100210 :
    leftComponent C A S x y z w ii 1 0 0 2 1 0 =
    rightComponent C A S x y z w ii 1 0 0 2 1 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 0 0 2 1 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 0 0 2 1 0 (by decide)]

lemma component_100211 :
    leftComponent C A S x y z w ii 1 0 0 2 1 1 =
    rightComponent C A S x y z w ii 1 0 0 2 1 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 0 0 2 1 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 0 0 2 1 1 (by decide)]

lemma component_100212 :
    leftComponent C A S x y z w ii 1 0 0 2 1 2 =
    rightComponent C A S x y z w ii 1 0 0 2 1 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 0 0 2 1 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 0 0 2 1 2 (by decide)]

lemma component_100220 :
    leftComponent C A S x y z w ii 1 0 0 2 2 0 =
    rightComponent C A S x y z w ii 1 0 0 2 2 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 0 0 2 2 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 0 0 2 2 0 (by decide)]

lemma component_100221 :
    leftComponent C A S x y z w ii 1 0 0 2 2 1 =
    rightComponent C A S x y z w ii 1 0 0 2 2 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 0 0 2 2 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 0 0 2 2 1 (by decide)]

lemma component_100222 :
    leftComponent C A S x y z w ii 1 0 0 2 2 2 =
    rightComponent C A S x y z w ii 1 0 0 2 2 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 0 0 2 2 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 0 0 2 2 2 (by decide)]

lemma component_101000 :
    leftComponent C A S x y z w ii 1 0 1 0 0 0 =
    rightComponent C A S x y z w ii 1 0 1 0 0 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 0 1 0 0 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 0 1 0 0 0 (by decide)]

lemma component_101001 :
    leftComponent C A S x y z w ii 1 0 1 0 0 1 =
    rightComponent C A S x y z w ii 1 0 1 0 0 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 0 1 0 0 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 0 1 0 0 1 (by decide)]

lemma component_101010 :
    leftComponent C A S x y z w ii 1 0 1 0 1 0 =
    rightComponent C A S x y z w ii 1 0 1 0 1 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 0 1 0 1 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 0 1 0 1 0 (by decide)]

lemma component_101012 :
    leftComponent C A S x y z w ii 1 0 1 0 1 2 =
    rightComponent C A S x y z w ii 1 0 1 0 1 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 0 1 0 1 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 0 1 0 1 2 (by decide)]

lemma component_101021 :
    leftComponent C A S x y z w ii 1 0 1 0 2 1 =
    rightComponent C A S x y z w ii 1 0 1 0 2 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 0 1 0 2 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 0 1 0 2 1 (by decide)]

lemma component_101022 :
    leftComponent C A S x y z w ii 1 0 1 0 2 2 =
    rightComponent C A S x y z w ii 1 0 1 0 2 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 0 1 0 2 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 0 1 0 2 2 (by decide)]

lemma component_101100 :
    leftComponent C A S x y z w ii 1 0 1 1 0 0 =
    rightComponent C A S x y z w ii 1 0 1 1 0 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 0 1 1 0 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 0 1 1 0 0 (by decide)]

lemma component_101101 :
    leftComponent C A S x y z w ii 1 0 1 1 0 1 =
    rightComponent C A S x y z w ii 1 0 1 1 0 1 := by
  simp only [leftComponent, rightComponent, Fin.sum_univ_three, numerator, Fin.val_zero, Fin.val_one, finThreeTwo, mul_zero, zero_mul, zero_add, add_zero]
  ; ring

lemma component_101102 :
    leftComponent C A S x y z w ii 1 0 1 1 0 2 =
    rightComponent C A S x y z w ii 1 0 1 1 0 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 0 1 1 0 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 0 1 1 0 2 (by decide)]

lemma component_101111 :
    leftComponent C A S x y z w ii 1 0 1 1 1 1 =
    rightComponent C A S x y z w ii 1 0 1 1 1 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 0 1 1 1 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 0 1 1 1 1 (by decide)]

lemma component_101112 :
    leftComponent C A S x y z w ii 1 0 1 1 1 2 =
    rightComponent C A S x y z w ii 1 0 1 1 1 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 0 1 1 1 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 0 1 1 1 2 (by decide)]

lemma component_101120 :
    leftComponent C A S x y z w ii 1 0 1 1 2 0 =
    rightComponent C A S x y z w ii 1 0 1 1 2 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 0 1 1 2 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 0 1 1 2 0 (by decide)]

lemma component_101121 :
    leftComponent C A S x y z w ii 1 0 1 1 2 1 =
    rightComponent C A S x y z w ii 1 0 1 1 2 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 0 1 1 2 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 0 1 1 2 1 (by decide)]

lemma component_101122 :
    leftComponent C A S x y z w ii 1 0 1 1 2 2 =
    rightComponent C A S x y z w ii 1 0 1 1 2 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 0 1 1 2 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 0 1 1 2 2 (by decide)]

lemma component_101201 :
    leftComponent C A S x y z w ii 1 0 1 2 0 1 =
    rightComponent C A S x y z w ii 1 0 1 2 0 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 0 1 2 0 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 0 1 2 0 1 (by decide)]

lemma component_101202 :
    leftComponent C A S x y z w ii 1 0 1 2 0 2 =
    rightComponent C A S x y z w ii 1 0 1 2 0 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 0 1 2 0 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 0 1 2 0 2 (by decide)]

lemma component_101210 :
    leftComponent C A S x y z w ii 1 0 1 2 1 0 =
    rightComponent C A S x y z w ii 1 0 1 2 1 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 0 1 2 1 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 0 1 2 1 0 (by decide)]

lemma component_101211 :
    leftComponent C A S x y z w ii 1 0 1 2 1 1 =
    rightComponent C A S x y z w ii 1 0 1 2 1 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 0 1 2 1 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 0 1 2 1 1 (by decide)]

lemma component_101212 :
    leftComponent C A S x y z w ii 1 0 1 2 1 2 =
    rightComponent C A S x y z w ii 1 0 1 2 1 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 0 1 2 1 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 0 1 2 1 2 (by decide)]

lemma component_101220 :
    leftComponent C A S x y z w ii 1 0 1 2 2 0 =
    rightComponent C A S x y z w ii 1 0 1 2 2 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 0 1 2 2 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 0 1 2 2 0 (by decide)]

lemma component_101221 :
    leftComponent C A S x y z w ii 1 0 1 2 2 1 =
    rightComponent C A S x y z w ii 1 0 1 2 2 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 0 1 2 2 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 0 1 2 2 1 (by decide)]

lemma component_101222 :
    leftComponent C A S x y z w ii 1 0 1 2 2 2 =
    rightComponent C A S x y z w ii 1 0 1 2 2 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 0 1 2 2 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 0 1 2 2 2 (by decide)]

lemma component_102000 :
    leftComponent C A S x y z w ii 1 0 2 0 0 0 =
    rightComponent C A S x y z w ii 1 0 2 0 0 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 0 2 0 0 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 0 2 0 0 0 (by decide)]

lemma component_102001 :
    leftComponent C A S x y z w ii 1 0 2 0 0 1 =
    rightComponent C A S x y z w ii 1 0 2 0 0 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 0 2 0 0 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 0 2 0 0 1 (by decide)]

lemma component_102002 :
    leftComponent C A S x y z w ii 1 0 2 0 0 2 =
    rightComponent C A S x y z w ii 1 0 2 0 0 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 0 2 0 0 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 0 2 0 0 2 (by decide)]

lemma component_102010 :
    leftComponent C A S x y z w ii 1 0 2 0 1 0 =
    rightComponent C A S x y z w ii 1 0 2 0 1 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 0 2 0 1 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 0 2 0 1 0 (by decide)]

lemma component_102011 :
    leftComponent C A S x y z w ii 1 0 2 0 1 1 =
    rightComponent C A S x y z w ii 1 0 2 0 1 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 0 2 0 1 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 0 2 0 1 1 (by decide)]

lemma component_102020 :
    leftComponent C A S x y z w ii 1 0 2 0 2 0 =
    rightComponent C A S x y z w ii 1 0 2 0 2 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 0 2 0 2 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 0 2 0 2 0 (by decide)]

lemma component_102022 :
    leftComponent C A S x y z w ii 1 0 2 0 2 2 =
    rightComponent C A S x y z w ii 1 0 2 0 2 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 0 2 0 2 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 0 2 0 2 2 (by decide)]

lemma component_102100 :
    leftComponent C A S x y z w ii 1 0 2 1 0 0 =
    rightComponent C A S x y z w ii 1 0 2 1 0 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 0 2 1 0 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 0 2 1 0 0 (by decide)]

lemma component_102101 :
    leftComponent C A S x y z w ii 1 0 2 1 0 1 =
    rightComponent C A S x y z w ii 1 0 2 1 0 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 0 2 1 0 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 0 2 1 0 1 (by decide)]

lemma component_102102 :
    leftComponent C A S x y z w ii 1 0 2 1 0 2 =
    rightComponent C A S x y z w ii 1 0 2 1 0 2 := by
  simp only [leftComponent, rightComponent, Fin.sum_univ_three, numerator, Fin.val_zero, Fin.val_one, finThreeTwo, mul_zero, zero_mul, zero_add, add_zero]
  ; ring

lemma component_102110 :
    leftComponent C A S x y z w ii 1 0 2 1 1 0 =
    rightComponent C A S x y z w ii 1 0 2 1 1 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 0 2 1 1 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 0 2 1 1 0 (by decide)]

lemma component_102112 :
    leftComponent C A S x y z w ii 1 0 2 1 1 2 =
    rightComponent C A S x y z w ii 1 0 2 1 1 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 0 2 1 1 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 0 2 1 1 2 (by decide)]

lemma component_102120 :
    leftComponent C A S x y z w ii 1 0 2 1 2 0 =
    rightComponent C A S x y z w ii 1 0 2 1 2 0 := by
  simp only [leftComponent, rightComponent, Fin.sum_univ_three, numerator, Fin.val_zero, Fin.val_one, finThreeTwo, mul_zero, zero_mul, zero_add, add_zero]
  ; ring

lemma component_102121 :
    leftComponent C A S x y z w ii 1 0 2 1 2 1 =
    rightComponent C A S x y z w ii 1 0 2 1 2 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 0 2 1 2 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 0 2 1 2 1 (by decide)]

lemma component_102122 :
    leftComponent C A S x y z w ii 1 0 2 1 2 2 =
    rightComponent C A S x y z w ii 1 0 2 1 2 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 0 2 1 2 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 0 2 1 2 2 (by decide)]

lemma component_102200 :
    leftComponent C A S x y z w ii 1 0 2 2 0 0 =
    rightComponent C A S x y z w ii 1 0 2 2 0 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 0 2 2 0 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 0 2 2 0 0 (by decide)]

lemma component_102202 :
    leftComponent C A S x y z w ii 1 0 2 2 0 2 =
    rightComponent C A S x y z w ii 1 0 2 2 0 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 0 2 2 0 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 0 2 2 0 2 (by decide)]

lemma component_102211 :
    leftComponent C A S x y z w ii 1 0 2 2 1 1 =
    rightComponent C A S x y z w ii 1 0 2 2 1 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 0 2 2 1 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 0 2 2 1 1 (by decide)]

lemma component_102212 :
    leftComponent C A S x y z w ii 1 0 2 2 1 2 =
    rightComponent C A S x y z w ii 1 0 2 2 1 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 0 2 2 1 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 0 2 2 1 2 (by decide)]

lemma component_102220 :
    leftComponent C A S x y z w ii 1 0 2 2 2 0 =
    rightComponent C A S x y z w ii 1 0 2 2 2 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 0 2 2 2 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 0 2 2 2 0 (by decide)]

lemma component_102221 :
    leftComponent C A S x y z w ii 1 0 2 2 2 1 =
    rightComponent C A S x y z w ii 1 0 2 2 2 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 0 2 2 2 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 0 2 2 2 1 (by decide)]

lemma component_102222 :
    leftComponent C A S x y z w ii 1 0 2 2 2 2 =
    rightComponent C A S x y z w ii 1 0 2 2 2 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 0 2 2 2 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 0 2 2 2 2 (by decide)]

lemma component_110000 :
    leftComponent C A S x y z w ii 1 1 0 0 0 0 =
    rightComponent C A S x y z w ii 1 1 0 0 0 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 1 0 0 0 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 1 0 0 0 0 (by decide)]

lemma component_110001 :
    leftComponent C A S x y z w ii 1 1 0 0 0 1 =
    rightComponent C A S x y z w ii 1 1 0 0 0 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 1 0 0 0 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 1 0 0 0 1 (by decide)]

lemma component_110010 :
    leftComponent C A S x y z w ii 1 1 0 0 1 0 =
    rightComponent C A S x y z w ii 1 1 0 0 1 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 1 0 0 1 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 1 0 0 1 0 (by decide)]

lemma component_110012 :
    leftComponent C A S x y z w ii 1 1 0 0 1 2 =
    rightComponent C A S x y z w ii 1 1 0 0 1 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 1 0 0 1 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 1 0 0 1 2 (by decide)]

lemma component_110021 :
    leftComponent C A S x y z w ii 1 1 0 0 2 1 =
    rightComponent C A S x y z w ii 1 1 0 0 2 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 1 0 0 2 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 1 0 0 2 1 (by decide)]

lemma component_110022 :
    leftComponent C A S x y z w ii 1 1 0 0 2 2 =
    rightComponent C A S x y z w ii 1 1 0 0 2 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 1 0 0 2 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 1 0 0 2 2 (by decide)]

lemma component_110100 :
    leftComponent C A S x y z w ii 1 1 0 1 0 0 =
    rightComponent C A S x y z w ii 1 1 0 1 0 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 1 0 1 0 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 1 0 1 0 0 (by decide)]

lemma component_110102 :
    leftComponent C A S x y z w ii 1 1 0 1 0 2 =
    rightComponent C A S x y z w ii 1 1 0 1 0 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 1 0 1 0 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 1 0 1 0 2 (by decide)]

lemma component_110110 :
    leftComponent C A S x y z w ii 1 1 0 1 1 0 =
    rightComponent C A S x y z w ii 1 1 0 1 1 0 := by
  simp only [leftComponent, rightComponent, Fin.sum_univ_three, numerator, Fin.val_zero, Fin.val_one, finThreeTwo, mul_zero, zero_mul, zero_add, add_zero]
  ; ring

lemma component_110111 :
    leftComponent C A S x y z w ii 1 1 0 1 1 1 =
    rightComponent C A S x y z w ii 1 1 0 1 1 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 1 0 1 1 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 1 0 1 1 1 (by decide)]

lemma component_110112 :
    leftComponent C A S x y z w ii 1 1 0 1 1 2 =
    rightComponent C A S x y z w ii 1 1 0 1 1 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 1 0 1 1 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 1 0 1 1 2 (by decide)]

lemma component_110120 :
    leftComponent C A S x y z w ii 1 1 0 1 2 0 =
    rightComponent C A S x y z w ii 1 1 0 1 2 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 1 0 1 2 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 1 0 1 2 0 (by decide)]

lemma component_110121 :
    leftComponent C A S x y z w ii 1 1 0 1 2 1 =
    rightComponent C A S x y z w ii 1 1 0 1 2 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 1 0 1 2 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 1 0 1 2 1 (by decide)]

lemma component_110122 :
    leftComponent C A S x y z w ii 1 1 0 1 2 2 =
    rightComponent C A S x y z w ii 1 1 0 1 2 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 1 0 1 2 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 1 0 1 2 2 (by decide)]

lemma component_110201 :
    leftComponent C A S x y z w ii 1 1 0 2 0 1 =
    rightComponent C A S x y z w ii 1 1 0 2 0 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 1 0 2 0 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 1 0 2 0 1 (by decide)]

lemma component_110202 :
    leftComponent C A S x y z w ii 1 1 0 2 0 2 =
    rightComponent C A S x y z w ii 1 1 0 2 0 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 1 0 2 0 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 1 0 2 0 2 (by decide)]

lemma component_110210 :
    leftComponent C A S x y z w ii 1 1 0 2 1 0 =
    rightComponent C A S x y z w ii 1 1 0 2 1 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 1 0 2 1 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 1 0 2 1 0 (by decide)]

lemma component_110211 :
    leftComponent C A S x y z w ii 1 1 0 2 1 1 =
    rightComponent C A S x y z w ii 1 1 0 2 1 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 1 0 2 1 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 1 0 2 1 1 (by decide)]

lemma component_110212 :
    leftComponent C A S x y z w ii 1 1 0 2 1 2 =
    rightComponent C A S x y z w ii 1 1 0 2 1 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 1 0 2 1 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 1 0 2 1 2 (by decide)]

lemma component_110220 :
    leftComponent C A S x y z w ii 1 1 0 2 2 0 =
    rightComponent C A S x y z w ii 1 1 0 2 2 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 1 0 2 2 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 1 0 2 2 0 (by decide)]

lemma component_110221 :
    leftComponent C A S x y z w ii 1 1 0 2 2 1 =
    rightComponent C A S x y z w ii 1 1 0 2 2 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 1 0 2 2 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 1 0 2 2 1 (by decide)]

lemma component_110222 :
    leftComponent C A S x y z w ii 1 1 0 2 2 2 =
    rightComponent C A S x y z w ii 1 1 0 2 2 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 1 0 2 2 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 1 0 2 2 2 (by decide)]

lemma component_111000 :
    leftComponent C A S x y z w ii 1 1 1 0 0 0 =
    rightComponent C A S x y z w ii 1 1 1 0 0 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 1 1 0 0 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 1 1 0 0 0 (by decide)]

lemma component_111001 :
    leftComponent C A S x y z w ii 1 1 1 0 0 1 =
    rightComponent C A S x y z w ii 1 1 1 0 0 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 1 1 0 0 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 1 1 0 0 1 (by decide)]

lemma component_111002 :
    leftComponent C A S x y z w ii 1 1 1 0 0 2 =
    rightComponent C A S x y z w ii 1 1 1 0 0 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 1 1 0 0 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 1 1 0 0 2 (by decide)]

lemma component_111010 :
    leftComponent C A S x y z w ii 1 1 1 0 1 0 =
    rightComponent C A S x y z w ii 1 1 1 0 1 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 1 1 0 1 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 1 1 0 1 0 (by decide)]

lemma component_111011 :
    leftComponent C A S x y z w ii 1 1 1 0 1 1 =
    rightComponent C A S x y z w ii 1 1 1 0 1 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 1 1 0 1 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 1 1 0 1 1 (by decide)]

lemma component_111020 :
    leftComponent C A S x y z w ii 1 1 1 0 2 0 =
    rightComponent C A S x y z w ii 1 1 1 0 2 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 1 1 0 2 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 1 1 0 2 0 (by decide)]

lemma component_111022 :
    leftComponent C A S x y z w ii 1 1 1 0 2 2 =
    rightComponent C A S x y z w ii 1 1 1 0 2 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 1 1 0 2 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 1 1 0 2 2 (by decide)]

lemma component_111100 :
    leftComponent C A S x y z w ii 1 1 1 1 0 0 =
    rightComponent C A S x y z w ii 1 1 1 1 0 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 1 1 1 0 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 1 1 1 0 0 (by decide)]

lemma component_111101 :
    leftComponent C A S x y z w ii 1 1 1 1 0 1 =
    rightComponent C A S x y z w ii 1 1 1 1 0 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 1 1 1 0 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 1 1 1 0 1 (by decide)]

lemma component_111110 :
    leftComponent C A S x y z w ii 1 1 1 1 1 0 =
    rightComponent C A S x y z w ii 1 1 1 1 1 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 1 1 1 1 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 1 1 1 1 0 (by decide)]

lemma component_111111 :
    leftComponent C A S x y z w ii 1 1 1 1 1 1 =
    rightComponent C A S x y z w ii 1 1 1 1 1 1 := by
  simp only [leftComponent, rightComponent, Fin.sum_univ_three, numerator, Fin.val_zero, Fin.val_one, finThreeTwo, mul_zero, zero_mul, zero_add, add_zero]
  ; ring

lemma component_111112 :
    leftComponent C A S x y z w ii 1 1 1 1 1 2 =
    rightComponent C A S x y z w ii 1 1 1 1 1 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 1 1 1 1 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 1 1 1 1 2 (by decide)]

lemma component_111121 :
    leftComponent C A S x y z w ii 1 1 1 1 2 1 =
    rightComponent C A S x y z w ii 1 1 1 1 2 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 1 1 1 2 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 1 1 1 2 1 (by decide)]

lemma component_111122 :
    leftComponent C A S x y z w ii 1 1 1 1 2 2 =
    rightComponent C A S x y z w ii 1 1 1 1 2 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 1 1 1 2 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 1 1 1 2 2 (by decide)]

lemma component_111200 :
    leftComponent C A S x y z w ii 1 1 1 2 0 0 =
    rightComponent C A S x y z w ii 1 1 1 2 0 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 1 1 2 0 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 1 1 2 0 0 (by decide)]

lemma component_111202 :
    leftComponent C A S x y z w ii 1 1 1 2 0 2 =
    rightComponent C A S x y z w ii 1 1 1 2 0 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 1 1 2 0 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 1 1 2 0 2 (by decide)]

lemma component_111211 :
    leftComponent C A S x y z w ii 1 1 1 2 1 1 =
    rightComponent C A S x y z w ii 1 1 1 2 1 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 1 1 2 1 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 1 1 2 1 1 (by decide)]

lemma component_111212 :
    leftComponent C A S x y z w ii 1 1 1 2 1 2 =
    rightComponent C A S x y z w ii 1 1 1 2 1 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 1 1 2 1 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 1 1 2 1 2 (by decide)]

lemma component_111220 :
    leftComponent C A S x y z w ii 1 1 1 2 2 0 =
    rightComponent C A S x y z w ii 1 1 1 2 2 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 1 1 2 2 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 1 1 2 2 0 (by decide)]

lemma component_111221 :
    leftComponent C A S x y z w ii 1 1 1 2 2 1 =
    rightComponent C A S x y z w ii 1 1 1 2 2 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 1 1 2 2 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 1 1 2 2 1 (by decide)]

lemma component_111222 :
    leftComponent C A S x y z w ii 1 1 1 2 2 2 =
    rightComponent C A S x y z w ii 1 1 1 2 2 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 1 1 2 2 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 1 1 2 2 2 (by decide)]

lemma component_112000 :
    leftComponent C A S x y z w ii 1 1 2 0 0 0 =
    rightComponent C A S x y z w ii 1 1 2 0 0 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 1 2 0 0 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 1 2 0 0 0 (by decide)]

lemma component_112001 :
    leftComponent C A S x y z w ii 1 1 2 0 0 1 =
    rightComponent C A S x y z w ii 1 1 2 0 0 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 1 2 0 0 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 1 2 0 0 1 (by decide)]

lemma component_112002 :
    leftComponent C A S x y z w ii 1 1 2 0 0 2 =
    rightComponent C A S x y z w ii 1 1 2 0 0 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 1 2 0 0 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 1 2 0 0 2 (by decide)]

lemma component_112010 :
    leftComponent C A S x y z w ii 1 1 2 0 1 0 =
    rightComponent C A S x y z w ii 1 1 2 0 1 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 1 2 0 1 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 1 2 0 1 0 (by decide)]

lemma component_112011 :
    leftComponent C A S x y z w ii 1 1 2 0 1 1 =
    rightComponent C A S x y z w ii 1 1 2 0 1 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 1 2 0 1 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 1 2 0 1 1 (by decide)]

lemma component_112012 :
    leftComponent C A S x y z w ii 1 1 2 0 1 2 =
    rightComponent C A S x y z w ii 1 1 2 0 1 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 1 2 0 1 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 1 2 0 1 2 (by decide)]

lemma component_112020 :
    leftComponent C A S x y z w ii 1 1 2 0 2 0 =
    rightComponent C A S x y z w ii 1 1 2 0 2 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 1 2 0 2 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 1 2 0 2 0 (by decide)]

lemma component_112021 :
    leftComponent C A S x y z w ii 1 1 2 0 2 1 =
    rightComponent C A S x y z w ii 1 1 2 0 2 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 1 2 0 2 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 1 2 0 2 1 (by decide)]

lemma component_112100 :
    leftComponent C A S x y z w ii 1 1 2 1 0 0 =
    rightComponent C A S x y z w ii 1 1 2 1 0 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 1 2 1 0 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 1 2 1 0 0 (by decide)]

lemma component_112101 :
    leftComponent C A S x y z w ii 1 1 2 1 0 1 =
    rightComponent C A S x y z w ii 1 1 2 1 0 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 1 2 1 0 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 1 2 1 0 1 (by decide)]

lemma component_112102 :
    leftComponent C A S x y z w ii 1 1 2 1 0 2 =
    rightComponent C A S x y z w ii 1 1 2 1 0 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 1 2 1 0 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 1 2 1 0 2 (by decide)]

lemma component_112110 :
    leftComponent C A S x y z w ii 1 1 2 1 1 0 =
    rightComponent C A S x y z w ii 1 1 2 1 1 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 1 2 1 1 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 1 2 1 1 0 (by decide)]

lemma component_112111 :
    leftComponent C A S x y z w ii 1 1 2 1 1 1 =
    rightComponent C A S x y z w ii 1 1 2 1 1 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 1 2 1 1 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 1 2 1 1 1 (by decide)]

lemma component_112112 :
    leftComponent C A S x y z w ii 1 1 2 1 1 2 =
    rightComponent C A S x y z w ii 1 1 2 1 1 2 := by
  simp only [leftComponent, rightComponent, Fin.sum_univ_three, numerator, Fin.val_zero, Fin.val_one, finThreeTwo, mul_zero, zero_mul, zero_add, add_zero]
  ; ring

lemma component_112120 :
    leftComponent C A S x y z w ii 1 1 2 1 2 0 =
    rightComponent C A S x y z w ii 1 1 2 1 2 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 1 2 1 2 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 1 2 1 2 0 (by decide)]

lemma component_112122 :
    leftComponent C A S x y z w ii 1 1 2 1 2 2 =
    rightComponent C A S x y z w ii 1 1 2 1 2 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 1 2 1 2 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 1 2 1 2 2 (by decide)]

lemma component_112200 :
    leftComponent C A S x y z w ii 1 1 2 2 0 0 =
    rightComponent C A S x y z w ii 1 1 2 2 0 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 1 2 2 0 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 1 2 2 0 0 (by decide)]

lemma component_112201 :
    leftComponent C A S x y z w ii 1 1 2 2 0 1 =
    rightComponent C A S x y z w ii 1 1 2 2 0 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 1 2 2 0 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 1 2 2 0 1 (by decide)]

lemma component_112210 :
    leftComponent C A S x y z w ii 1 1 2 2 1 0 =
    rightComponent C A S x y z w ii 1 1 2 2 1 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 1 2 2 1 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 1 2 2 1 0 (by decide)]

lemma component_112212 :
    leftComponent C A S x y z w ii 1 1 2 2 1 2 =
    rightComponent C A S x y z w ii 1 1 2 2 1 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 1 2 2 1 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 1 2 2 1 2 (by decide)]

lemma component_112221 :
    leftComponent C A S x y z w ii 1 1 2 2 2 1 =
    rightComponent C A S x y z w ii 1 1 2 2 2 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 1 2 2 2 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 1 2 2 2 1 (by decide)]

lemma component_112222 :
    leftComponent C A S x y z w ii 1 1 2 2 2 2 =
    rightComponent C A S x y z w ii 1 1 2 2 2 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 1 2 2 2 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 1 2 2 2 2 (by decide)]

lemma component_120000 :
    leftComponent C A S x y z w ii 1 2 0 0 0 0 =
    rightComponent C A S x y z w ii 1 2 0 0 0 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 2 0 0 0 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 2 0 0 0 0 (by decide)]

lemma component_120001 :
    leftComponent C A S x y z w ii 1 2 0 0 0 1 =
    rightComponent C A S x y z w ii 1 2 0 0 0 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 2 0 0 0 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 2 0 0 0 1 (by decide)]

lemma component_120002 :
    leftComponent C A S x y z w ii 1 2 0 0 0 2 =
    rightComponent C A S x y z w ii 1 2 0 0 0 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 2 0 0 0 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 2 0 0 0 2 (by decide)]

lemma component_120010 :
    leftComponent C A S x y z w ii 1 2 0 0 1 0 =
    rightComponent C A S x y z w ii 1 2 0 0 1 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 2 0 0 1 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 2 0 0 1 0 (by decide)]

lemma component_120011 :
    leftComponent C A S x y z w ii 1 2 0 0 1 1 =
    rightComponent C A S x y z w ii 1 2 0 0 1 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 2 0 0 1 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 2 0 0 1 1 (by decide)]

lemma component_120020 :
    leftComponent C A S x y z w ii 1 2 0 0 2 0 =
    rightComponent C A S x y z w ii 1 2 0 0 2 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 2 0 0 2 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 2 0 0 2 0 (by decide)]

lemma component_120022 :
    leftComponent C A S x y z w ii 1 2 0 0 2 2 =
    rightComponent C A S x y z w ii 1 2 0 0 2 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 2 0 0 2 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 2 0 0 2 2 (by decide)]

lemma component_120100 :
    leftComponent C A S x y z w ii 1 2 0 1 0 0 =
    rightComponent C A S x y z w ii 1 2 0 1 0 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 2 0 1 0 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 2 0 1 0 0 (by decide)]

lemma component_120101 :
    leftComponent C A S x y z w ii 1 2 0 1 0 1 =
    rightComponent C A S x y z w ii 1 2 0 1 0 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 2 0 1 0 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 2 0 1 0 1 (by decide)]

lemma component_120102 :
    leftComponent C A S x y z w ii 1 2 0 1 0 2 =
    rightComponent C A S x y z w ii 1 2 0 1 0 2 := by
  simp only [leftComponent, rightComponent, Fin.sum_univ_three, numerator, Fin.val_zero, Fin.val_one, finThreeTwo, mul_zero, zero_mul, zero_add, add_zero]
  ; ring

lemma component_120110 :
    leftComponent C A S x y z w ii 1 2 0 1 1 0 =
    rightComponent C A S x y z w ii 1 2 0 1 1 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 2 0 1 1 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 2 0 1 1 0 (by decide)]

lemma component_120112 :
    leftComponent C A S x y z w ii 1 2 0 1 1 2 =
    rightComponent C A S x y z w ii 1 2 0 1 1 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 2 0 1 1 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 2 0 1 1 2 (by decide)]

lemma component_120120 :
    leftComponent C A S x y z w ii 1 2 0 1 2 0 =
    rightComponent C A S x y z w ii 1 2 0 1 2 0 := by
  simp only [leftComponent, rightComponent, Fin.sum_univ_three, numerator, Fin.val_zero, Fin.val_one, finThreeTwo, mul_zero, zero_mul, zero_add, add_zero]
  ; ring

lemma component_120121 :
    leftComponent C A S x y z w ii 1 2 0 1 2 1 =
    rightComponent C A S x y z w ii 1 2 0 1 2 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 2 0 1 2 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 2 0 1 2 1 (by decide)]

lemma component_120122 :
    leftComponent C A S x y z w ii 1 2 0 1 2 2 =
    rightComponent C A S x y z w ii 1 2 0 1 2 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 2 0 1 2 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 2 0 1 2 2 (by decide)]

lemma component_120200 :
    leftComponent C A S x y z w ii 1 2 0 2 0 0 =
    rightComponent C A S x y z w ii 1 2 0 2 0 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 2 0 2 0 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 2 0 2 0 0 (by decide)]

lemma component_120202 :
    leftComponent C A S x y z w ii 1 2 0 2 0 2 =
    rightComponent C A S x y z w ii 1 2 0 2 0 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 2 0 2 0 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 2 0 2 0 2 (by decide)]

lemma component_120211 :
    leftComponent C A S x y z w ii 1 2 0 2 1 1 =
    rightComponent C A S x y z w ii 1 2 0 2 1 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 2 0 2 1 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 2 0 2 1 1 (by decide)]

lemma component_120212 :
    leftComponent C A S x y z w ii 1 2 0 2 1 2 =
    rightComponent C A S x y z w ii 1 2 0 2 1 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 2 0 2 1 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 2 0 2 1 2 (by decide)]

lemma component_120220 :
    leftComponent C A S x y z w ii 1 2 0 2 2 0 =
    rightComponent C A S x y z w ii 1 2 0 2 2 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 2 0 2 2 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 2 0 2 2 0 (by decide)]

lemma component_120221 :
    leftComponent C A S x y z w ii 1 2 0 2 2 1 =
    rightComponent C A S x y z w ii 1 2 0 2 2 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 2 0 2 2 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 2 0 2 2 1 (by decide)]

lemma component_120222 :
    leftComponent C A S x y z w ii 1 2 0 2 2 2 =
    rightComponent C A S x y z w ii 1 2 0 2 2 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 2 0 2 2 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 2 0 2 2 2 (by decide)]

lemma component_121000 :
    leftComponent C A S x y z w ii 1 2 1 0 0 0 =
    rightComponent C A S x y z w ii 1 2 1 0 0 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 2 1 0 0 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 2 1 0 0 0 (by decide)]

lemma component_121001 :
    leftComponent C A S x y z w ii 1 2 1 0 0 1 =
    rightComponent C A S x y z w ii 1 2 1 0 0 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 2 1 0 0 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 2 1 0 0 1 (by decide)]

lemma component_121002 :
    leftComponent C A S x y z w ii 1 2 1 0 0 2 =
    rightComponent C A S x y z w ii 1 2 1 0 0 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 2 1 0 0 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 2 1 0 0 2 (by decide)]

lemma component_121010 :
    leftComponent C A S x y z w ii 1 2 1 0 1 0 =
    rightComponent C A S x y z w ii 1 2 1 0 1 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 2 1 0 1 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 2 1 0 1 0 (by decide)]

lemma component_121011 :
    leftComponent C A S x y z w ii 1 2 1 0 1 1 =
    rightComponent C A S x y z w ii 1 2 1 0 1 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 2 1 0 1 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 2 1 0 1 1 (by decide)]

lemma component_121012 :
    leftComponent C A S x y z w ii 1 2 1 0 1 2 =
    rightComponent C A S x y z w ii 1 2 1 0 1 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 2 1 0 1 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 2 1 0 1 2 (by decide)]

lemma component_121020 :
    leftComponent C A S x y z w ii 1 2 1 0 2 0 =
    rightComponent C A S x y z w ii 1 2 1 0 2 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 2 1 0 2 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 2 1 0 2 0 (by decide)]

lemma component_121021 :
    leftComponent C A S x y z w ii 1 2 1 0 2 1 =
    rightComponent C A S x y z w ii 1 2 1 0 2 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 2 1 0 2 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 2 1 0 2 1 (by decide)]

lemma component_121100 :
    leftComponent C A S x y z w ii 1 2 1 1 0 0 =
    rightComponent C A S x y z w ii 1 2 1 1 0 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 2 1 1 0 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 2 1 1 0 0 (by decide)]

lemma component_121101 :
    leftComponent C A S x y z w ii 1 2 1 1 0 1 =
    rightComponent C A S x y z w ii 1 2 1 1 0 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 2 1 1 0 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 2 1 1 0 1 (by decide)]

lemma component_121102 :
    leftComponent C A S x y z w ii 1 2 1 1 0 2 =
    rightComponent C A S x y z w ii 1 2 1 1 0 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 2 1 1 0 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 2 1 1 0 2 (by decide)]

lemma component_121110 :
    leftComponent C A S x y z w ii 1 2 1 1 1 0 =
    rightComponent C A S x y z w ii 1 2 1 1 1 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 2 1 1 1 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 2 1 1 1 0 (by decide)]

lemma component_121111 :
    leftComponent C A S x y z w ii 1 2 1 1 1 1 =
    rightComponent C A S x y z w ii 1 2 1 1 1 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 2 1 1 1 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 2 1 1 1 1 (by decide)]

lemma component_121120 :
    leftComponent C A S x y z w ii 1 2 1 1 2 0 =
    rightComponent C A S x y z w ii 1 2 1 1 2 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 2 1 1 2 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 2 1 1 2 0 (by decide)]

lemma component_121121 :
    leftComponent C A S x y z w ii 1 2 1 1 2 1 =
    rightComponent C A S x y z w ii 1 2 1 1 2 1 := by
  simp only [leftComponent, rightComponent, Fin.sum_univ_three, numerator, Fin.val_zero, Fin.val_one, finThreeTwo, mul_zero, zero_mul, zero_add, add_zero]
  ; ring

lemma component_121122 :
    leftComponent C A S x y z w ii 1 2 1 1 2 2 =
    rightComponent C A S x y z w ii 1 2 1 1 2 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 2 1 1 2 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 2 1 1 2 2 (by decide)]

lemma component_121200 :
    leftComponent C A S x y z w ii 1 2 1 2 0 0 =
    rightComponent C A S x y z w ii 1 2 1 2 0 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 2 1 2 0 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 2 1 2 0 0 (by decide)]

lemma component_121201 :
    leftComponent C A S x y z w ii 1 2 1 2 0 1 =
    rightComponent C A S x y z w ii 1 2 1 2 0 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 2 1 2 0 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 2 1 2 0 1 (by decide)]

lemma component_121210 :
    leftComponent C A S x y z w ii 1 2 1 2 1 0 =
    rightComponent C A S x y z w ii 1 2 1 2 1 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 2 1 2 1 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 2 1 2 1 0 (by decide)]

lemma component_121212 :
    leftComponent C A S x y z w ii 1 2 1 2 1 2 =
    rightComponent C A S x y z w ii 1 2 1 2 1 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 2 1 2 1 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 2 1 2 1 2 (by decide)]

lemma component_121221 :
    leftComponent C A S x y z w ii 1 2 1 2 2 1 =
    rightComponent C A S x y z w ii 1 2 1 2 2 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 2 1 2 2 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 2 1 2 2 1 (by decide)]

lemma component_121222 :
    leftComponent C A S x y z w ii 1 2 1 2 2 2 =
    rightComponent C A S x y z w ii 1 2 1 2 2 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 2 1 2 2 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 2 1 2 2 2 (by decide)]

lemma component_122000 :
    leftComponent C A S x y z w ii 1 2 2 0 0 0 =
    rightComponent C A S x y z w ii 1 2 2 0 0 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 2 2 0 0 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 2 2 0 0 0 (by decide)]

lemma component_122001 :
    leftComponent C A S x y z w ii 1 2 2 0 0 1 =
    rightComponent C A S x y z w ii 1 2 2 0 0 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 2 2 0 0 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 2 2 0 0 1 (by decide)]

lemma component_122002 :
    leftComponent C A S x y z w ii 1 2 2 0 0 2 =
    rightComponent C A S x y z w ii 1 2 2 0 0 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 2 2 0 0 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 2 2 0 0 2 (by decide)]

lemma component_122010 :
    leftComponent C A S x y z w ii 1 2 2 0 1 0 =
    rightComponent C A S x y z w ii 1 2 2 0 1 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 2 2 0 1 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 2 2 0 1 0 (by decide)]

lemma component_122011 :
    leftComponent C A S x y z w ii 1 2 2 0 1 1 =
    rightComponent C A S x y z w ii 1 2 2 0 1 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 2 2 0 1 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 2 2 0 1 1 (by decide)]

lemma component_122012 :
    leftComponent C A S x y z w ii 1 2 2 0 1 2 =
    rightComponent C A S x y z w ii 1 2 2 0 1 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 2 2 0 1 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 2 2 0 1 2 (by decide)]

lemma component_122020 :
    leftComponent C A S x y z w ii 1 2 2 0 2 0 =
    rightComponent C A S x y z w ii 1 2 2 0 2 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 2 2 0 2 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 2 2 0 2 0 (by decide)]

lemma component_122021 :
    leftComponent C A S x y z w ii 1 2 2 0 2 1 =
    rightComponent C A S x y z w ii 1 2 2 0 2 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 2 2 0 2 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 2 2 0 2 1 (by decide)]

lemma component_122022 :
    leftComponent C A S x y z w ii 1 2 2 0 2 2 =
    rightComponent C A S x y z w ii 1 2 2 0 2 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 2 2 0 2 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 2 2 0 2 2 (by decide)]

lemma component_122100 :
    leftComponent C A S x y z w ii 1 2 2 1 0 0 =
    rightComponent C A S x y z w ii 1 2 2 1 0 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 2 2 1 0 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 2 2 1 0 0 (by decide)]

lemma component_122101 :
    leftComponent C A S x y z w ii 1 2 2 1 0 1 =
    rightComponent C A S x y z w ii 1 2 2 1 0 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 2 2 1 0 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 2 2 1 0 1 (by decide)]

lemma component_122102 :
    leftComponent C A S x y z w ii 1 2 2 1 0 2 =
    rightComponent C A S x y z w ii 1 2 2 1 0 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 2 2 1 0 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 2 2 1 0 2 (by decide)]

lemma component_122110 :
    leftComponent C A S x y z w ii 1 2 2 1 1 0 =
    rightComponent C A S x y z w ii 1 2 2 1 1 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 2 2 1 1 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 2 2 1 1 0 (by decide)]

lemma component_122111 :
    leftComponent C A S x y z w ii 1 2 2 1 1 1 =
    rightComponent C A S x y z w ii 1 2 2 1 1 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 2 2 1 1 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 2 2 1 1 1 (by decide)]

lemma component_122112 :
    leftComponent C A S x y z w ii 1 2 2 1 1 2 =
    rightComponent C A S x y z w ii 1 2 2 1 1 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 2 2 1 1 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 2 2 1 1 2 (by decide)]

lemma component_122120 :
    leftComponent C A S x y z w ii 1 2 2 1 2 0 =
    rightComponent C A S x y z w ii 1 2 2 1 2 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 2 2 1 2 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 2 2 1 2 0 (by decide)]

lemma component_122121 :
    leftComponent C A S x y z w ii 1 2 2 1 2 1 =
    rightComponent C A S x y z w ii 1 2 2 1 2 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 2 2 1 2 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 2 2 1 2 1 (by decide)]

lemma component_122122 :
    leftComponent C A S x y z w ii 1 2 2 1 2 2 =
    rightComponent C A S x y z w ii 1 2 2 1 2 2 := by
  simp only [leftComponent, rightComponent, Fin.sum_univ_three, numerator, Fin.val_zero, Fin.val_one, finThreeTwo, mul_zero, zero_mul, zero_add, add_zero]
  ; ring

lemma component_122200 :
    leftComponent C A S x y z w ii 1 2 2 2 0 0 =
    rightComponent C A S x y z w ii 1 2 2 2 0 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 2 2 2 0 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 2 2 2 0 0 (by decide)]

lemma component_122201 :
    leftComponent C A S x y z w ii 1 2 2 2 0 1 =
    rightComponent C A S x y z w ii 1 2 2 2 0 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 2 2 2 0 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 2 2 2 0 1 (by decide)]

lemma component_122202 :
    leftComponent C A S x y z w ii 1 2 2 2 0 2 =
    rightComponent C A S x y z w ii 1 2 2 2 0 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 2 2 2 0 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 2 2 2 0 2 (by decide)]

lemma component_122210 :
    leftComponent C A S x y z w ii 1 2 2 2 1 0 =
    rightComponent C A S x y z w ii 1 2 2 2 1 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 2 2 2 1 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 2 2 2 1 0 (by decide)]

lemma component_122211 :
    leftComponent C A S x y z w ii 1 2 2 2 1 1 =
    rightComponent C A S x y z w ii 1 2 2 2 1 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 2 2 2 1 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 2 2 2 1 1 (by decide)]

lemma component_122212 :
    leftComponent C A S x y z w ii 1 2 2 2 1 2 =
    rightComponent C A S x y z w ii 1 2 2 2 1 2 := by
  simp only [leftComponent, rightComponent, Fin.sum_univ_three, numerator, Fin.val_zero, Fin.val_one, finThreeTwo, mul_zero, zero_mul, zero_add, add_zero]
  ; ring

lemma component_122220 :
    leftComponent C A S x y z w ii 1 2 2 2 2 0 =
    rightComponent C A S x y z w ii 1 2 2 2 2 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 2 2 2 2 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 2 2 2 2 0 (by decide)]

lemma component_122222 :
    leftComponent C A S x y z w ii 1 2 2 2 2 2 =
    rightComponent C A S x y z w ii 1 2 2 2 2 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 1 2 2 2 2 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 1 2 2 2 2 2 (by decide)]

include hC hA hS hy hw in
lemma block_100 (d e f : Fin 3) :
    leftComponent C A S x y z w ii 1 0 0 d e f =
    rightComponent C A S x y z w ii 1 0 0 d e f := by
  fin_cases d <;> fin_cases e <;> fin_cases f
  · exact component_100000 C A S x y z w ii
  · exact component_100001 C A S x y z w ii hC hA hS hy hw
  · exact component_100002 C A S x y z w ii
  · exact component_100010 C A S x y z w ii
  · exact component_100011 C A S x y z w ii
  · exact component_100012 C A S x y z w ii
  · exact component_100020 C A S x y z w ii
  · exact component_100021 C A S x y z w ii
  · exact component_100022 C A S x y z w ii
  · exact component_100100 C A S x y z w ii
  · exact component_100101 C A S x y z w ii
  · exact component_100102 C A S x y z w ii
  · exact component_100110 C A S x y z w ii
  · exact component_100111 C A S x y z w ii
  · exact component_100112 C A S x y z w ii
  · exact component_100120 C A S x y z w ii
  · exact component_100121 C A S x y z w ii
  · exact component_100122 C A S x y z w ii
  · exact component_100200 C A S x y z w ii
  · exact component_100201 C A S x y z w ii
  · exact component_100202 C A S x y z w ii
  · exact component_100210 C A S x y z w ii
  · exact component_100211 C A S x y z w ii
  · exact component_100212 C A S x y z w ii
  · exact component_100220 C A S x y z w ii
  · exact component_100221 C A S x y z w ii
  · exact component_100222 C A S x y z w ii

include hC hA hS hy hw hi in
lemma block_101 (d e f : Fin 3) :
    leftComponent C A S x y z w ii 1 0 1 d e f =
    rightComponent C A S x y z w ii 1 0 1 d e f := by
  fin_cases d <;> fin_cases e <;> fin_cases f
  · exact component_101000 C A S x y z w ii
  · exact component_101001 C A S x y z w ii
  · exact component_101002 C A S x y z w ii hC hA hS hy hw
  · exact component_101010 C A S x y z w ii
  · exact component_101011 C A S x y z w ii hC hA hS hy hw hi
  · exact component_101012 C A S x y z w ii
  · exact component_101020 C A S x y z w ii hC hA hS hy hw hi
  · exact component_101021 C A S x y z w ii
  · exact component_101022 C A S x y z w ii
  · exact component_101100 C A S x y z w ii
  · exact component_101101 C A S x y z w ii
  · exact component_101102 C A S x y z w ii
  · exact component_101110 C A S x y z w ii hC hA hS hy hw hi
  · exact component_101111 C A S x y z w ii
  · exact component_101112 C A S x y z w ii
  · exact component_101120 C A S x y z w ii
  · exact component_101121 C A S x y z w ii
  · exact component_101122 C A S x y z w ii
  · exact component_101200 C A S x y z w ii hC hA hS hy hw
  · exact component_101201 C A S x y z w ii
  · exact component_101202 C A S x y z w ii
  · exact component_101210 C A S x y z w ii
  · exact component_101211 C A S x y z w ii
  · exact component_101212 C A S x y z w ii
  · exact component_101220 C A S x y z w ii
  · exact component_101221 C A S x y z w ii
  · exact component_101222 C A S x y z w ii

include hC hA hS hy hw hi in
lemma block_102 (d e f : Fin 3) :
    leftComponent C A S x y z w ii 1 0 2 d e f =
    rightComponent C A S x y z w ii 1 0 2 d e f := by
  fin_cases d <;> fin_cases e <;> fin_cases f
  · exact component_102000 C A S x y z w ii
  · exact component_102001 C A S x y z w ii
  · exact component_102002 C A S x y z w ii
  · exact component_102010 C A S x y z w ii
  · exact component_102011 C A S x y z w ii
  · exact component_102012 C A S x y z w ii hC hA hS hy hw hi
  · exact component_102020 C A S x y z w ii
  · exact component_102021 C A S x y z w ii hC hA hS hy hw hi
  · exact component_102022 C A S x y z w ii
  · exact component_102100 C A S x y z w ii
  · exact component_102101 C A S x y z w ii
  · exact component_102102 C A S x y z w ii
  · exact component_102110 C A S x y z w ii
  · exact component_102111 C A S x y z w ii hC hA hS hy hw hi
  · exact component_102112 C A S x y z w ii
  · exact component_102120 C A S x y z w ii
  · exact component_102121 C A S x y z w ii
  · exact component_102122 C A S x y z w ii
  · exact component_102200 C A S x y z w ii
  · exact component_102201 C A S x y z w ii hC hA hS hy hw hi
  · exact component_102202 C A S x y z w ii
  · exact component_102210 C A S x y z w ii hC hA hS hy hw hi
  · exact component_102211 C A S x y z w ii
  · exact component_102212 C A S x y z w ii
  · exact component_102220 C A S x y z w ii
  · exact component_102221 C A S x y z w ii
  · exact component_102222 C A S x y z w ii

include hC hA hS hy hw hi in
lemma block_110 (d e f : Fin 3) :
    leftComponent C A S x y z w ii 1 1 0 d e f =
    rightComponent C A S x y z w ii 1 1 0 d e f := by
  fin_cases d <;> fin_cases e <;> fin_cases f
  · exact component_110000 C A S x y z w ii
  · exact component_110001 C A S x y z w ii
  · exact component_110002 C A S x y z w ii hC hA hS hy hw hi
  · exact component_110010 C A S x y z w ii
  · exact component_110011 C A S x y z w ii hC hA hS hy hw hi
  · exact component_110012 C A S x y z w ii
  · exact component_110020 C A S x y z w ii hC hA hS hy hw hi
  · exact component_110021 C A S x y z w ii
  · exact component_110022 C A S x y z w ii
  · exact component_110100 C A S x y z w ii
  · exact component_110101 C A S x y z w ii hC hA hS hy hw hi
  · exact component_110102 C A S x y z w ii
  · exact component_110110 C A S x y z w ii
  · exact component_110111 C A S x y z w ii
  · exact component_110112 C A S x y z w ii
  · exact component_110120 C A S x y z w ii
  · exact component_110121 C A S x y z w ii
  · exact component_110122 C A S x y z w ii
  · exact component_110200 C A S x y z w ii hC hA hS hy hw
  · exact component_110201 C A S x y z w ii
  · exact component_110202 C A S x y z w ii
  · exact component_110210 C A S x y z w ii
  · exact component_110211 C A S x y z w ii
  · exact component_110212 C A S x y z w ii
  · exact component_110220 C A S x y z w ii
  · exact component_110221 C A S x y z w ii
  · exact component_110222 C A S x y z w ii

include hC hA hS hy hw hi in
lemma block_111 (d e f : Fin 3) :
    leftComponent C A S x y z w ii 1 1 1 d e f =
    rightComponent C A S x y z w ii 1 1 1 d e f := by
  fin_cases d <;> fin_cases e <;> fin_cases f
  · exact component_111000 C A S x y z w ii
  · exact component_111001 C A S x y z w ii
  · exact component_111002 C A S x y z w ii
  · exact component_111010 C A S x y z w ii
  · exact component_111011 C A S x y z w ii
  · exact component_111012 C A S x y z w ii hC hA hS hy hw
  · exact component_111020 C A S x y z w ii
  · exact component_111021 C A S x y z w ii hC hA hS hy hw hi
  · exact component_111022 C A S x y z w ii
  · exact component_111100 C A S x y z w ii
  · exact component_111101 C A S x y z w ii
  · exact component_111102 C A S x y z w ii hC hA hS hy hw hi
  · exact component_111110 C A S x y z w ii
  · exact component_111111 C A S x y z w ii
  · exact component_111112 C A S x y z w ii
  · exact component_111120 C A S x y z w ii hC hA hS hy hw hi
  · exact component_111121 C A S x y z w ii
  · exact component_111122 C A S x y z w ii
  · exact component_111200 C A S x y z w ii
  · exact component_111201 C A S x y z w ii hC hA hS hy hw hi
  · exact component_111202 C A S x y z w ii
  · exact component_111210 C A S x y z w ii hC hA hS hy hw
  · exact component_111211 C A S x y z w ii
  · exact component_111212 C A S x y z w ii
  · exact component_111220 C A S x y z w ii
  · exact component_111221 C A S x y z w ii
  · exact component_111222 C A S x y z w ii

include hC hA hS hy hw hi in
lemma block_112 (d e f : Fin 3) :
    leftComponent C A S x y z w ii 1 1 2 d e f =
    rightComponent C A S x y z w ii 1 1 2 d e f := by
  fin_cases d <;> fin_cases e <;> fin_cases f
  · exact component_112000 C A S x y z w ii
  · exact component_112001 C A S x y z w ii
  · exact component_112002 C A S x y z w ii
  · exact component_112010 C A S x y z w ii
  · exact component_112011 C A S x y z w ii
  · exact component_112012 C A S x y z w ii
  · exact component_112020 C A S x y z w ii
  · exact component_112021 C A S x y z w ii
  · exact component_112022 C A S x y z w ii hC hA hS hy hw
  · exact component_112100 C A S x y z w ii
  · exact component_112101 C A S x y z w ii
  · exact component_112102 C A S x y z w ii
  · exact component_112110 C A S x y z w ii
  · exact component_112111 C A S x y z w ii
  · exact component_112112 C A S x y z w ii
  · exact component_112120 C A S x y z w ii
  · exact component_112121 C A S x y z w ii hC hA hS hy hw hi
  · exact component_112122 C A S x y z w ii
  · exact component_112200 C A S x y z w ii
  · exact component_112201 C A S x y z w ii
  · exact component_112202 C A S x y z w ii hC hA hS hy hw hi
  · exact component_112210 C A S x y z w ii
  · exact component_112211 C A S x y z w ii hC hA hS hy hw hi
  · exact component_112212 C A S x y z w ii
  · exact component_112220 C A S x y z w ii hC hA hS hy hw hi
  · exact component_112221 C A S x y z w ii
  · exact component_112222 C A S x y z w ii

include hC hA hS hy hw hi in
lemma block_120 (d e f : Fin 3) :
    leftComponent C A S x y z w ii 1 2 0 d e f =
    rightComponent C A S x y z w ii 1 2 0 d e f := by
  fin_cases d <;> fin_cases e <;> fin_cases f
  · exact component_120000 C A S x y z w ii
  · exact component_120001 C A S x y z w ii
  · exact component_120002 C A S x y z w ii
  · exact component_120010 C A S x y z w ii
  · exact component_120011 C A S x y z w ii
  · exact component_120012 C A S x y z w ii hC hA hS hy hw hi
  · exact component_120020 C A S x y z w ii
  · exact component_120021 C A S x y z w ii hC hA hS hy hw hi
  · exact component_120022 C A S x y z w ii
  · exact component_120100 C A S x y z w ii
  · exact component_120101 C A S x y z w ii
  · exact component_120102 C A S x y z w ii
  · exact component_120110 C A S x y z w ii
  · exact component_120111 C A S x y z w ii hC hA hS hy hw hi
  · exact component_120112 C A S x y z w ii
  · exact component_120120 C A S x y z w ii
  · exact component_120121 C A S x y z w ii
  · exact component_120122 C A S x y z w ii
  · exact component_120200 C A S x y z w ii
  · exact component_120201 C A S x y z w ii hC hA hS hy hw hi
  · exact component_120202 C A S x y z w ii
  · exact component_120210 C A S x y z w ii hC hA hS hy hw hi
  · exact component_120211 C A S x y z w ii
  · exact component_120212 C A S x y z w ii
  · exact component_120220 C A S x y z w ii
  · exact component_120221 C A S x y z w ii
  · exact component_120222 C A S x y z w ii

include hC hA hS hy hw hi in
lemma block_121 (d e f : Fin 3) :
    leftComponent C A S x y z w ii 1 2 1 d e f =
    rightComponent C A S x y z w ii 1 2 1 d e f := by
  fin_cases d <;> fin_cases e <;> fin_cases f
  · exact component_121000 C A S x y z w ii
  · exact component_121001 C A S x y z w ii
  · exact component_121002 C A S x y z w ii
  · exact component_121010 C A S x y z w ii
  · exact component_121011 C A S x y z w ii
  · exact component_121012 C A S x y z w ii
  · exact component_121020 C A S x y z w ii
  · exact component_121021 C A S x y z w ii
  · exact component_121022 C A S x y z w ii hC hA hS hy hw
  · exact component_121100 C A S x y z w ii
  · exact component_121101 C A S x y z w ii
  · exact component_121102 C A S x y z w ii
  · exact component_121110 C A S x y z w ii
  · exact component_121111 C A S x y z w ii
  · exact component_121112 C A S x y z w ii hC hA hS hy hw hi
  · exact component_121120 C A S x y z w ii
  · exact component_121121 C A S x y z w ii
  · exact component_121122 C A S x y z w ii
  · exact component_121200 C A S x y z w ii
  · exact component_121201 C A S x y z w ii
  · exact component_121202 C A S x y z w ii hC hA hS hy hw hi
  · exact component_121210 C A S x y z w ii
  · exact component_121211 C A S x y z w ii hC hA hS hy hw hi
  · exact component_121212 C A S x y z w ii
  · exact component_121220 C A S x y z w ii hC hA hS hy hw
  · exact component_121221 C A S x y z w ii
  · exact component_121222 C A S x y z w ii

include hC hA hS hy hw in
lemma block_122 (d e f : Fin 3) :
    leftComponent C A S x y z w ii 1 2 2 d e f =
    rightComponent C A S x y z w ii 1 2 2 d e f := by
  fin_cases d <;> fin_cases e <;> fin_cases f
  · exact component_122000 C A S x y z w ii
  · exact component_122001 C A S x y z w ii
  · exact component_122002 C A S x y z w ii
  · exact component_122010 C A S x y z w ii
  · exact component_122011 C A S x y z w ii
  · exact component_122012 C A S x y z w ii
  · exact component_122020 C A S x y z w ii
  · exact component_122021 C A S x y z w ii
  · exact component_122022 C A S x y z w ii
  · exact component_122100 C A S x y z w ii
  · exact component_122101 C A S x y z w ii
  · exact component_122102 C A S x y z w ii
  · exact component_122110 C A S x y z w ii
  · exact component_122111 C A S x y z w ii
  · exact component_122112 C A S x y z w ii
  · exact component_122120 C A S x y z w ii
  · exact component_122121 C A S x y z w ii
  · exact component_122122 C A S x y z w ii
  · exact component_122200 C A S x y z w ii
  · exact component_122201 C A S x y z w ii
  · exact component_122202 C A S x y z w ii
  · exact component_122210 C A S x y z w ii
  · exact component_122211 C A S x y z w ii
  · exact component_122212 C A S x y z w ii
  · exact component_122220 C A S x y z w ii
  · exact component_122221 C A S x y z w ii hC hA hS hy hw
  · exact component_122222 C A S x y z w ii

end Algebra
end CriticalHoneycomb.Transfer.YangBaxter

end OAI
