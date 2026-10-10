import OAI.Combinatorics.HoneycombChords.YangBaxterPolynomialsPositive
import OAI.Combinatorics.HoneycombChords.YangBaxterSupport
import Mathlib.Tactic.FinCases

namespace OAI

/-! Yang–Baxter components with first spin positive.

This development follows the finite strip transfer calculation for critical honeycomb
walks in the companion paper on uniform marked polygon estimates. -/


namespace CriticalHoneycomb.Transfer.YangBaxter
open scoped BigOperators

section Algebra
variable (C A S x y z w ii : ℂ)
variable (hC : C = (2*S+1)*A) (hA : A^2 = (1-S)/2)
  (hS : S^2 = 1/2) (hy : y^2+x^2=1) (hw : w^2+z^2=1) (hi : ii^2+1=0)

include hy in
lemma component_001010 :
    leftComponent C A S x y z w ii 0 0 1 0 1 0 =
    rightComponent C A S x y z w ii 0 0 1 0 1 0 := by
  simp only [leftComponent, rightComponent, Fin.sum_univ_three, numerator, Fin.val_zero, Fin.val_one, finThreeTwo, mul_zero, zero_mul, zero_add, add_zero]
  have hp := polynomial_001010 C A S x y z w ii hy
  dsimp only [poly_001010_0, complexAdd, complexMul, complexPow] at hp
  linear_combination hp

include hC hA hS hy hw in
lemma component_001100 :
    leftComponent C A S x y z w ii 0 0 1 1 0 0 =
    rightComponent C A S x y z w ii 0 0 1 1 0 0 := by
  simp only [leftComponent, rightComponent, Fin.sum_univ_three, numerator, Fin.val_zero, Fin.val_one, finThreeTwo, mul_zero, zero_mul, zero_add, add_zero]
  have hp := polynomial_001100 C A S x y z w ii hC hA hS hy hw
  dsimp only [poly_001100_0, complexAdd, complexMul, complexPow] at hp
  linear_combination hp

include hC hA hS hy hw in
lemma component_002011 :
    leftComponent C A S x y z w ii 0 0 2 0 1 1 =
    rightComponent C A S x y z w ii 0 0 2 0 1 1 := by
  simp only [leftComponent, rightComponent, Fin.sum_univ_three, numerator, Fin.val_zero, Fin.val_one, finThreeTwo, mul_zero, zero_mul, zero_add, add_zero]
  have hp := polynomial_002011 C A S x y z w ii hC hA hS hy hw
  dsimp only [poly_002011_0, complexAdd, complexMul, complexPow] at hp
  linear_combination hp

include hC hA hS hy hw hi in
lemma component_002020 :
    leftComponent C A S x y z w ii 0 0 2 0 2 0 =
    rightComponent C A S x y z w ii 0 0 2 0 2 0 := by
  simp only [leftComponent, rightComponent, Fin.sum_univ_three, numerator, Fin.val_zero, Fin.val_one, finThreeTwo, mul_zero, zero_mul, zero_add, add_zero]
  have hp := polynomial_002020 C A S x y z w ii hC hA hS hy hw hi
  dsimp only [poly_002020_0, complexAdd, complexMul, complexPow] at hp
  linear_combination hp

include hC hA hS hy hw in
lemma component_002101 :
    leftComponent C A S x y z w ii 0 0 2 1 0 1 =
    rightComponent C A S x y z w ii 0 0 2 1 0 1 := by
  simp only [leftComponent, rightComponent, Fin.sum_univ_three, numerator, Fin.val_zero, Fin.val_one, finThreeTwo, mul_zero, zero_mul, zero_add, add_zero]
  have hp := polynomial_002101 C A S x y z w ii hC hA hS hy hw
  dsimp only [poly_002101_0, complexAdd, complexMul, complexPow] at hp
  linear_combination hp

include hC hA hS hy hw hi in
lemma component_002110 :
    leftComponent C A S x y z w ii 0 0 2 1 1 0 =
    rightComponent C A S x y z w ii 0 0 2 1 1 0 := by
  simp only [leftComponent, rightComponent, Fin.sum_univ_three, numerator, Fin.val_zero, Fin.val_one, finThreeTwo, mul_zero, zero_mul, zero_add, add_zero]
  have hp := polynomial_002110 C A S x y z w ii hC hA hS hy hw hi
  dsimp only [poly_002110_0, complexAdd, complexMul, complexPow] at hp
  linear_combination hp

include hC hA hS hy hw hi in
lemma component_002200 :
    leftComponent C A S x y z w ii 0 0 2 2 0 0 =
    rightComponent C A S x y z w ii 0 0 2 2 0 0 := by
  simp only [leftComponent, rightComponent, Fin.sum_univ_three, numerator, Fin.val_zero, Fin.val_one, finThreeTwo, mul_zero, zero_mul, zero_add, add_zero]
  have hp := polynomial_002200 C A S x y z w ii hC hA hS hy hw hi
  dsimp only [poly_002200_0, complexAdd, complexMul, complexPow] at hp
  linear_combination hp

include hC hA hS hy hw in
lemma component_011002 :
    leftComponent C A S x y z w ii 0 1 1 0 0 2 =
    rightComponent C A S x y z w ii 0 1 1 0 0 2 := by
  simp only [leftComponent, rightComponent, Fin.sum_univ_three, numerator, Fin.val_zero, Fin.val_one, finThreeTwo, mul_zero, zero_mul, zero_add, add_zero]
  have hp := polynomial_011002 C A S x y z w ii hC hA hS hy hw
  dsimp only [poly_011002_0, complexAdd, complexMul, complexPow] at hp
  linear_combination hp

include hC hA hS hy hw hi in
lemma component_011020 :
    leftComponent C A S x y z w ii 0 1 1 0 2 0 =
    rightComponent C A S x y z w ii 0 1 1 0 2 0 := by
  simp only [leftComponent, rightComponent, Fin.sum_univ_three, numerator, Fin.val_zero, Fin.val_one, finThreeTwo, mul_zero, zero_mul, zero_add, add_zero]
  have hp := polynomial_011020 C A S x y z w ii hC hA hS hy hw hi
  dsimp only [poly_011020_0, complexAdd, complexMul, complexPow] at hp
  linear_combination hp

include hC hA hS hy hw hi in
lemma component_011101 :
    leftComponent C A S x y z w ii 0 1 1 1 0 1 =
    rightComponent C A S x y z w ii 0 1 1 1 0 1 := by
  simp only [leftComponent, rightComponent, Fin.sum_univ_three, numerator, Fin.val_zero, Fin.val_one, finThreeTwo, mul_zero, zero_mul, zero_add, add_zero]
  have hp := polynomial_011101 C A S x y z w ii hC hA hS hy hw hi
  dsimp only [poly_011101_0, complexAdd, complexMul, complexPow] at hp
  linear_combination hp

include hC hA hS hy hw hi in
lemma component_011110 :
    leftComponent C A S x y z w ii 0 1 1 1 1 0 =
    rightComponent C A S x y z w ii 0 1 1 1 1 0 := by
  simp only [leftComponent, rightComponent, Fin.sum_univ_three, numerator, Fin.val_zero, Fin.val_one, finThreeTwo, mul_zero, zero_mul, zero_add, add_zero]
  have hp := polynomial_011110 C A S x y z w ii hC hA hS hy hw hi
  dsimp only [poly_011110_0, complexAdd, complexMul, complexPow] at hp
  linear_combination hp

include hC hA hS hy hw hi in
lemma component_011200 :
    leftComponent C A S x y z w ii 0 1 1 2 0 0 =
    rightComponent C A S x y z w ii 0 1 1 2 0 0 := by
  simp only [leftComponent, rightComponent, Fin.sum_univ_three, numerator, Fin.val_zero, Fin.val_one, finThreeTwo, mul_zero, zero_mul, zero_add, add_zero]
  have hp := polynomial_011200 C A S x y z w ii hC hA hS hy hw hi
  dsimp only [poly_011200_0, complexAdd, complexMul, complexPow] at hp
  linear_combination hp

include hC hA hS hy hw hi in
lemma component_012021 :
    leftComponent C A S x y z w ii 0 1 2 0 2 1 =
    rightComponent C A S x y z w ii 0 1 2 0 2 1 := by
  simp only [leftComponent, rightComponent, Fin.sum_univ_three, numerator, Fin.val_zero, Fin.val_one, finThreeTwo, mul_zero, zero_mul, zero_add, add_zero]
  have hp := polynomial_012021 C A S x y z w ii hC hA hS hy hw hi
  dsimp only [poly_012021_0, complexAdd, complexMul, complexPow] at hp
  linear_combination hp

include hC hA hS hy hw hi in
lemma component_012102 :
    leftComponent C A S x y z w ii 0 1 2 1 0 2 =
    rightComponent C A S x y z w ii 0 1 2 1 0 2 := by
  simp only [leftComponent, rightComponent, Fin.sum_univ_three, numerator, Fin.val_zero, Fin.val_one, finThreeTwo, mul_zero, zero_mul, zero_add, add_zero]
  have hp := polynomial_012102 C A S x y z w ii hC hA hS hy hw hi
  dsimp only [poly_012102_0, complexAdd, complexMul, complexPow] at hp
  linear_combination hp

include hC hA hS hy hw in
lemma component_012111 :
    leftComponent C A S x y z w ii 0 1 2 1 1 1 =
    rightComponent C A S x y z w ii 0 1 2 1 1 1 := by
  simp only [leftComponent, rightComponent, Fin.sum_univ_three, numerator, Fin.val_zero, Fin.val_one, finThreeTwo, mul_zero, zero_mul, zero_add, add_zero]
  have hp := polynomial_012111 C A S x y z w ii hC hA hS hy hw
  dsimp only [poly_012111_0, complexAdd, complexMul, complexPow] at hp
  linear_combination hp

include hC hA hS hy hw hi in
lemma component_012120 :
    leftComponent C A S x y z w ii 0 1 2 1 2 0 =
    rightComponent C A S x y z w ii 0 1 2 1 2 0 := by
  simp only [leftComponent, rightComponent, Fin.sum_univ_three, numerator, Fin.val_zero, Fin.val_one, finThreeTwo, mul_zero, zero_mul, zero_add, add_zero]
  have hp := polynomial_012120 C A S x y z w ii hC hA hS hy hw hi
  dsimp only [poly_012120_0, complexAdd, complexMul, complexPow] at hp
  linear_combination hp

include hC hA hS hy hw hi in
lemma component_012201 :
    leftComponent C A S x y z w ii 0 1 2 2 0 1 =
    rightComponent C A S x y z w ii 0 1 2 2 0 1 := by
  simp only [leftComponent, rightComponent, Fin.sum_univ_three, numerator, Fin.val_zero, Fin.val_one, finThreeTwo, mul_zero, zero_mul, zero_add, add_zero]
  have hp := polynomial_012201 C A S x y z w ii hC hA hS hy hw hi
  dsimp only [poly_012201_0, complexAdd, complexMul, complexPow] at hp
  linear_combination hp

include hC hA hS hy hw hi in
lemma component_020011 :
    leftComponent C A S x y z w ii 0 2 0 0 1 1 =
    rightComponent C A S x y z w ii 0 2 0 0 1 1 := by
  simp only [leftComponent, rightComponent, Fin.sum_univ_three, numerator, Fin.val_zero, Fin.val_one, finThreeTwo, mul_zero, zero_mul, zero_add, add_zero]
  have hp := polynomial_020011 C A S x y z w ii hC hA hS hy hw hi
  dsimp only [poly_020011_0, complexAdd, complexMul, complexPow] at hp
  linear_combination hp

include hC hA hS hy hw hi in
lemma component_020020 :
    leftComponent C A S x y z w ii 0 2 0 0 2 0 =
    rightComponent C A S x y z w ii 0 2 0 0 2 0 := by
  simp only [leftComponent, rightComponent, Fin.sum_univ_three, numerator, Fin.val_zero, Fin.val_one, finThreeTwo, mul_zero, zero_mul, zero_add, add_zero]
  have hp := polynomial_020020 C A S x y z w ii hC hA hS hy hw hi
  dsimp only [poly_020020_0, complexAdd, complexMul, complexPow] at hp
  linear_combination hp

include hC hA hS hy hw hi in
lemma component_020101 :
    leftComponent C A S x y z w ii 0 2 0 1 0 1 =
    rightComponent C A S x y z w ii 0 2 0 1 0 1 := by
  simp only [leftComponent, rightComponent, Fin.sum_univ_three, numerator, Fin.val_zero, Fin.val_one, finThreeTwo, mul_zero, zero_mul, zero_add, add_zero]
  have hp := polynomial_020101 C A S x y z w ii hC hA hS hy hw hi
  dsimp only [poly_020101_0, complexAdd, complexMul, complexPow] at hp
  linear_combination hp

include hC hA hS hy hw hi in
lemma component_020110 :
    leftComponent C A S x y z w ii 0 2 0 1 1 0 =
    rightComponent C A S x y z w ii 0 2 0 1 1 0 := by
  simp only [leftComponent, rightComponent, Fin.sum_univ_three, numerator, Fin.val_zero, Fin.val_one, finThreeTwo, mul_zero, zero_mul, zero_add, add_zero]
  have hp := polynomial_020110 C A S x y z w ii hC hA hS hy hw hi
  dsimp only [poly_020110_0, complexAdd, complexMul, complexPow] at hp
  linear_combination hp

include hC hA hS hy hw hi in
lemma component_021102 :
    leftComponent C A S x y z w ii 0 2 1 1 0 2 =
    rightComponent C A S x y z w ii 0 2 1 1 0 2 := by
  simp only [leftComponent, rightComponent, Fin.sum_univ_three, numerator, Fin.val_zero, Fin.val_one, finThreeTwo, mul_zero, zero_mul, zero_add, add_zero]
  have hp := polynomial_021102 C A S x y z w ii hC hA hS hy hw hi
  dsimp only [poly_021102_0, complexAdd, complexMul, complexPow] at hp
  linear_combination hp

include hC hA hS hy hw hi in
lemma component_021111 :
    leftComponent C A S x y z w ii 0 2 1 1 1 1 =
    rightComponent C A S x y z w ii 0 2 1 1 1 1 := by
  simp only [leftComponent, rightComponent, Fin.sum_univ_three, numerator, Fin.val_zero, Fin.val_one, finThreeTwo, mul_zero, zero_mul, zero_add, add_zero]
  have hp := polynomial_021111 C A S x y z w ii hC hA hS hy hw hi
  dsimp only [poly_021111_0, complexAdd, complexMul, complexPow] at hp
  linear_combination hp

include hC hA hS hy hw hi in
lemma component_021120 :
    leftComponent C A S x y z w ii 0 2 1 1 2 0 =
    rightComponent C A S x y z w ii 0 2 1 1 2 0 := by
  simp only [leftComponent, rightComponent, Fin.sum_univ_three, numerator, Fin.val_zero, Fin.val_one, finThreeTwo, mul_zero, zero_mul, zero_add, add_zero]
  have hp := polynomial_021120 C A S x y z w ii hC hA hS hy hw hi
  dsimp only [poly_021120_0, complexAdd, complexMul, complexPow] at hp
  linear_combination hp

include hC hA hS hy hw in
lemma component_022112 :
    leftComponent C A S x y z w ii 0 2 2 1 1 2 =
    rightComponent C A S x y z w ii 0 2 2 1 1 2 := by
  simp only [leftComponent, rightComponent, Fin.sum_univ_three, numerator, Fin.val_zero, Fin.val_one, finThreeTwo, mul_zero, zero_mul, zero_add, add_zero]
  have hp := polynomial_022112 C A S x y z w ii hC hA hS hy hw
  dsimp only [poly_022112_0, complexAdd, complexMul, complexPow] at hp
  linear_combination hp

include hC hA hS hy hw in
lemma component_022121 :
    leftComponent C A S x y z w ii 0 2 2 1 2 1 =
    rightComponent C A S x y z w ii 0 2 2 1 2 1 := by
  simp only [leftComponent, rightComponent, Fin.sum_univ_three, numerator, Fin.val_zero, Fin.val_one, finThreeTwo, mul_zero, zero_mul, zero_add, add_zero]
  have hp := polynomial_022121 C A S x y z w ii hC hA hS hy hw
  dsimp only [poly_022121_0, complexAdd, complexMul, complexPow] at hp
  linear_combination hp

include hy in
lemma component_010001 :
    leftComponent C A S x y z w ii 0 1 0 0 0 1 =
    rightComponent C A S x y z w ii 0 1 0 0 0 1 := by
  simp only [leftComponent, rightComponent, Fin.sum_univ_three, numerator, Fin.val_zero, Fin.val_one, finThreeTwo, mul_zero, zero_mul, zero_add, add_zero]
  have hp := polynomial_001010 C A S x y z w ii hy
  dsimp only [poly_001010_0, complexAdd, complexMul, complexPow] at hp
  linear_combination (-1:ℂ)/1*hp

include hC hA hS hy hw hi in
lemma component_020002 :
    leftComponent C A S x y z w ii 0 2 0 0 0 2 =
    rightComponent C A S x y z w ii 0 2 0 0 0 2 := by
  simp only [leftComponent, rightComponent, Fin.sum_univ_three, numerator, Fin.val_zero, Fin.val_one, finThreeTwo, mul_zero, zero_mul, zero_add, add_zero]
  have hp := polynomial_002020 C A S x y z w ii hC hA hS hy hw hi
  dsimp only [poly_002020_0, complexAdd, complexMul, complexPow] at hp
  linear_combination (-1:ℂ)/1*hp

include hC hA hS hy hw hi in
lemma component_020200 :
    leftComponent C A S x y z w ii 0 2 0 2 0 0 =
    rightComponent C A S x y z w ii 0 2 0 2 0 0 := by
  simp only [leftComponent, rightComponent, Fin.sum_univ_three, numerator, Fin.val_zero, Fin.val_one, finThreeTwo, mul_zero, zero_mul, zero_add, add_zero]
  have hp := polynomial_002020 C A S x y z w ii hC hA hS hy hw hi
  dsimp only [poly_002020_0, complexAdd, complexMul, complexPow] at hp
  linear_combination (1:ℂ)/1*hp

include hC hA hS hy hw hi in
lemma component_021012 :
    leftComponent C A S x y z w ii 0 2 1 0 1 2 =
    rightComponent C A S x y z w ii 0 2 1 0 1 2 := by
  simp only [leftComponent, rightComponent, Fin.sum_univ_three, numerator, Fin.val_zero, Fin.val_one, finThreeTwo, mul_zero, zero_mul, zero_add, add_zero]
  have hp := polynomial_012021 C A S x y z w ii hC hA hS hy hw hi
  dsimp only [poly_012021_0, complexAdd, complexMul, complexPow] at hp
  linear_combination (-1:ℂ)/1*hp

include hC hA hS hy hw hi in
lemma component_021210 :
    leftComponent C A S x y z w ii 0 2 1 2 1 0 =
    rightComponent C A S x y z w ii 0 2 1 2 1 0 := by
  simp only [leftComponent, rightComponent, Fin.sum_univ_three, numerator, Fin.val_zero, Fin.val_one, finThreeTwo, mul_zero, zero_mul, zero_add, add_zero]
  have hp := polynomial_012201 C A S x y z w ii hC hA hS hy hw hi
  dsimp only [poly_012201_0, complexAdd, complexMul, complexPow] at hp
  linear_combination (-1:ℂ)/1*hp

include hC hA hS hy hw hi in
lemma component_022202 :
    leftComponent C A S x y z w ii 0 2 2 2 0 2 =
    rightComponent C A S x y z w ii 0 2 2 2 0 2 := by
  simp only [leftComponent, rightComponent, Fin.sum_univ_three, numerator, Fin.val_zero, Fin.val_one, finThreeTwo, mul_zero, zero_mul, zero_add, add_zero]
  have hp := polynomial_002020 C A S x y z w ii hC hA hS hy hw hi
  dsimp only [poly_002020_0, complexAdd, complexMul, complexPow] at hp
  linear_combination (-1:ℂ)/1*hp

include hC hA hS hy hw hi in
lemma component_022211 :
    leftComponent C A S x y z w ii 0 2 2 2 1 1 =
    rightComponent C A S x y z w ii 0 2 2 2 1 1 := by
  simp only [leftComponent, rightComponent, Fin.sum_univ_three, numerator, Fin.val_zero, Fin.val_one, finThreeTwo, mul_zero, zero_mul, zero_add, add_zero]
  have hp := polynomial_011200 C A S x y z w ii hC hA hS hy hw hi
  dsimp only [poly_011200_0, complexAdd, complexMul, complexPow] at hp
  linear_combination (-1:ℂ)/1*hp

include hC hA hS hy hw hi in
lemma component_022220 :
    leftComponent C A S x y z w ii 0 2 2 2 2 0 =
    rightComponent C A S x y z w ii 0 2 2 2 2 0 := by
  simp only [leftComponent, rightComponent, Fin.sum_univ_three, numerator, Fin.val_zero, Fin.val_one, finThreeTwo, mul_zero, zero_mul, zero_add, add_zero]
  have hp := polynomial_002200 C A S x y z w ii hC hA hS hy hw hi
  dsimp only [poly_002200_0, complexAdd, complexMul, complexPow] at hp
  linear_combination (-1:ℂ)/1*hp

lemma component_000000 :
    leftComponent C A S x y z w ii 0 0 0 0 0 0 =
    rightComponent C A S x y z w ii 0 0 0 0 0 0 := by
  simp only [leftComponent, rightComponent, Fin.sum_univ_three, numerator, Fin.val_zero, Fin.val_one, finThreeTwo, mul_zero, zero_mul, add_zero]
  ; ring

lemma component_000001 :
    leftComponent C A S x y z w ii 0 0 0 0 0 1 =
    rightComponent C A S x y z w ii 0 0 0 0 0 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 0 0 0 0 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 0 0 0 0 1 (by decide)]

lemma component_000002 :
    leftComponent C A S x y z w ii 0 0 0 0 0 2 =
    rightComponent C A S x y z w ii 0 0 0 0 0 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 0 0 0 0 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 0 0 0 0 2 (by decide)]

lemma component_000010 :
    leftComponent C A S x y z w ii 0 0 0 0 1 0 =
    rightComponent C A S x y z w ii 0 0 0 0 1 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 0 0 0 1 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 0 0 0 1 0 (by decide)]

lemma component_000011 :
    leftComponent C A S x y z w ii 0 0 0 0 1 1 =
    rightComponent C A S x y z w ii 0 0 0 0 1 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 0 0 0 1 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 0 0 0 1 1 (by decide)]

lemma component_000012 :
    leftComponent C A S x y z w ii 0 0 0 0 1 2 =
    rightComponent C A S x y z w ii 0 0 0 0 1 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 0 0 0 1 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 0 0 0 1 2 (by decide)]

lemma component_000020 :
    leftComponent C A S x y z w ii 0 0 0 0 2 0 =
    rightComponent C A S x y z w ii 0 0 0 0 2 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 0 0 0 2 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 0 0 0 2 0 (by decide)]

lemma component_000021 :
    leftComponent C A S x y z w ii 0 0 0 0 2 1 =
    rightComponent C A S x y z w ii 0 0 0 0 2 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 0 0 0 2 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 0 0 0 2 1 (by decide)]

lemma component_000022 :
    leftComponent C A S x y z w ii 0 0 0 0 2 2 =
    rightComponent C A S x y z w ii 0 0 0 0 2 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 0 0 0 2 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 0 0 0 2 2 (by decide)]

lemma component_000100 :
    leftComponent C A S x y z w ii 0 0 0 1 0 0 =
    rightComponent C A S x y z w ii 0 0 0 1 0 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 0 0 1 0 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 0 0 1 0 0 (by decide)]

lemma component_000101 :
    leftComponent C A S x y z w ii 0 0 0 1 0 1 =
    rightComponent C A S x y z w ii 0 0 0 1 0 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 0 0 1 0 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 0 0 1 0 1 (by decide)]

lemma component_000102 :
    leftComponent C A S x y z w ii 0 0 0 1 0 2 =
    rightComponent C A S x y z w ii 0 0 0 1 0 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 0 0 1 0 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 0 0 1 0 2 (by decide)]

lemma component_000110 :
    leftComponent C A S x y z w ii 0 0 0 1 1 0 =
    rightComponent C A S x y z w ii 0 0 0 1 1 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 0 0 1 1 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 0 0 1 1 0 (by decide)]

lemma component_000111 :
    leftComponent C A S x y z w ii 0 0 0 1 1 1 =
    rightComponent C A S x y z w ii 0 0 0 1 1 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 0 0 1 1 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 0 0 1 1 1 (by decide)]

lemma component_000112 :
    leftComponent C A S x y z w ii 0 0 0 1 1 2 =
    rightComponent C A S x y z w ii 0 0 0 1 1 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 0 0 1 1 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 0 0 1 1 2 (by decide)]

lemma component_000120 :
    leftComponent C A S x y z w ii 0 0 0 1 2 0 =
    rightComponent C A S x y z w ii 0 0 0 1 2 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 0 0 1 2 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 0 0 1 2 0 (by decide)]

lemma component_000121 :
    leftComponent C A S x y z w ii 0 0 0 1 2 1 =
    rightComponent C A S x y z w ii 0 0 0 1 2 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 0 0 1 2 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 0 0 1 2 1 (by decide)]

lemma component_000122 :
    leftComponent C A S x y z w ii 0 0 0 1 2 2 =
    rightComponent C A S x y z w ii 0 0 0 1 2 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 0 0 1 2 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 0 0 1 2 2 (by decide)]

lemma component_000200 :
    leftComponent C A S x y z w ii 0 0 0 2 0 0 =
    rightComponent C A S x y z w ii 0 0 0 2 0 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 0 0 2 0 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 0 0 2 0 0 (by decide)]

lemma component_000201 :
    leftComponent C A S x y z w ii 0 0 0 2 0 1 =
    rightComponent C A S x y z w ii 0 0 0 2 0 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 0 0 2 0 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 0 0 2 0 1 (by decide)]

lemma component_000202 :
    leftComponent C A S x y z w ii 0 0 0 2 0 2 =
    rightComponent C A S x y z w ii 0 0 0 2 0 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 0 0 2 0 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 0 0 2 0 2 (by decide)]

lemma component_000210 :
    leftComponent C A S x y z w ii 0 0 0 2 1 0 =
    rightComponent C A S x y z w ii 0 0 0 2 1 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 0 0 2 1 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 0 0 2 1 0 (by decide)]

lemma component_000211 :
    leftComponent C A S x y z w ii 0 0 0 2 1 1 =
    rightComponent C A S x y z w ii 0 0 0 2 1 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 0 0 2 1 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 0 0 2 1 1 (by decide)]

lemma component_000212 :
    leftComponent C A S x y z w ii 0 0 0 2 1 2 =
    rightComponent C A S x y z w ii 0 0 0 2 1 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 0 0 2 1 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 0 0 2 1 2 (by decide)]

lemma component_000220 :
    leftComponent C A S x y z w ii 0 0 0 2 2 0 =
    rightComponent C A S x y z w ii 0 0 0 2 2 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 0 0 2 2 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 0 0 2 2 0 (by decide)]

lemma component_000221 :
    leftComponent C A S x y z w ii 0 0 0 2 2 1 =
    rightComponent C A S x y z w ii 0 0 0 2 2 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 0 0 2 2 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 0 0 2 2 1 (by decide)]

lemma component_000222 :
    leftComponent C A S x y z w ii 0 0 0 2 2 2 =
    rightComponent C A S x y z w ii 0 0 0 2 2 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 0 0 2 2 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 0 0 2 2 2 (by decide)]

lemma component_001000 :
    leftComponent C A S x y z w ii 0 0 1 0 0 0 =
    rightComponent C A S x y z w ii 0 0 1 0 0 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 0 1 0 0 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 0 1 0 0 0 (by decide)]

lemma component_001001 :
    leftComponent C A S x y z w ii 0 0 1 0 0 1 =
    rightComponent C A S x y z w ii 0 0 1 0 0 1 := by
  simp only [leftComponent, rightComponent, Fin.sum_univ_three, numerator, Fin.val_zero, Fin.val_one, finThreeTwo, mul_zero, zero_mul, zero_add, add_zero]
  ; ring

lemma component_001002 :
    leftComponent C A S x y z w ii 0 0 1 0 0 2 =
    rightComponent C A S x y z w ii 0 0 1 0 0 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 0 1 0 0 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 0 1 0 0 2 (by decide)]

lemma component_001011 :
    leftComponent C A S x y z w ii 0 0 1 0 1 1 =
    rightComponent C A S x y z w ii 0 0 1 0 1 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 0 1 0 1 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 0 1 0 1 1 (by decide)]

lemma component_001012 :
    leftComponent C A S x y z w ii 0 0 1 0 1 2 =
    rightComponent C A S x y z w ii 0 0 1 0 1 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 0 1 0 1 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 0 1 0 1 2 (by decide)]

lemma component_001020 :
    leftComponent C A S x y z w ii 0 0 1 0 2 0 =
    rightComponent C A S x y z w ii 0 0 1 0 2 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 0 1 0 2 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 0 1 0 2 0 (by decide)]

lemma component_001021 :
    leftComponent C A S x y z w ii 0 0 1 0 2 1 =
    rightComponent C A S x y z w ii 0 0 1 0 2 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 0 1 0 2 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 0 1 0 2 1 (by decide)]

lemma component_001022 :
    leftComponent C A S x y z w ii 0 0 1 0 2 2 =
    rightComponent C A S x y z w ii 0 0 1 0 2 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 0 1 0 2 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 0 1 0 2 2 (by decide)]

lemma component_001101 :
    leftComponent C A S x y z w ii 0 0 1 1 0 1 =
    rightComponent C A S x y z w ii 0 0 1 1 0 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 0 1 1 0 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 0 1 1 0 1 (by decide)]

lemma component_001102 :
    leftComponent C A S x y z w ii 0 0 1 1 0 2 =
    rightComponent C A S x y z w ii 0 0 1 1 0 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 0 1 1 0 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 0 1 1 0 2 (by decide)]

lemma component_001110 :
    leftComponent C A S x y z w ii 0 0 1 1 1 0 =
    rightComponent C A S x y z w ii 0 0 1 1 1 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 0 1 1 1 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 0 1 1 1 0 (by decide)]

lemma component_001111 :
    leftComponent C A S x y z w ii 0 0 1 1 1 1 =
    rightComponent C A S x y z w ii 0 0 1 1 1 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 0 1 1 1 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 0 1 1 1 1 (by decide)]

lemma component_001112 :
    leftComponent C A S x y z w ii 0 0 1 1 1 2 =
    rightComponent C A S x y z w ii 0 0 1 1 1 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 0 1 1 1 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 0 1 1 1 2 (by decide)]

lemma component_001120 :
    leftComponent C A S x y z w ii 0 0 1 1 2 0 =
    rightComponent C A S x y z w ii 0 0 1 1 2 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 0 1 1 2 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 0 1 1 2 0 (by decide)]

lemma component_001121 :
    leftComponent C A S x y z w ii 0 0 1 1 2 1 =
    rightComponent C A S x y z w ii 0 0 1 1 2 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 0 1 1 2 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 0 1 1 2 1 (by decide)]

lemma component_001122 :
    leftComponent C A S x y z w ii 0 0 1 1 2 2 =
    rightComponent C A S x y z w ii 0 0 1 1 2 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 0 1 1 2 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 0 1 1 2 2 (by decide)]

lemma component_001200 :
    leftComponent C A S x y z w ii 0 0 1 2 0 0 =
    rightComponent C A S x y z w ii 0 0 1 2 0 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 0 1 2 0 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 0 1 2 0 0 (by decide)]

lemma component_001201 :
    leftComponent C A S x y z w ii 0 0 1 2 0 1 =
    rightComponent C A S x y z w ii 0 0 1 2 0 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 0 1 2 0 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 0 1 2 0 1 (by decide)]

lemma component_001202 :
    leftComponent C A S x y z w ii 0 0 1 2 0 2 =
    rightComponent C A S x y z w ii 0 0 1 2 0 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 0 1 2 0 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 0 1 2 0 2 (by decide)]

lemma component_001210 :
    leftComponent C A S x y z w ii 0 0 1 2 1 0 =
    rightComponent C A S x y z w ii 0 0 1 2 1 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 0 1 2 1 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 0 1 2 1 0 (by decide)]

lemma component_001211 :
    leftComponent C A S x y z w ii 0 0 1 2 1 1 =
    rightComponent C A S x y z w ii 0 0 1 2 1 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 0 1 2 1 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 0 1 2 1 1 (by decide)]

lemma component_001212 :
    leftComponent C A S x y z w ii 0 0 1 2 1 2 =
    rightComponent C A S x y z w ii 0 0 1 2 1 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 0 1 2 1 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 0 1 2 1 2 (by decide)]

lemma component_001220 :
    leftComponent C A S x y z w ii 0 0 1 2 2 0 =
    rightComponent C A S x y z w ii 0 0 1 2 2 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 0 1 2 2 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 0 1 2 2 0 (by decide)]

lemma component_001221 :
    leftComponent C A S x y z w ii 0 0 1 2 2 1 =
    rightComponent C A S x y z w ii 0 0 1 2 2 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 0 1 2 2 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 0 1 2 2 1 (by decide)]

lemma component_001222 :
    leftComponent C A S x y z w ii 0 0 1 2 2 2 =
    rightComponent C A S x y z w ii 0 0 1 2 2 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 0 1 2 2 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 0 1 2 2 2 (by decide)]

lemma component_002000 :
    leftComponent C A S x y z w ii 0 0 2 0 0 0 =
    rightComponent C A S x y z w ii 0 0 2 0 0 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 0 2 0 0 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 0 2 0 0 0 (by decide)]

lemma component_002001 :
    leftComponent C A S x y z w ii 0 0 2 0 0 1 =
    rightComponent C A S x y z w ii 0 0 2 0 0 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 0 2 0 0 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 0 2 0 0 1 (by decide)]

lemma component_002002 :
    leftComponent C A S x y z w ii 0 0 2 0 0 2 =
    rightComponent C A S x y z w ii 0 0 2 0 0 2 := by
  simp only [leftComponent, rightComponent, Fin.sum_univ_three, numerator, Fin.val_zero, Fin.val_one, finThreeTwo, mul_zero, zero_mul, zero_add, add_zero]
  ; ring

lemma component_002010 :
    leftComponent C A S x y z w ii 0 0 2 0 1 0 =
    rightComponent C A S x y z w ii 0 0 2 0 1 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 0 2 0 1 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 0 2 0 1 0 (by decide)]

lemma component_002012 :
    leftComponent C A S x y z w ii 0 0 2 0 1 2 =
    rightComponent C A S x y z w ii 0 0 2 0 1 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 0 2 0 1 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 0 2 0 1 2 (by decide)]

lemma component_002021 :
    leftComponent C A S x y z w ii 0 0 2 0 2 1 =
    rightComponent C A S x y z w ii 0 0 2 0 2 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 0 2 0 2 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 0 2 0 2 1 (by decide)]

lemma component_002022 :
    leftComponent C A S x y z w ii 0 0 2 0 2 2 =
    rightComponent C A S x y z w ii 0 0 2 0 2 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 0 2 0 2 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 0 2 0 2 2 (by decide)]

lemma component_002100 :
    leftComponent C A S x y z w ii 0 0 2 1 0 0 =
    rightComponent C A S x y z w ii 0 0 2 1 0 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 0 2 1 0 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 0 2 1 0 0 (by decide)]

lemma component_002102 :
    leftComponent C A S x y z w ii 0 0 2 1 0 2 =
    rightComponent C A S x y z w ii 0 0 2 1 0 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 0 2 1 0 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 0 2 1 0 2 (by decide)]

lemma component_002111 :
    leftComponent C A S x y z w ii 0 0 2 1 1 1 =
    rightComponent C A S x y z w ii 0 0 2 1 1 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 0 2 1 1 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 0 2 1 1 1 (by decide)]

lemma component_002112 :
    leftComponent C A S x y z w ii 0 0 2 1 1 2 =
    rightComponent C A S x y z w ii 0 0 2 1 1 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 0 2 1 1 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 0 2 1 1 2 (by decide)]

lemma component_002120 :
    leftComponent C A S x y z w ii 0 0 2 1 2 0 =
    rightComponent C A S x y z w ii 0 0 2 1 2 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 0 2 1 2 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 0 2 1 2 0 (by decide)]

lemma component_002121 :
    leftComponent C A S x y z w ii 0 0 2 1 2 1 =
    rightComponent C A S x y z w ii 0 0 2 1 2 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 0 2 1 2 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 0 2 1 2 1 (by decide)]

lemma component_002122 :
    leftComponent C A S x y z w ii 0 0 2 1 2 2 =
    rightComponent C A S x y z w ii 0 0 2 1 2 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 0 2 1 2 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 0 2 1 2 2 (by decide)]

lemma component_002201 :
    leftComponent C A S x y z w ii 0 0 2 2 0 1 =
    rightComponent C A S x y z w ii 0 0 2 2 0 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 0 2 2 0 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 0 2 2 0 1 (by decide)]

lemma component_002202 :
    leftComponent C A S x y z w ii 0 0 2 2 0 2 =
    rightComponent C A S x y z w ii 0 0 2 2 0 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 0 2 2 0 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 0 2 2 0 2 (by decide)]

lemma component_002210 :
    leftComponent C A S x y z w ii 0 0 2 2 1 0 =
    rightComponent C A S x y z w ii 0 0 2 2 1 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 0 2 2 1 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 0 2 2 1 0 (by decide)]

lemma component_002211 :
    leftComponent C A S x y z w ii 0 0 2 2 1 1 =
    rightComponent C A S x y z w ii 0 0 2 2 1 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 0 2 2 1 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 0 2 2 1 1 (by decide)]

lemma component_002212 :
    leftComponent C A S x y z w ii 0 0 2 2 1 2 =
    rightComponent C A S x y z w ii 0 0 2 2 1 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 0 2 2 1 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 0 2 2 1 2 (by decide)]

lemma component_002220 :
    leftComponent C A S x y z w ii 0 0 2 2 2 0 =
    rightComponent C A S x y z w ii 0 0 2 2 2 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 0 2 2 2 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 0 2 2 2 0 (by decide)]

lemma component_002221 :
    leftComponent C A S x y z w ii 0 0 2 2 2 1 =
    rightComponent C A S x y z w ii 0 0 2 2 2 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 0 2 2 2 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 0 2 2 2 1 (by decide)]

lemma component_002222 :
    leftComponent C A S x y z w ii 0 0 2 2 2 2 =
    rightComponent C A S x y z w ii 0 0 2 2 2 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 0 2 2 2 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 0 2 2 2 2 (by decide)]

lemma component_010000 :
    leftComponent C A S x y z w ii 0 1 0 0 0 0 =
    rightComponent C A S x y z w ii 0 1 0 0 0 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 1 0 0 0 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 1 0 0 0 0 (by decide)]

lemma component_010002 :
    leftComponent C A S x y z w ii 0 1 0 0 0 2 =
    rightComponent C A S x y z w ii 0 1 0 0 0 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 1 0 0 0 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 1 0 0 0 2 (by decide)]

lemma component_010010 :
    leftComponent C A S x y z w ii 0 1 0 0 1 0 =
    rightComponent C A S x y z w ii 0 1 0 0 1 0 := by
  simp only [leftComponent, rightComponent, Fin.sum_univ_three, numerator, Fin.val_zero, Fin.val_one, finThreeTwo, mul_zero, zero_mul, zero_add, add_zero]
  ; ring

lemma component_010011 :
    leftComponent C A S x y z w ii 0 1 0 0 1 1 =
    rightComponent C A S x y z w ii 0 1 0 0 1 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 1 0 0 1 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 1 0 0 1 1 (by decide)]

lemma component_010012 :
    leftComponent C A S x y z w ii 0 1 0 0 1 2 =
    rightComponent C A S x y z w ii 0 1 0 0 1 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 1 0 0 1 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 1 0 0 1 2 (by decide)]

lemma component_010020 :
    leftComponent C A S x y z w ii 0 1 0 0 2 0 =
    rightComponent C A S x y z w ii 0 1 0 0 2 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 1 0 0 2 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 1 0 0 2 0 (by decide)]

lemma component_010021 :
    leftComponent C A S x y z w ii 0 1 0 0 2 1 =
    rightComponent C A S x y z w ii 0 1 0 0 2 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 1 0 0 2 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 1 0 0 2 1 (by decide)]

lemma component_010022 :
    leftComponent C A S x y z w ii 0 1 0 0 2 2 =
    rightComponent C A S x y z w ii 0 1 0 0 2 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 1 0 0 2 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 1 0 0 2 2 (by decide)]

lemma component_010100 :
    leftComponent C A S x y z w ii 0 1 0 1 0 0 =
    rightComponent C A S x y z w ii 0 1 0 1 0 0 := by
  simp only [leftComponent, rightComponent, Fin.sum_univ_three, numerator, Fin.val_zero, Fin.val_one, finThreeTwo, mul_zero, zero_mul, zero_add, add_zero]
  ; ring

lemma component_010101 :
    leftComponent C A S x y z w ii 0 1 0 1 0 1 =
    rightComponent C A S x y z w ii 0 1 0 1 0 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 1 0 1 0 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 1 0 1 0 1 (by decide)]

lemma component_010102 :
    leftComponent C A S x y z w ii 0 1 0 1 0 2 =
    rightComponent C A S x y z w ii 0 1 0 1 0 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 1 0 1 0 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 1 0 1 0 2 (by decide)]

lemma component_010110 :
    leftComponent C A S x y z w ii 0 1 0 1 1 0 =
    rightComponent C A S x y z w ii 0 1 0 1 1 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 1 0 1 1 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 1 0 1 1 0 (by decide)]

lemma component_010111 :
    leftComponent C A S x y z w ii 0 1 0 1 1 1 =
    rightComponent C A S x y z w ii 0 1 0 1 1 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 1 0 1 1 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 1 0 1 1 1 (by decide)]

lemma component_010112 :
    leftComponent C A S x y z w ii 0 1 0 1 1 2 =
    rightComponent C A S x y z w ii 0 1 0 1 1 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 1 0 1 1 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 1 0 1 1 2 (by decide)]

lemma component_010120 :
    leftComponent C A S x y z w ii 0 1 0 1 2 0 =
    rightComponent C A S x y z w ii 0 1 0 1 2 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 1 0 1 2 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 1 0 1 2 0 (by decide)]

lemma component_010121 :
    leftComponent C A S x y z w ii 0 1 0 1 2 1 =
    rightComponent C A S x y z w ii 0 1 0 1 2 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 1 0 1 2 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 1 0 1 2 1 (by decide)]

lemma component_010122 :
    leftComponent C A S x y z w ii 0 1 0 1 2 2 =
    rightComponent C A S x y z w ii 0 1 0 1 2 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 1 0 1 2 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 1 0 1 2 2 (by decide)]

lemma component_010200 :
    leftComponent C A S x y z w ii 0 1 0 2 0 0 =
    rightComponent C A S x y z w ii 0 1 0 2 0 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 1 0 2 0 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 1 0 2 0 0 (by decide)]

lemma component_010201 :
    leftComponent C A S x y z w ii 0 1 0 2 0 1 =
    rightComponent C A S x y z w ii 0 1 0 2 0 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 1 0 2 0 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 1 0 2 0 1 (by decide)]

lemma component_010202 :
    leftComponent C A S x y z w ii 0 1 0 2 0 2 =
    rightComponent C A S x y z w ii 0 1 0 2 0 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 1 0 2 0 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 1 0 2 0 2 (by decide)]

lemma component_010210 :
    leftComponent C A S x y z w ii 0 1 0 2 1 0 =
    rightComponent C A S x y z w ii 0 1 0 2 1 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 1 0 2 1 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 1 0 2 1 0 (by decide)]

lemma component_010211 :
    leftComponent C A S x y z w ii 0 1 0 2 1 1 =
    rightComponent C A S x y z w ii 0 1 0 2 1 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 1 0 2 1 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 1 0 2 1 1 (by decide)]

lemma component_010212 :
    leftComponent C A S x y z w ii 0 1 0 2 1 2 =
    rightComponent C A S x y z w ii 0 1 0 2 1 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 1 0 2 1 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 1 0 2 1 2 (by decide)]

lemma component_010220 :
    leftComponent C A S x y z w ii 0 1 0 2 2 0 =
    rightComponent C A S x y z w ii 0 1 0 2 2 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 1 0 2 2 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 1 0 2 2 0 (by decide)]

lemma component_010221 :
    leftComponent C A S x y z w ii 0 1 0 2 2 1 =
    rightComponent C A S x y z w ii 0 1 0 2 2 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 1 0 2 2 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 1 0 2 2 1 (by decide)]

lemma component_010222 :
    leftComponent C A S x y z w ii 0 1 0 2 2 2 =
    rightComponent C A S x y z w ii 0 1 0 2 2 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 1 0 2 2 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 1 0 2 2 2 (by decide)]

lemma component_011000 :
    leftComponent C A S x y z w ii 0 1 1 0 0 0 =
    rightComponent C A S x y z w ii 0 1 1 0 0 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 1 1 0 0 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 1 1 0 0 0 (by decide)]

lemma component_011001 :
    leftComponent C A S x y z w ii 0 1 1 0 0 1 =
    rightComponent C A S x y z w ii 0 1 1 0 0 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 1 1 0 0 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 1 1 0 0 1 (by decide)]

lemma component_011010 :
    leftComponent C A S x y z w ii 0 1 1 0 1 0 =
    rightComponent C A S x y z w ii 0 1 1 0 1 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 1 1 0 1 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 1 1 0 1 0 (by decide)]

lemma component_011011 :
    leftComponent C A S x y z w ii 0 1 1 0 1 1 =
    rightComponent C A S x y z w ii 0 1 1 0 1 1 := by
  simp only [leftComponent, rightComponent, Fin.sum_univ_three, numerator, Fin.val_zero, Fin.val_one, finThreeTwo, mul_zero, zero_mul, zero_add, add_zero]
  ; ring

lemma component_011012 :
    leftComponent C A S x y z w ii 0 1 1 0 1 2 =
    rightComponent C A S x y z w ii 0 1 1 0 1 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 1 1 0 1 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 1 1 0 1 2 (by decide)]

lemma component_011021 :
    leftComponent C A S x y z w ii 0 1 1 0 2 1 =
    rightComponent C A S x y z w ii 0 1 1 0 2 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 1 1 0 2 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 1 1 0 2 1 (by decide)]

lemma component_011022 :
    leftComponent C A S x y z w ii 0 1 1 0 2 2 =
    rightComponent C A S x y z w ii 0 1 1 0 2 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 1 1 0 2 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 1 1 0 2 2 (by decide)]

lemma component_011100 :
    leftComponent C A S x y z w ii 0 1 1 1 0 0 =
    rightComponent C A S x y z w ii 0 1 1 1 0 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 1 1 1 0 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 1 1 1 0 0 (by decide)]

lemma component_011102 :
    leftComponent C A S x y z w ii 0 1 1 1 0 2 =
    rightComponent C A S x y z w ii 0 1 1 1 0 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 1 1 1 0 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 1 1 1 0 2 (by decide)]

lemma component_011111 :
    leftComponent C A S x y z w ii 0 1 1 1 1 1 =
    rightComponent C A S x y z w ii 0 1 1 1 1 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 1 1 1 1 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 1 1 1 1 1 (by decide)]

lemma component_011112 :
    leftComponent C A S x y z w ii 0 1 1 1 1 2 =
    rightComponent C A S x y z w ii 0 1 1 1 1 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 1 1 1 1 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 1 1 1 1 2 (by decide)]

lemma component_011120 :
    leftComponent C A S x y z w ii 0 1 1 1 2 0 =
    rightComponent C A S x y z w ii 0 1 1 1 2 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 1 1 1 2 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 1 1 1 2 0 (by decide)]

lemma component_011121 :
    leftComponent C A S x y z w ii 0 1 1 1 2 1 =
    rightComponent C A S x y z w ii 0 1 1 1 2 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 1 1 1 2 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 1 1 1 2 1 (by decide)]

lemma component_011122 :
    leftComponent C A S x y z w ii 0 1 1 1 2 2 =
    rightComponent C A S x y z w ii 0 1 1 1 2 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 1 1 1 2 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 1 1 1 2 2 (by decide)]

lemma component_011201 :
    leftComponent C A S x y z w ii 0 1 1 2 0 1 =
    rightComponent C A S x y z w ii 0 1 1 2 0 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 1 1 2 0 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 1 1 2 0 1 (by decide)]

lemma component_011202 :
    leftComponent C A S x y z w ii 0 1 1 2 0 2 =
    rightComponent C A S x y z w ii 0 1 1 2 0 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 1 1 2 0 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 1 1 2 0 2 (by decide)]

lemma component_011210 :
    leftComponent C A S x y z w ii 0 1 1 2 1 0 =
    rightComponent C A S x y z w ii 0 1 1 2 1 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 1 1 2 1 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 1 1 2 1 0 (by decide)]

lemma component_011211 :
    leftComponent C A S x y z w ii 0 1 1 2 1 1 =
    rightComponent C A S x y z w ii 0 1 1 2 1 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 1 1 2 1 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 1 1 2 1 1 (by decide)]

lemma component_011212 :
    leftComponent C A S x y z w ii 0 1 1 2 1 2 =
    rightComponent C A S x y z w ii 0 1 1 2 1 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 1 1 2 1 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 1 1 2 1 2 (by decide)]

lemma component_011220 :
    leftComponent C A S x y z w ii 0 1 1 2 2 0 =
    rightComponent C A S x y z w ii 0 1 1 2 2 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 1 1 2 2 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 1 1 2 2 0 (by decide)]

lemma component_011221 :
    leftComponent C A S x y z w ii 0 1 1 2 2 1 =
    rightComponent C A S x y z w ii 0 1 1 2 2 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 1 1 2 2 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 1 1 2 2 1 (by decide)]

lemma component_011222 :
    leftComponent C A S x y z w ii 0 1 1 2 2 2 =
    rightComponent C A S x y z w ii 0 1 1 2 2 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 1 1 2 2 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 1 1 2 2 2 (by decide)]

lemma component_012000 :
    leftComponent C A S x y z w ii 0 1 2 0 0 0 =
    rightComponent C A S x y z w ii 0 1 2 0 0 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 1 2 0 0 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 1 2 0 0 0 (by decide)]

lemma component_012001 :
    leftComponent C A S x y z w ii 0 1 2 0 0 1 =
    rightComponent C A S x y z w ii 0 1 2 0 0 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 1 2 0 0 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 1 2 0 0 1 (by decide)]

lemma component_012002 :
    leftComponent C A S x y z w ii 0 1 2 0 0 2 =
    rightComponent C A S x y z w ii 0 1 2 0 0 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 1 2 0 0 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 1 2 0 0 2 (by decide)]

lemma component_012010 :
    leftComponent C A S x y z w ii 0 1 2 0 1 0 =
    rightComponent C A S x y z w ii 0 1 2 0 1 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 1 2 0 1 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 1 2 0 1 0 (by decide)]

lemma component_012011 :
    leftComponent C A S x y z w ii 0 1 2 0 1 1 =
    rightComponent C A S x y z w ii 0 1 2 0 1 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 1 2 0 1 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 1 2 0 1 1 (by decide)]

lemma component_012012 :
    leftComponent C A S x y z w ii 0 1 2 0 1 2 =
    rightComponent C A S x y z w ii 0 1 2 0 1 2 := by
  simp only [leftComponent, rightComponent, Fin.sum_univ_three, numerator, Fin.val_zero, Fin.val_one, finThreeTwo, mul_zero, zero_mul, zero_add, add_zero]
  ; ring

lemma component_012020 :
    leftComponent C A S x y z w ii 0 1 2 0 2 0 =
    rightComponent C A S x y z w ii 0 1 2 0 2 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 1 2 0 2 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 1 2 0 2 0 (by decide)]

lemma component_012022 :
    leftComponent C A S x y z w ii 0 1 2 0 2 2 =
    rightComponent C A S x y z w ii 0 1 2 0 2 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 1 2 0 2 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 1 2 0 2 2 (by decide)]

lemma component_012100 :
    leftComponent C A S x y z w ii 0 1 2 1 0 0 =
    rightComponent C A S x y z w ii 0 1 2 1 0 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 1 2 1 0 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 1 2 1 0 0 (by decide)]

lemma component_012101 :
    leftComponent C A S x y z w ii 0 1 2 1 0 1 =
    rightComponent C A S x y z w ii 0 1 2 1 0 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 1 2 1 0 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 1 2 1 0 1 (by decide)]

lemma component_012110 :
    leftComponent C A S x y z w ii 0 1 2 1 1 0 =
    rightComponent C A S x y z w ii 0 1 2 1 1 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 1 2 1 1 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 1 2 1 1 0 (by decide)]

lemma component_012112 :
    leftComponent C A S x y z w ii 0 1 2 1 1 2 =
    rightComponent C A S x y z w ii 0 1 2 1 1 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 1 2 1 1 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 1 2 1 1 2 (by decide)]

lemma component_012121 :
    leftComponent C A S x y z w ii 0 1 2 1 2 1 =
    rightComponent C A S x y z w ii 0 1 2 1 2 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 1 2 1 2 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 1 2 1 2 1 (by decide)]

lemma component_012122 :
    leftComponent C A S x y z w ii 0 1 2 1 2 2 =
    rightComponent C A S x y z w ii 0 1 2 1 2 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 1 2 1 2 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 1 2 1 2 2 (by decide)]

lemma component_012200 :
    leftComponent C A S x y z w ii 0 1 2 2 0 0 =
    rightComponent C A S x y z w ii 0 1 2 2 0 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 1 2 2 0 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 1 2 2 0 0 (by decide)]

lemma component_012202 :
    leftComponent C A S x y z w ii 0 1 2 2 0 2 =
    rightComponent C A S x y z w ii 0 1 2 2 0 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 1 2 2 0 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 1 2 2 0 2 (by decide)]

lemma component_012210 :
    leftComponent C A S x y z w ii 0 1 2 2 1 0 =
    rightComponent C A S x y z w ii 0 1 2 2 1 0 := by
  simp only [leftComponent, rightComponent, Fin.sum_univ_three, numerator, Fin.val_zero, Fin.val_one, finThreeTwo, mul_zero, zero_mul, zero_add, add_zero]
  ; ring

lemma component_012211 :
    leftComponent C A S x y z w ii 0 1 2 2 1 1 =
    rightComponent C A S x y z w ii 0 1 2 2 1 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 1 2 2 1 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 1 2 2 1 1 (by decide)]

lemma component_012212 :
    leftComponent C A S x y z w ii 0 1 2 2 1 2 =
    rightComponent C A S x y z w ii 0 1 2 2 1 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 1 2 2 1 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 1 2 2 1 2 (by decide)]

lemma component_012220 :
    leftComponent C A S x y z w ii 0 1 2 2 2 0 =
    rightComponent C A S x y z w ii 0 1 2 2 2 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 1 2 2 2 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 1 2 2 2 0 (by decide)]

lemma component_012221 :
    leftComponent C A S x y z w ii 0 1 2 2 2 1 =
    rightComponent C A S x y z w ii 0 1 2 2 2 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 1 2 2 2 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 1 2 2 2 1 (by decide)]

lemma component_012222 :
    leftComponent C A S x y z w ii 0 1 2 2 2 2 =
    rightComponent C A S x y z w ii 0 1 2 2 2 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 1 2 2 2 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 1 2 2 2 2 (by decide)]

lemma component_020000 :
    leftComponent C A S x y z w ii 0 2 0 0 0 0 =
    rightComponent C A S x y z w ii 0 2 0 0 0 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 2 0 0 0 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 2 0 0 0 0 (by decide)]

lemma component_020001 :
    leftComponent C A S x y z w ii 0 2 0 0 0 1 =
    rightComponent C A S x y z w ii 0 2 0 0 0 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 2 0 0 0 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 2 0 0 0 1 (by decide)]

lemma component_020010 :
    leftComponent C A S x y z w ii 0 2 0 0 1 0 =
    rightComponent C A S x y z w ii 0 2 0 0 1 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 2 0 0 1 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 2 0 0 1 0 (by decide)]

lemma component_020012 :
    leftComponent C A S x y z w ii 0 2 0 0 1 2 =
    rightComponent C A S x y z w ii 0 2 0 0 1 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 2 0 0 1 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 2 0 0 1 2 (by decide)]

lemma component_020021 :
    leftComponent C A S x y z w ii 0 2 0 0 2 1 =
    rightComponent C A S x y z w ii 0 2 0 0 2 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 2 0 0 2 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 2 0 0 2 1 (by decide)]

lemma component_020022 :
    leftComponent C A S x y z w ii 0 2 0 0 2 2 =
    rightComponent C A S x y z w ii 0 2 0 0 2 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 2 0 0 2 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 2 0 0 2 2 (by decide)]

lemma component_020100 :
    leftComponent C A S x y z w ii 0 2 0 1 0 0 =
    rightComponent C A S x y z w ii 0 2 0 1 0 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 2 0 1 0 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 2 0 1 0 0 (by decide)]

lemma component_020102 :
    leftComponent C A S x y z w ii 0 2 0 1 0 2 =
    rightComponent C A S x y z w ii 0 2 0 1 0 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 2 0 1 0 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 2 0 1 0 2 (by decide)]

lemma component_020111 :
    leftComponent C A S x y z w ii 0 2 0 1 1 1 =
    rightComponent C A S x y z w ii 0 2 0 1 1 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 2 0 1 1 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 2 0 1 1 1 (by decide)]

lemma component_020112 :
    leftComponent C A S x y z w ii 0 2 0 1 1 2 =
    rightComponent C A S x y z w ii 0 2 0 1 1 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 2 0 1 1 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 2 0 1 1 2 (by decide)]

lemma component_020120 :
    leftComponent C A S x y z w ii 0 2 0 1 2 0 =
    rightComponent C A S x y z w ii 0 2 0 1 2 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 2 0 1 2 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 2 0 1 2 0 (by decide)]

lemma component_020121 :
    leftComponent C A S x y z w ii 0 2 0 1 2 1 =
    rightComponent C A S x y z w ii 0 2 0 1 2 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 2 0 1 2 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 2 0 1 2 1 (by decide)]

lemma component_020122 :
    leftComponent C A S x y z w ii 0 2 0 1 2 2 =
    rightComponent C A S x y z w ii 0 2 0 1 2 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 2 0 1 2 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 2 0 1 2 2 (by decide)]

lemma component_020201 :
    leftComponent C A S x y z w ii 0 2 0 2 0 1 =
    rightComponent C A S x y z w ii 0 2 0 2 0 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 2 0 2 0 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 2 0 2 0 1 (by decide)]

lemma component_020202 :
    leftComponent C A S x y z w ii 0 2 0 2 0 2 =
    rightComponent C A S x y z w ii 0 2 0 2 0 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 2 0 2 0 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 2 0 2 0 2 (by decide)]

lemma component_020210 :
    leftComponent C A S x y z w ii 0 2 0 2 1 0 =
    rightComponent C A S x y z w ii 0 2 0 2 1 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 2 0 2 1 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 2 0 2 1 0 (by decide)]

lemma component_020211 :
    leftComponent C A S x y z w ii 0 2 0 2 1 1 =
    rightComponent C A S x y z w ii 0 2 0 2 1 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 2 0 2 1 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 2 0 2 1 1 (by decide)]

lemma component_020212 :
    leftComponent C A S x y z w ii 0 2 0 2 1 2 =
    rightComponent C A S x y z w ii 0 2 0 2 1 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 2 0 2 1 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 2 0 2 1 2 (by decide)]

lemma component_020220 :
    leftComponent C A S x y z w ii 0 2 0 2 2 0 =
    rightComponent C A S x y z w ii 0 2 0 2 2 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 2 0 2 2 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 2 0 2 2 0 (by decide)]

lemma component_020221 :
    leftComponent C A S x y z w ii 0 2 0 2 2 1 =
    rightComponent C A S x y z w ii 0 2 0 2 2 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 2 0 2 2 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 2 0 2 2 1 (by decide)]

lemma component_020222 :
    leftComponent C A S x y z w ii 0 2 0 2 2 2 =
    rightComponent C A S x y z w ii 0 2 0 2 2 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 2 0 2 2 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 2 0 2 2 2 (by decide)]

lemma component_021000 :
    leftComponent C A S x y z w ii 0 2 1 0 0 0 =
    rightComponent C A S x y z w ii 0 2 1 0 0 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 2 1 0 0 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 2 1 0 0 0 (by decide)]

lemma component_021001 :
    leftComponent C A S x y z w ii 0 2 1 0 0 1 =
    rightComponent C A S x y z w ii 0 2 1 0 0 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 2 1 0 0 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 2 1 0 0 1 (by decide)]

lemma component_021002 :
    leftComponent C A S x y z w ii 0 2 1 0 0 2 =
    rightComponent C A S x y z w ii 0 2 1 0 0 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 2 1 0 0 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 2 1 0 0 2 (by decide)]

lemma component_021010 :
    leftComponent C A S x y z w ii 0 2 1 0 1 0 =
    rightComponent C A S x y z w ii 0 2 1 0 1 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 2 1 0 1 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 2 1 0 1 0 (by decide)]

lemma component_021011 :
    leftComponent C A S x y z w ii 0 2 1 0 1 1 =
    rightComponent C A S x y z w ii 0 2 1 0 1 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 2 1 0 1 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 2 1 0 1 1 (by decide)]

lemma component_021020 :
    leftComponent C A S x y z w ii 0 2 1 0 2 0 =
    rightComponent C A S x y z w ii 0 2 1 0 2 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 2 1 0 2 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 2 1 0 2 0 (by decide)]

lemma component_021021 :
    leftComponent C A S x y z w ii 0 2 1 0 2 1 =
    rightComponent C A S x y z w ii 0 2 1 0 2 1 := by
  simp only [leftComponent, rightComponent, Fin.sum_univ_three, numerator, Fin.val_zero, Fin.val_one, finThreeTwo, mul_zero, zero_mul, zero_add, add_zero]
  ; ring

lemma component_021022 :
    leftComponent C A S x y z w ii 0 2 1 0 2 2 =
    rightComponent C A S x y z w ii 0 2 1 0 2 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 2 1 0 2 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 2 1 0 2 2 (by decide)]

lemma component_021100 :
    leftComponent C A S x y z w ii 0 2 1 1 0 0 =
    rightComponent C A S x y z w ii 0 2 1 1 0 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 2 1 1 0 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 2 1 1 0 0 (by decide)]

lemma component_021101 :
    leftComponent C A S x y z w ii 0 2 1 1 0 1 =
    rightComponent C A S x y z w ii 0 2 1 1 0 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 2 1 1 0 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 2 1 1 0 1 (by decide)]

lemma component_021110 :
    leftComponent C A S x y z w ii 0 2 1 1 1 0 =
    rightComponent C A S x y z w ii 0 2 1 1 1 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 2 1 1 1 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 2 1 1 1 0 (by decide)]

lemma component_021112 :
    leftComponent C A S x y z w ii 0 2 1 1 1 2 =
    rightComponent C A S x y z w ii 0 2 1 1 1 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 2 1 1 1 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 2 1 1 1 2 (by decide)]

lemma component_021121 :
    leftComponent C A S x y z w ii 0 2 1 1 2 1 =
    rightComponent C A S x y z w ii 0 2 1 1 2 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 2 1 1 2 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 2 1 1 2 1 (by decide)]

lemma component_021122 :
    leftComponent C A S x y z w ii 0 2 1 1 2 2 =
    rightComponent C A S x y z w ii 0 2 1 1 2 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 2 1 1 2 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 2 1 1 2 2 (by decide)]

lemma component_021200 :
    leftComponent C A S x y z w ii 0 2 1 2 0 0 =
    rightComponent C A S x y z w ii 0 2 1 2 0 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 2 1 2 0 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 2 1 2 0 0 (by decide)]

lemma component_021201 :
    leftComponent C A S x y z w ii 0 2 1 2 0 1 =
    rightComponent C A S x y z w ii 0 2 1 2 0 1 := by
  simp only [leftComponent, rightComponent, Fin.sum_univ_three, numerator, Fin.val_zero, Fin.val_one, finThreeTwo, mul_zero, zero_mul, zero_add, add_zero]
  ; ring

lemma component_021202 :
    leftComponent C A S x y z w ii 0 2 1 2 0 2 =
    rightComponent C A S x y z w ii 0 2 1 2 0 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 2 1 2 0 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 2 1 2 0 2 (by decide)]

lemma component_021211 :
    leftComponent C A S x y z w ii 0 2 1 2 1 1 =
    rightComponent C A S x y z w ii 0 2 1 2 1 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 2 1 2 1 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 2 1 2 1 1 (by decide)]

lemma component_021212 :
    leftComponent C A S x y z w ii 0 2 1 2 1 2 =
    rightComponent C A S x y z w ii 0 2 1 2 1 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 2 1 2 1 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 2 1 2 1 2 (by decide)]

lemma component_021220 :
    leftComponent C A S x y z w ii 0 2 1 2 2 0 =
    rightComponent C A S x y z w ii 0 2 1 2 2 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 2 1 2 2 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 2 1 2 2 0 (by decide)]

lemma component_021221 :
    leftComponent C A S x y z w ii 0 2 1 2 2 1 =
    rightComponent C A S x y z w ii 0 2 1 2 2 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 2 1 2 2 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 2 1 2 2 1 (by decide)]

lemma component_021222 :
    leftComponent C A S x y z w ii 0 2 1 2 2 2 =
    rightComponent C A S x y z w ii 0 2 1 2 2 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 2 1 2 2 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 2 1 2 2 2 (by decide)]

lemma component_022000 :
    leftComponent C A S x y z w ii 0 2 2 0 0 0 =
    rightComponent C A S x y z w ii 0 2 2 0 0 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 2 2 0 0 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 2 2 0 0 0 (by decide)]

lemma component_022001 :
    leftComponent C A S x y z w ii 0 2 2 0 0 1 =
    rightComponent C A S x y z w ii 0 2 2 0 0 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 2 2 0 0 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 2 2 0 0 1 (by decide)]

lemma component_022002 :
    leftComponent C A S x y z w ii 0 2 2 0 0 2 =
    rightComponent C A S x y z w ii 0 2 2 0 0 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 2 2 0 0 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 2 2 0 0 2 (by decide)]

lemma component_022010 :
    leftComponent C A S x y z w ii 0 2 2 0 1 0 =
    rightComponent C A S x y z w ii 0 2 2 0 1 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 2 2 0 1 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 2 2 0 1 0 (by decide)]

lemma component_022011 :
    leftComponent C A S x y z w ii 0 2 2 0 1 1 =
    rightComponent C A S x y z w ii 0 2 2 0 1 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 2 2 0 1 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 2 2 0 1 1 (by decide)]

lemma component_022012 :
    leftComponent C A S x y z w ii 0 2 2 0 1 2 =
    rightComponent C A S x y z w ii 0 2 2 0 1 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 2 2 0 1 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 2 2 0 1 2 (by decide)]

lemma component_022020 :
    leftComponent C A S x y z w ii 0 2 2 0 2 0 =
    rightComponent C A S x y z w ii 0 2 2 0 2 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 2 2 0 2 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 2 2 0 2 0 (by decide)]

lemma component_022021 :
    leftComponent C A S x y z w ii 0 2 2 0 2 1 =
    rightComponent C A S x y z w ii 0 2 2 0 2 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 2 2 0 2 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 2 2 0 2 1 (by decide)]

lemma component_022022 :
    leftComponent C A S x y z w ii 0 2 2 0 2 2 =
    rightComponent C A S x y z w ii 0 2 2 0 2 2 := by
  simp only [leftComponent, rightComponent, Fin.sum_univ_three, numerator, Fin.val_zero, Fin.val_one, finThreeTwo, mul_zero, zero_mul, zero_add, add_zero]
  ; ring

lemma component_022100 :
    leftComponent C A S x y z w ii 0 2 2 1 0 0 =
    rightComponent C A S x y z w ii 0 2 2 1 0 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 2 2 1 0 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 2 2 1 0 0 (by decide)]

lemma component_022101 :
    leftComponent C A S x y z w ii 0 2 2 1 0 1 =
    rightComponent C A S x y z w ii 0 2 2 1 0 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 2 2 1 0 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 2 2 1 0 1 (by decide)]

lemma component_022102 :
    leftComponent C A S x y z w ii 0 2 2 1 0 2 =
    rightComponent C A S x y z w ii 0 2 2 1 0 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 2 2 1 0 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 2 2 1 0 2 (by decide)]

lemma component_022110 :
    leftComponent C A S x y z w ii 0 2 2 1 1 0 =
    rightComponent C A S x y z w ii 0 2 2 1 1 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 2 2 1 1 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 2 2 1 1 0 (by decide)]

lemma component_022111 :
    leftComponent C A S x y z w ii 0 2 2 1 1 1 =
    rightComponent C A S x y z w ii 0 2 2 1 1 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 2 2 1 1 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 2 2 1 1 1 (by decide)]

lemma component_022120 :
    leftComponent C A S x y z w ii 0 2 2 1 2 0 =
    rightComponent C A S x y z w ii 0 2 2 1 2 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 2 2 1 2 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 2 2 1 2 0 (by decide)]

lemma component_022122 :
    leftComponent C A S x y z w ii 0 2 2 1 2 2 =
    rightComponent C A S x y z w ii 0 2 2 1 2 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 2 2 1 2 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 2 2 1 2 2 (by decide)]

lemma component_022200 :
    leftComponent C A S x y z w ii 0 2 2 2 0 0 =
    rightComponent C A S x y z w ii 0 2 2 2 0 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 2 2 2 0 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 2 2 2 0 0 (by decide)]

lemma component_022201 :
    leftComponent C A S x y z w ii 0 2 2 2 0 1 =
    rightComponent C A S x y z w ii 0 2 2 2 0 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 2 2 2 0 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 2 2 2 0 1 (by decide)]

lemma component_022210 :
    leftComponent C A S x y z w ii 0 2 2 2 1 0 =
    rightComponent C A S x y z w ii 0 2 2 2 1 0 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 2 2 2 1 0 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 2 2 2 1 0 (by decide)]

lemma component_022212 :
    leftComponent C A S x y z w ii 0 2 2 2 1 2 =
    rightComponent C A S x y z w ii 0 2 2 2 1 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 2 2 2 1 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 2 2 2 1 2 (by decide)]

lemma component_022221 :
    leftComponent C A S x y z w ii 0 2 2 2 2 1 =
    rightComponent C A S x y z w ii 0 2 2 2 2 1 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 2 2 2 2 1 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 2 2 2 2 1 (by decide)]

lemma component_022222 :
    leftComponent C A S x y z w ii 0 2 2 2 2 2 =
    rightComponent C A S x y z w ii 0 2 2 2 2 2 := by
  rw [leftComponent_eq_zero_of_sum_ne C A S x y z w ii 0 2 2 2 2 2 (by decide),
    rightComponent_eq_zero_of_sum_ne C A S x y z w ii 0 2 2 2 2 2 (by decide)]

lemma block_000 (d e f : Fin 3) :
    leftComponent C A S x y z w ii 0 0 0 d e f =
    rightComponent C A S x y z w ii 0 0 0 d e f := by
  fin_cases d <;> fin_cases e <;> fin_cases f
  · exact component_000000 C A S x y z w ii
  · exact component_000001 C A S x y z w ii
  · exact component_000002 C A S x y z w ii
  · exact component_000010 C A S x y z w ii
  · exact component_000011 C A S x y z w ii
  · exact component_000012 C A S x y z w ii
  · exact component_000020 C A S x y z w ii
  · exact component_000021 C A S x y z w ii
  · exact component_000022 C A S x y z w ii
  · exact component_000100 C A S x y z w ii
  · exact component_000101 C A S x y z w ii
  · exact component_000102 C A S x y z w ii
  · exact component_000110 C A S x y z w ii
  · exact component_000111 C A S x y z w ii
  · exact component_000112 C A S x y z w ii
  · exact component_000120 C A S x y z w ii
  · exact component_000121 C A S x y z w ii
  · exact component_000122 C A S x y z w ii
  · exact component_000200 C A S x y z w ii
  · exact component_000201 C A S x y z w ii
  · exact component_000202 C A S x y z w ii
  · exact component_000210 C A S x y z w ii
  · exact component_000211 C A S x y z w ii
  · exact component_000212 C A S x y z w ii
  · exact component_000220 C A S x y z w ii
  · exact component_000221 C A S x y z w ii
  · exact component_000222 C A S x y z w ii

include hC hA hS hy hw in
lemma block_001 (d e f : Fin 3) :
    leftComponent C A S x y z w ii 0 0 1 d e f =
    rightComponent C A S x y z w ii 0 0 1 d e f := by
  fin_cases d <;> fin_cases e <;> fin_cases f
  · exact component_001000 C A S x y z w ii
  · exact component_001001 C A S x y z w ii
  · exact component_001002 C A S x y z w ii
  · exact component_001010 C A S x y z w ii hy
  · exact component_001011 C A S x y z w ii
  · exact component_001012 C A S x y z w ii
  · exact component_001020 C A S x y z w ii
  · exact component_001021 C A S x y z w ii
  · exact component_001022 C A S x y z w ii
  · exact component_001100 C A S x y z w ii hC hA hS hy hw
  · exact component_001101 C A S x y z w ii
  · exact component_001102 C A S x y z w ii
  · exact component_001110 C A S x y z w ii
  · exact component_001111 C A S x y z w ii
  · exact component_001112 C A S x y z w ii
  · exact component_001120 C A S x y z w ii
  · exact component_001121 C A S x y z w ii
  · exact component_001122 C A S x y z w ii
  · exact component_001200 C A S x y z w ii
  · exact component_001201 C A S x y z w ii
  · exact component_001202 C A S x y z w ii
  · exact component_001210 C A S x y z w ii
  · exact component_001211 C A S x y z w ii
  · exact component_001212 C A S x y z w ii
  · exact component_001220 C A S x y z w ii
  · exact component_001221 C A S x y z w ii
  · exact component_001222 C A S x y z w ii

include hC hA hS hy hw hi in
lemma block_002 (d e f : Fin 3) :
    leftComponent C A S x y z w ii 0 0 2 d e f =
    rightComponent C A S x y z w ii 0 0 2 d e f := by
  fin_cases d <;> fin_cases e <;> fin_cases f
  · exact component_002000 C A S x y z w ii
  · exact component_002001 C A S x y z w ii
  · exact component_002002 C A S x y z w ii
  · exact component_002010 C A S x y z w ii
  · exact component_002011 C A S x y z w ii hC hA hS hy hw
  · exact component_002012 C A S x y z w ii
  · exact component_002020 C A S x y z w ii hC hA hS hy hw hi
  · exact component_002021 C A S x y z w ii
  · exact component_002022 C A S x y z w ii
  · exact component_002100 C A S x y z w ii
  · exact component_002101 C A S x y z w ii hC hA hS hy hw
  · exact component_002102 C A S x y z w ii
  · exact component_002110 C A S x y z w ii hC hA hS hy hw hi
  · exact component_002111 C A S x y z w ii
  · exact component_002112 C A S x y z w ii
  · exact component_002120 C A S x y z w ii
  · exact component_002121 C A S x y z w ii
  · exact component_002122 C A S x y z w ii
  · exact component_002200 C A S x y z w ii hC hA hS hy hw hi
  · exact component_002201 C A S x y z w ii
  · exact component_002202 C A S x y z w ii
  · exact component_002210 C A S x y z w ii
  · exact component_002211 C A S x y z w ii
  · exact component_002212 C A S x y z w ii
  · exact component_002220 C A S x y z w ii
  · exact component_002221 C A S x y z w ii
  · exact component_002222 C A S x y z w ii

include hy in
lemma block_010 (d e f : Fin 3) :
    leftComponent C A S x y z w ii 0 1 0 d e f =
    rightComponent C A S x y z w ii 0 1 0 d e f := by
  fin_cases d <;> fin_cases e <;> fin_cases f
  · exact component_010000 C A S x y z w ii
  · exact component_010001 C A S x y z w ii hy
  · exact component_010002 C A S x y z w ii
  · exact component_010010 C A S x y z w ii
  · exact component_010011 C A S x y z w ii
  · exact component_010012 C A S x y z w ii
  · exact component_010020 C A S x y z w ii
  · exact component_010021 C A S x y z w ii
  · exact component_010022 C A S x y z w ii
  · exact component_010100 C A S x y z w ii
  · exact component_010101 C A S x y z w ii
  · exact component_010102 C A S x y z w ii
  · exact component_010110 C A S x y z w ii
  · exact component_010111 C A S x y z w ii
  · exact component_010112 C A S x y z w ii
  · exact component_010120 C A S x y z w ii
  · exact component_010121 C A S x y z w ii
  · exact component_010122 C A S x y z w ii
  · exact component_010200 C A S x y z w ii
  · exact component_010201 C A S x y z w ii
  · exact component_010202 C A S x y z w ii
  · exact component_010210 C A S x y z w ii
  · exact component_010211 C A S x y z w ii
  · exact component_010212 C A S x y z w ii
  · exact component_010220 C A S x y z w ii
  · exact component_010221 C A S x y z w ii
  · exact component_010222 C A S x y z w ii

include hC hA hS hy hw hi in
lemma block_011 (d e f : Fin 3) :
    leftComponent C A S x y z w ii 0 1 1 d e f =
    rightComponent C A S x y z w ii 0 1 1 d e f := by
  fin_cases d <;> fin_cases e <;> fin_cases f
  · exact component_011000 C A S x y z w ii
  · exact component_011001 C A S x y z w ii
  · exact component_011002 C A S x y z w ii hC hA hS hy hw
  · exact component_011010 C A S x y z w ii
  · exact component_011011 C A S x y z w ii
  · exact component_011012 C A S x y z w ii
  · exact component_011020 C A S x y z w ii hC hA hS hy hw hi
  · exact component_011021 C A S x y z w ii
  · exact component_011022 C A S x y z w ii
  · exact component_011100 C A S x y z w ii
  · exact component_011101 C A S x y z w ii hC hA hS hy hw hi
  · exact component_011102 C A S x y z w ii
  · exact component_011110 C A S x y z w ii hC hA hS hy hw hi
  · exact component_011111 C A S x y z w ii
  · exact component_011112 C A S x y z w ii
  · exact component_011120 C A S x y z w ii
  · exact component_011121 C A S x y z w ii
  · exact component_011122 C A S x y z w ii
  · exact component_011200 C A S x y z w ii hC hA hS hy hw hi
  · exact component_011201 C A S x y z w ii
  · exact component_011202 C A S x y z w ii
  · exact component_011210 C A S x y z w ii
  · exact component_011211 C A S x y z w ii
  · exact component_011212 C A S x y z w ii
  · exact component_011220 C A S x y z w ii
  · exact component_011221 C A S x y z w ii
  · exact component_011222 C A S x y z w ii

include hC hA hS hy hw hi in
lemma block_012 (d e f : Fin 3) :
    leftComponent C A S x y z w ii 0 1 2 d e f =
    rightComponent C A S x y z w ii 0 1 2 d e f := by
  fin_cases d <;> fin_cases e <;> fin_cases f
  · exact component_012000 C A S x y z w ii
  · exact component_012001 C A S x y z w ii
  · exact component_012002 C A S x y z w ii
  · exact component_012010 C A S x y z w ii
  · exact component_012011 C A S x y z w ii
  · exact component_012012 C A S x y z w ii
  · exact component_012020 C A S x y z w ii
  · exact component_012021 C A S x y z w ii hC hA hS hy hw hi
  · exact component_012022 C A S x y z w ii
  · exact component_012100 C A S x y z w ii
  · exact component_012101 C A S x y z w ii
  · exact component_012102 C A S x y z w ii hC hA hS hy hw hi
  · exact component_012110 C A S x y z w ii
  · exact component_012111 C A S x y z w ii hC hA hS hy hw
  · exact component_012112 C A S x y z w ii
  · exact component_012120 C A S x y z w ii hC hA hS hy hw hi
  · exact component_012121 C A S x y z w ii
  · exact component_012122 C A S x y z w ii
  · exact component_012200 C A S x y z w ii
  · exact component_012201 C A S x y z w ii hC hA hS hy hw hi
  · exact component_012202 C A S x y z w ii
  · exact component_012210 C A S x y z w ii
  · exact component_012211 C A S x y z w ii
  · exact component_012212 C A S x y z w ii
  · exact component_012220 C A S x y z w ii
  · exact component_012221 C A S x y z w ii
  · exact component_012222 C A S x y z w ii

include hC hA hS hy hw hi in
lemma block_020 (d e f : Fin 3) :
    leftComponent C A S x y z w ii 0 2 0 d e f =
    rightComponent C A S x y z w ii 0 2 0 d e f := by
  fin_cases d <;> fin_cases e <;> fin_cases f
  · exact component_020000 C A S x y z w ii
  · exact component_020001 C A S x y z w ii
  · exact component_020002 C A S x y z w ii hC hA hS hy hw hi
  · exact component_020010 C A S x y z w ii
  · exact component_020011 C A S x y z w ii hC hA hS hy hw hi
  · exact component_020012 C A S x y z w ii
  · exact component_020020 C A S x y z w ii hC hA hS hy hw hi
  · exact component_020021 C A S x y z w ii
  · exact component_020022 C A S x y z w ii
  · exact component_020100 C A S x y z w ii
  · exact component_020101 C A S x y z w ii hC hA hS hy hw hi
  · exact component_020102 C A S x y z w ii
  · exact component_020110 C A S x y z w ii hC hA hS hy hw hi
  · exact component_020111 C A S x y z w ii
  · exact component_020112 C A S x y z w ii
  · exact component_020120 C A S x y z w ii
  · exact component_020121 C A S x y z w ii
  · exact component_020122 C A S x y z w ii
  · exact component_020200 C A S x y z w ii hC hA hS hy hw hi
  · exact component_020201 C A S x y z w ii
  · exact component_020202 C A S x y z w ii
  · exact component_020210 C A S x y z w ii
  · exact component_020211 C A S x y z w ii
  · exact component_020212 C A S x y z w ii
  · exact component_020220 C A S x y z w ii
  · exact component_020221 C A S x y z w ii
  · exact component_020222 C A S x y z w ii

include hC hA hS hy hw hi in
lemma block_021 (d e f : Fin 3) :
    leftComponent C A S x y z w ii 0 2 1 d e f =
    rightComponent C A S x y z w ii 0 2 1 d e f := by
  fin_cases d <;> fin_cases e <;> fin_cases f
  · exact component_021000 C A S x y z w ii
  · exact component_021001 C A S x y z w ii
  · exact component_021002 C A S x y z w ii
  · exact component_021010 C A S x y z w ii
  · exact component_021011 C A S x y z w ii
  · exact component_021012 C A S x y z w ii hC hA hS hy hw hi
  · exact component_021020 C A S x y z w ii
  · exact component_021021 C A S x y z w ii
  · exact component_021022 C A S x y z w ii
  · exact component_021100 C A S x y z w ii
  · exact component_021101 C A S x y z w ii
  · exact component_021102 C A S x y z w ii hC hA hS hy hw hi
  · exact component_021110 C A S x y z w ii
  · exact component_021111 C A S x y z w ii hC hA hS hy hw hi
  · exact component_021112 C A S x y z w ii
  · exact component_021120 C A S x y z w ii hC hA hS hy hw hi
  · exact component_021121 C A S x y z w ii
  · exact component_021122 C A S x y z w ii
  · exact component_021200 C A S x y z w ii
  · exact component_021201 C A S x y z w ii
  · exact component_021202 C A S x y z w ii
  · exact component_021210 C A S x y z w ii hC hA hS hy hw hi
  · exact component_021211 C A S x y z w ii
  · exact component_021212 C A S x y z w ii
  · exact component_021220 C A S x y z w ii
  · exact component_021221 C A S x y z w ii
  · exact component_021222 C A S x y z w ii

include hC hA hS hy hw hi in
lemma block_022 (d e f : Fin 3) :
    leftComponent C A S x y z w ii 0 2 2 d e f =
    rightComponent C A S x y z w ii 0 2 2 d e f := by
  fin_cases d <;> fin_cases e <;> fin_cases f
  · exact component_022000 C A S x y z w ii
  · exact component_022001 C A S x y z w ii
  · exact component_022002 C A S x y z w ii
  · exact component_022010 C A S x y z w ii
  · exact component_022011 C A S x y z w ii
  · exact component_022012 C A S x y z w ii
  · exact component_022020 C A S x y z w ii
  · exact component_022021 C A S x y z w ii
  · exact component_022022 C A S x y z w ii
  · exact component_022100 C A S x y z w ii
  · exact component_022101 C A S x y z w ii
  · exact component_022102 C A S x y z w ii
  · exact component_022110 C A S x y z w ii
  · exact component_022111 C A S x y z w ii
  · exact component_022112 C A S x y z w ii hC hA hS hy hw
  · exact component_022120 C A S x y z w ii
  · exact component_022121 C A S x y z w ii hC hA hS hy hw
  · exact component_022122 C A S x y z w ii
  · exact component_022200 C A S x y z w ii
  · exact component_022201 C A S x y z w ii
  · exact component_022202 C A S x y z w ii hC hA hS hy hw hi
  · exact component_022210 C A S x y z w ii
  · exact component_022211 C A S x y z w ii hC hA hS hy hw hi
  · exact component_022212 C A S x y z w ii
  · exact component_022220 C A S x y z w ii hC hA hS hy hw hi
  · exact component_022221 C A S x y z w ii
  · exact component_022222 C A S x y z w ii

end Algebra
end CriticalHoneycomb.Transfer.YangBaxter

end OAI
