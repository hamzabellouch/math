import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.PrimeWindow
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.E
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.PrimeLogReciprocalBound

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory intervalIntegral
open Finset
open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open Filter
open MeasureTheory Filter
open MeasureTheory
open MeasureTheory Set
open Set MeasureTheory Complex
open Set
open Finset Filter
open ArithmeticFunction
open MeasureTheory Finset

namespace OrdinaryMinorArcNumerics
open OrdinaryNarrowGrid OrdinaryChainScales OrdinaryPrimeSupply Finset Filter
lemma block_diagonal_bound (P : Finset ℕ) (i : ℕ×ℕ) (hi : i.2=1)
    (hL : 1 ≤ ∑p∈P,(p:ℝ)⁻¹) :
    Real.sqrt (((lower i:ℝ)⁻¹*(4/(∑p∈P,(p:ℝ)⁻¹)^2+4/(∑p∈P,(p:ℝ)⁻¹)))*
      ((lower i:ℝ)⁻¹*(primeBin i).card)) ≤ 3*(3/4:ℝ)^i.1 := by
  let L : ℝ := ∑p∈P,(p:ℝ)⁻¹
  have hLp : 0 < L := lt_of_lt_of_le (by norm_num) hL
  have hC : 4/L^2+4/L ≤ 8 := by
    have h1 : 1 ≤ L^2 := by nlinarith only [hL]
    have h2 := (div_le_iff₀ (sq_pos_of_pos hLp)).mpr (show (4:ℝ) ≤ 4*L^2 by linarith)
    have h3 := (div_le_iff₀ hLp).mpr (show (4:ℝ) ≤ 4*L by linarith)
    linarith only [h2,h3]
  have hA : lower i=2^i.1 := by simp [lower,hi]
  have hc : (primeBin i).card ≤ lower i := by
    have hh := Finset.card_le_card (filter_subset Nat.Prime (Ioc (lower i) (upper i)))
    have he : upper i=2^i.1+2^i.1 := by simp only [upper,hi]; ring
    simpa only [primeBin,Nat.card_Ioc,he,hA,Nat.add_sub_cancel_left] using hh
  have hAr : (0:ℝ) < lower i := by rw [hA]; positivity
  have hb : (lower i:ℝ)⁻¹*(primeBin i).card ≤ 1 := by
    rw [← div_eq_inv_mul]
    exact (div_le_one hAr).mpr (by exact_mod_cast hc)
  have hh : ((lower i:ℝ)⁻¹*(4/L^2+4/L))*((lower i:ℝ)⁻¹*(primeBin i).card) ≤
      8*(2:ℝ)⁻¹^i.1 := by
    calc
      _ ≤ ((lower i:ℝ)⁻¹*8)*1 := mul_le_mul
        (mul_le_mul_of_nonneg_left hC (by positivity)) hb (by positivity) (by positivity)
      _ = _ := by rw [hA]; push_cast; rw [inv_pow]; ring
  have hg : (2:ℝ)⁻¹^i.1 ≤ ((3/4:ℝ)^i.1)^2 := by
    rw [← pow_mul, mul_comm i.1 2,pow_mul]
    exact pow_le_pow_left₀ (by norm_num) (by norm_num : (2:ℝ)⁻¹ ≤ (3/4:ℝ)^2) _
  apply (Real.sqrt_le_iff).mpr
  constructor
  · positivity
  · change ((lower i:ℝ)⁻¹*(4/L^2+4/L))*((lower i:ℝ)⁻¹*(primeBin i).card) ≤ _
    have hp : 0 ≤ ((3/4:ℝ)^i.1)^2 := sq_nonneg _
    nlinarith only [hh,hg,hp]

lemma grid_one_diagonal_bound (P : Finset ℕ) (r R : ℕ)
    (hL : 1 ≤ ∑p∈P,(p:ℝ)⁻¹) :
    (∑i∈grid 1 r R,
      Real.sqrt (((lower i:ℝ)⁻¹*(4/(∑p∈P,(p:ℝ)⁻¹)^2+4/(∑p∈P,(p:ℝ)⁻¹)))*
        ((lower i:ℝ)⁻¹*(primeBin i).card))) ≤ 12*(3/4:ℝ)^r := by
  have hsum : (∑i∈grid 1 r R,(3:ℝ)*(3/4:ℝ)^i.1)=
      ∑j∈Ico r (r+R),(3:ℝ)*(3/4:ℝ)^j := by
    simp [grid]
  calc
    _ ≤ ∑i∈grid 1 r R,(3:ℝ)*(3/4:ℝ)^i.1 := by
      apply sum_le_sum
      intro i hi
      have hi2 := (mem_Ico.mp (mem_product.mp hi).2)
      exact block_diagonal_bound P i (by omega) hL
    _ = _ := hsum
    _ = (3/4:ℝ)^r*(3*∑j∈range R,(3/4:ℝ)^j) := by
      rw [sum_Ico_eq_sum_range,Nat.add_sub_cancel_left]
      simp_rw [pow_add]
      rw [mul_sum,mul_sum]
      apply sum_congr rfl
      intro j hj
      ring
    _ ≤ (3/4:ℝ)^r*(3*4) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      rw [geom_sum_eq (by norm_num : (3/4:ℝ)≠1) R]
      have hp := pow_nonneg (by norm_num : (0:ℝ)≤3/4) R
      have he : ((3/4:ℝ)^R-1)/(3/4-1)=4-4*(3/4:ℝ)^R := by ring
      rw [he]
      linarith only [hp]
    _ = _ := by ring

end OrdinaryMinorArcNumerics

end

end OAI
