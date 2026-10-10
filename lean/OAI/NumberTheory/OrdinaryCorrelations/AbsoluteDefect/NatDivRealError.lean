import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.Reciprocal

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

namespace OrdinarySelbergWeights
open Finset

lemma nat_div_real_error (N d : ℕ) (hd : 0 < d) :
    |((N/d:ℕ):ℝ) - (N:ℝ)/(d:ℝ)| ≤ 1 := by
  have hd' : (0:ℝ) < d := by exact_mod_cast hd
  have he : (d:ℝ)*(N/d:ℕ)+(N%d:ℕ) = N := by exact_mod_cast Nat.div_add_mod N d
  have hr : ((N%d:ℕ):ℝ) < d := by exact_mod_cast Nat.mod_lt N hd
  have hr0 : (0:ℝ) ≤ (N%d:ℕ) := Nat.cast_nonneg _
  apply abs_le.mpr
  constructor
  · have hh : (N:ℝ)/(d:ℝ) ≤ ((N/d:ℕ):ℝ)+1 :=
      (div_le_iff₀ hd').mpr (by nlinarith)
    linarith
  · have hh : ((N/d:ℕ):ℝ) ≤ (N:ℝ)/(d:ℝ) := (le_div_iff₀ hd').mpr (by nlinarith)
    linarith

lemma sieveWeight_sum (P z N : ℕ) (hP : Squarefree P) :
    (∑ n ∈ Icc 1 N, sieveWeight P z hP n) =
      ∑ d ∈ P.divisors, ∑ e ∈ P.divisors,
        actualWeights P z hP d * actualWeights P z hP e * ((N/Nat.lcm d e:ℕ):ℝ) := by
  simp_rw [sieveWeight_expansion]
  rw [sum_comm]
  apply sum_congr rfl
  intro d hd
  rw [sum_comm]
  apply sum_congr rfl
  intro e he
  rw [← sum_filter, sum_const, nsmul_eq_mul]
  have hI : Finset.Icc 1 N = Finset.Ioc 0 N := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_Ioc]
    omega
  rw [hI, Nat.Ioc_filter_dvd_card_eq_div]
  ring

theorem rough_count_bound (P z N : ℕ) (hP : Squarefree P) (hz : 1 ≤ z) :
    ((Finset.Icc 1 N).filter (fun n => n.Coprime P)).card ≤
      (N:ℝ)*(actualMass P z hP)⁻¹ + (z:ℝ)^4 := by
  have hs : (((Finset.Icc 1 N).filter (fun n => n.Coprime P)).card:ℝ) ≤
      ∑ n ∈ Icc 1 N, sieveWeight P z hP n := by
    calc
      _ = ∑ n ∈ Icc 1 N, if n.Coprime P then (1:ℝ) else 0 := by simp
      _ ≤ _ := sum_le_sum (fun n hn => rough_indicator_le hP hz)
  rw [sieveWeight_sum] at hs
  apply hs.trans
  calc
    _ ≤ ∑ d ∈ P.divisors, ∑ e ∈ P.divisors,
        ((N:ℝ) * (actualWeights P z hP d * actualWeights P z hP e / (Nat.lcm d e:ℝ)) +
          |actualWeights P z hP d| * |actualWeights P z hP e|) := by
      apply sum_le_sum
      intro d hd
      apply sum_le_sum
      intro e he
      have hl : 0 < Nat.lcm d e := Nat.lcm_pos (Nat.pos_of_mem_divisors hd) (Nat.pos_of_mem_divisors he)
      have hh := nat_div_real_error N (Nat.lcm d e) hl
      have hb : actualWeights P z hP d * actualWeights P z hP e *
          (((N/Nat.lcm d e:ℕ):ℝ) - (N:ℝ)/(Nat.lcm d e:ℝ)) ≤
          |actualWeights P z hP d| * |actualWeights P z hP e| := by
        calc
          _ ≤ |actualWeights P z hP d * actualWeights P z hP e *
              (((N/Nat.lcm d e:ℕ):ℝ) - (N:ℝ)/(Nat.lcm d e:ℝ))| := le_abs_self _
          _ = |actualWeights P z hP d| * |actualWeights P z hP e| *
              |((N/Nat.lcm d e:ℕ):ℝ) - (N:ℝ)/(Nat.lcm d e:ℝ)| := by rw [abs_mul, abs_mul]
          _ ≤ _ := by
            simpa only [mul_one] using mul_le_mul_of_nonneg_left hh
              (mul_nonneg (abs_nonneg (actualWeights P z hP d)) (abs_nonneg (actualWeights P z hP e)))
      simp only [div_eq_mul_inv] at hb ⊢
      nlinarith
    _ = (N:ℝ)*(actualMass P z hP)⁻¹ + (∑ d ∈ P.divisors, |actualWeights P z hP d|)^2 := by
      simp only [sum_add_distrib]
      rw [← sum_mul_sum]
      simp_rw [← mul_sum]
      rw [actualWeights_diagonal hP hz]
      ring
    _ ≤ _ := by
      have hb := actualWeights_l1 hP hz
      have h0 : 0 ≤ ∑ d ∈ P.divisors, |actualWeights P z hP d| := sum_nonneg (fun _ _ => abs_nonneg _)
      nlinarith [sq_nonneg ((z:ℝ)^2 - ∑ d ∈ P.divisors, |actualWeights P z hP d|)]

end OrdinarySelbergWeights

end

end OAI
