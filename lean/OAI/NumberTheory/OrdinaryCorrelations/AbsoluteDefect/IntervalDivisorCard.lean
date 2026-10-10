import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.NatDivRealError

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
open MeasureTheory
open MeasureTheory Complex
open Finset Filter

namespace OrdinarySelbergWeights
open Finset

lemma interval_divisor_card (L U d : ℕ) (hLU : L ≤ U) :
    (((Ioc L U).filter (fun n => d∣n)).card:ℝ) =
      ((U/d:ℕ):ℝ)-((L/d:ℕ):ℝ) := by
  have hdj : Disjoint (Ioc 0 L) (Ioc L U) := Ioc_disjoint_Ioc.mpr (by simp)
  have hc : ((Ioc 0 L).filter (fun n => d∣n)).card +
      ((Ioc L U).filter (fun n => d∣n)).card = ((Ioc 0 U).filter (fun n => d∣n)).card := by
    rw [← card_union_of_disjoint (disjoint_filter_filter hdj), ← filter_union,
      Ioc_union_Ioc_eq_Ioc (Nat.zero_le L) hLU]
  rw [Nat.Ioc_filter_dvd_card_eq_div, Nat.Ioc_filter_dvd_card_eq_div] at hc
  have hr : ((L/d:ℕ):ℝ) + (((Ioc L U).filter (fun n => d∣n)).card:ℝ) = ((U/d:ℕ):ℝ) := by
    exact_mod_cast hc
  linarith

lemma nat_interval_div_real_error (L U d : ℕ) (hd : 0 < d) :
    |(((U/d:ℕ):ℝ)-((L/d:ℕ):ℝ)) - ((U:ℝ)-(L:ℝ))/(d:ℝ)| ≤ 2 := by
  have hu := nat_div_real_error U d hd
  have hl := nat_div_real_error L d hd
  have he : (((U/d:ℕ):ℝ)-((L/d:ℕ):ℝ)) - ((U:ℝ)-(L:ℝ))/(d:ℝ) =
      (((U/d:ℕ):ℝ)-(U:ℝ)/(d:ℝ)) - (((L/d:ℕ):ℝ)-(L:ℝ)/(d:ℝ)) := by ring
  rw [he]
  exact (abs_sub _ _).trans (by linarith)

lemma sieveWeight_sum_interval (P z L U : ℕ) (hP : Squarefree P) (hLU : L ≤ U) :
    (∑ n ∈ Ioc L U, sieveWeight P z hP n) =
      ∑ d ∈ P.divisors, ∑ e ∈ P.divisors,
        actualWeights P z hP d * actualWeights P z hP e *
          (((U/Nat.lcm d e:ℕ):ℝ)-((L/Nat.lcm d e:ℕ):ℝ)) := by
  simp_rw [sieveWeight_expansion]
  rw [sum_comm]
  apply sum_congr rfl
  intro d hd
  rw [sum_comm]
  apply sum_congr rfl
  intro e he
  rw [← sum_filter, sum_const, nsmul_eq_mul, interval_divisor_card L U _ hLU]
  ring

theorem rough_interval_count (P z L U : ℕ) (hP : Squarefree P) (hz : 1 ≤ z)
    (hLU : L ≤ U) :
    (((Ioc L U).filter (fun n => n.Coprime P)).card:ℝ) ≤
      ((U:ℝ)-(L:ℝ))*(actualMass P z hP)⁻¹ + 2*(z:ℝ)^4 := by
  have hs : (((Ioc L U).filter (fun n => n.Coprime P)).card:ℝ) ≤
      ∑ n ∈ Ioc L U, sieveWeight P z hP n := by
    calc
      _ = ∑ n ∈ Ioc L U, if n.Coprime P then (1:ℝ) else 0 := by simp
      _ ≤ _ := sum_le_sum (fun n hn => rough_indicator_le hP hz)
  rw [sieveWeight_sum_interval P z L U hP hLU] at hs
  apply hs.trans
  calc
    _ ≤ ∑ d ∈ P.divisors, ∑ e ∈ P.divisors,
        (((U:ℝ)-(L:ℝ)) * (actualWeights P z hP d * actualWeights P z hP e / (Nat.lcm d e:ℝ)) +
          2*|actualWeights P z hP d| * |actualWeights P z hP e|) := by
      apply sum_le_sum
      intro d hd
      apply sum_le_sum
      intro e he
      have hl : 0 < Nat.lcm d e := Nat.lcm_pos (Nat.pos_of_mem_divisors hd) (Nat.pos_of_mem_divisors he)
      have hh := nat_interval_div_real_error L U (Nat.lcm d e) hl
      have hb : actualWeights P z hP d * actualWeights P z hP e *
          ((((U/Nat.lcm d e:ℕ):ℝ)-((L/Nat.lcm d e:ℕ):ℝ)) -
            ((U:ℝ)-(L:ℝ))/(Nat.lcm d e:ℝ)) ≤
          2*|actualWeights P z hP d| * |actualWeights P z hP e| := by
        calc
          _ ≤ |actualWeights P z hP d * actualWeights P z hP e *
              ((((U/Nat.lcm d e:ℕ):ℝ)-((L/Nat.lcm d e:ℕ):ℝ)) -
                ((U:ℝ)-(L:ℝ))/(Nat.lcm d e:ℝ))| := le_abs_self _
          _ = |actualWeights P z hP d| * |actualWeights P z hP e| *
              |(((U/Nat.lcm d e:ℕ):ℝ)-((L/Nat.lcm d e:ℕ):ℝ)) -
                ((U:ℝ)-(L:ℝ))/(Nat.lcm d e:ℝ)| := by rw [abs_mul, abs_mul]
          _ ≤ |actualWeights P z hP d| * |actualWeights P z hP e| * 2 :=
            mul_le_mul_of_nonneg_left hh (mul_nonneg (abs_nonneg _) (abs_nonneg _))
          _ = _ := by ring
      simp only [div_eq_mul_inv] at hb ⊢
      nlinarith
    _ = ((U:ℝ)-(L:ℝ))*(actualMass P z hP)⁻¹ + 2*(∑ d ∈ P.divisors, |actualWeights P z hP d|)^2 := by
      simp only [sum_add_distrib]
      simp_rw [← mul_sum]
      rw [actualWeights_diagonal hP hz]
      rw [pow_two, sum_mul_sum]
      simp only [mul_sum]
      ring_nf
    _ ≤ _ := by
      have hb := actualWeights_l1 hP hz
      have h0 : 0 ≤ ∑ d ∈ P.divisors, |actualWeights P z hP d| := sum_nonneg (fun _ _ => abs_nonneg _)
      nlinarith [sq_nonneg ((z:ℝ)^2 - ∑ d ∈ P.divisors, |actualWeights P z hP d|)]

end OrdinarySelbergWeights

end

end OAI
