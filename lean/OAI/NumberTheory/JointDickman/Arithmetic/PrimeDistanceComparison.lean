import OAI.NumberTheory.JointDickman.Analysis.CharacterDistanceInput
import OAI.NumberTheory.JointDickman.Arithmetic.PrimeIntervalSums

namespace OAI

/-! # Changes of prime values in the squared pretentious distance -/
namespace JointDickman
open Finset Filter Classical PublishedInputs
open scoped Topology

theorem primeDistance_phase_norm (p : ℕ) (t : ℝ) :
    ‖Complex.exp (-((t*Real.log (p : ℝ) : ℝ) : ℂ)*Complex.I)‖ = 1 := by
  simp only [Complex.norm_exp,Complex.mul_re,Complex.neg_re,Complex.ofReal_re,
    Complex.neg_im,Complex.ofReal_im,Complex.I_re,Complex.I_im,mul_zero,zero_mul,
    sub_self,neg_zero,Real.exp_zero]

theorem primeDistance_term_sub_le (f g : ArithmeticFunction ℂ)
    (hf : ∀ n, ‖f n‖ ≤ 1) (hg : ∀ n, ‖g n‖ ≤ 1) (p : ℕ) (t : ℝ) :
    (1-(g p*Complex.exp (-((t*Real.log (p : ℝ) : ℝ) : ℂ)*Complex.I)).re)/(p : ℝ)-
      (1-(f p*Complex.exp (-((t*Real.log (p : ℝ) : ℝ) : ℂ)*Complex.I)).re)/(p : ℝ) ≤
        2/(p : ℝ) := by
  let e := Complex.exp (-((t*Real.log (p : ℝ) : ℝ) : ℂ)*Complex.I)
  have he : ‖e‖ = 1 := primeDistance_phase_norm p t
  have hfn : ‖f p*e‖ ≤ 1 := by simpa only [norm_mul,he,mul_one] using hf p
  have hgn : ‖g p*e‖ ≤ 1 := by simpa only [norm_mul,he,mul_one] using hg p
  have hl : -1 ≤ (g p*e).re := by
    have hh := (Complex.abs_re_le_norm (g p*e)).trans hgn
    exact (abs_le.mp hh).1
  have hu : (f p*e).re ≤ 1 := (Complex.re_le_norm _).trans hfn
  rw [← sub_div]
  exact div_le_div_of_nonneg_right (by dsimp [e] at hl hu; linarith) (Nat.cast_nonneg _)

theorem primeDistanceSquared_lower_of_agree (f g : ArithmeticFunction ℂ)
    (hf : ∀ n, ‖f n‖ ≤ 1) (hg : ∀ n, ‖g n‖ ≤ 1)
    (P : Finset ℕ) (X Y t : ℝ)
    (heq : ∀ p : ℕ, p.Prime → p ∉ P → (p : ℝ) ≤ Y → f p = g p) :
    primeDistanceSquared g X t-2*((∑ p ∈ largePrimeSet X Y, 1/(p : ℝ))+
      ∑ p ∈ P, 1/(p : ℝ)) ≤ primeDistanceSquared f X t := by
  let S := (Icc 2 ⌊X⌋₊).filter Nat.Prime
  have hb : primeDistanceSquared g X t-primeDistanceSquared f X t ≤
      ∑ p ∈ S, ((if Y < (p : ℝ) then 2/(p : ℝ) else 0)+
        (if p ∈ P then 2/(p : ℝ) else 0)) := by
    unfold primeDistanceSquared
    rw [← sum_sub_distrib]
    apply sum_le_sum
    intro p hp
    have hp' : p.Prime := (mem_filter.mp hp).2
    by_cases hP : p ∈ P
    · have hh := primeDistance_term_sub_le f g hf hg p t
      rw [ite_eq_left hP]
      split_ifs <;> linarith [show (0 : ℝ) ≤ 2/(p : ℝ) by positivity]
    · rw [ite_eq_right hP,add_zero]
      by_cases hY : Y < (p : ℝ)
      · rw [ite_eq_left hY]
        exact primeDistance_term_sub_le f g hf hg p t
      · rw [ite_eq_right hY,heq p hp' hP (le_of_not_gt hY),sub_self]
  have hl : (∑ p ∈ S, if Y < (p : ℝ) then 2/(p : ℝ) else 0) =
      2*∑ p ∈ largePrimeSet X Y, 1/(p : ℝ) := by
    rw [← sum_filter]
    change (∑ p ∈ ((Icc 2 ⌊X⌋₊).filter Nat.Prime).filter (fun p : ℕ => Y < (p : ℝ)), 2/(p : ℝ)) = _
    rw [← primesLE_eq_filter]
    change (∑ p ∈ largePrimeSet X Y, 2/(p : ℝ)) = _
    rw [mul_sum]
    apply sum_congr rfl
    intro p _
    ring
  have hp : (∑ p ∈ S, if p ∈ P then 2/(p : ℝ) else 0) ≤ 2*∑ p ∈ P, 1/(p : ℝ) := by
    rw [← sum_filter,mul_sum]
    calc
      _ ≤ ∑ p ∈ P, 2/(p : ℝ) := sum_le_sum_of_subset_of_nonneg
        (fun p hp => (mem_filter.mp hp).2) (fun p _ _ => by positivity)
      _ = _ := by apply sum_congr rfl; intro p _; ring
  rw [sum_add_distrib,hl] at hb
  linarith

end JointDickman

end OAI
