import Mathlib
import OAI.Probability.SKBarriers.Dynamics.ClockTail
import OAI.Probability.SKBarriers.Dynamics.BarrierCrossing

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic

theorem occupation_mono {n : ℕ} (β : ℝ) (J : Disorder n) (A : Config n → Prop) [DecidablePred A]
    {k m : ℕ} (hkm : k ≤ m) (x : Config n) : occupation β J A k x ≤ occupation β J A m x := by
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.add_le_add_right hkm 1))
  intro i _ _
  exact kernelEvent_nonneg _ _ _ _ _

theorem clock_kernelEvent_summable {n : ℕ} (hn : 0 < n) (β : ℝ) (J : Disorder n)
    (A : Config n → Prop) [DecidablePred A] {a : ℝ} (ha : 0 ≤ a) (x : Config n) :
    Summable (fun k : ℕ => clockWeight a k*kernelEvent β J A k x) := by
  apply Summable.of_nonneg_of_le _ _ (clockWeight_hasSum a).summable
  · intro k
    exact mul_nonneg (clockWeight_nonneg ha k) (kernelEvent_nonneg _ _ _ _ _)
  · intro k
    exact mul_le_of_le_one_right (clockWeight_nonneg ha k) (kernelEvent_le_one hn β J A k x)

theorem continuous_event_eq_clock {n : ℕ} (hn : 0 < n) (β : ℝ) (J : Disorder n)
    (A : Config n → Prop) [DecidablePred A] {t : ℝ} (ht : 0 ≤ t) (x : Config n) :
    (∑ y : Config n, if A y then continuousKernel β J t x y else 0) =
      ∑' k : ℕ, clockWeight ((n:ℝ)*t) k*kernelEvent β J A k x := by
  have he (y : Config n) : (if A y then continuousKernel β J t x y else 0) =
      ∑' k : ℕ, if A y then clockWeight ((n:ℝ)*t) k*discreteKernel β J k x y else 0 := by
    by_cases hy : A y
    · simp only [ite_eq_left hy,continuousKernel_eq_clock]
    · simp only [ite_eq_right hy,tsum_zero]
  have hs (y : Config n) : Summable (fun k : ℕ =>
      if A y then clockWeight ((n:ℝ)*t) k*discreteKernel β J k x y else 0) := by
    by_cases hy : A y
    · simp only [ite_eq_left hy]
      exact uniformization_summable hn β J ht x y
    · simp only [ite_eq_right hy]
      exact summable_zero
  simp_rw [he]
  rw [← Summable.tsum_finsetSum (fun y (_ : y ∈ (Finset.univ : Finset (Config n))) => hs y)]
  simp only [kernelEvent,Finset.mul_sum,mul_ite,mul_zero]

theorem continuous_sign_le_stripOccupation_tail {n : ℕ} (hn : 0 < n) (β : ℝ) (J : Disorder n)
    (v : Config n) {a₀ a₁ : ℝ} (ha₀ : 0 < a₀) (hgap : 2/(n:ℝ) < a₁-a₀)
    {t : ℝ} (ht : 0 ≤ t) (m : ℕ) (x : Config n) (hx : a₁ < overlap v x) :
    (∑ y : Config n, if overlap v y ≤ 0 then continuousKernel β J t x y else 0) ≤
      occupation β J (fun y => a₀ ≤ overlap v y ∧ overlap v y ≤ a₁) m x +
        ∑' k : ℕ, if m < k then clockWeight ((n:ℝ)*t) k else 0 := by
  rw [continuous_event_eq_clock hn β J _ ht]
  have ha : 0 ≤ (n:ℝ)*t := by positivity
  let O := occupation β J (fun y => a₀ ≤ overlap v y ∧ overlap v y ≤ a₁) m x
  have hO : 0 ≤ O := occupation_nonneg _ _ _ _ _
  have H := (clock_kernelEvent_summable hn β J (fun y => overlap v y ≤ 0) ha x).tsum_le_tsum
    (g := fun k => clockWeight ((n:ℝ)*t) k*O+(if m < k then clockWeight ((n:ℝ)*t) k else 0))
    (fun k => show _ ≤ _ from by
      by_cases hk : m < k
      · simp only [ite_eq_left hk]
        have HH := mul_le_of_le_one_right (clockWeight_nonneg ha k) (kernelEvent_le_one hn β J (fun y => overlap v y ≤ 0) k x)
        linarith [mul_nonneg (clockWeight_nonneg ha k) hO]
      · simp only [ite_eq_right hk,add_zero]
        exact mul_le_mul_of_nonneg_left ((signEvent_le_stripOccupation hn β J v ha₀ hgap k x hx).trans
          (occupation_mono β J _ (le_of_not_gt hk) x)) (clockWeight_nonneg ha k))
    (((clockWeight_hasSum ((n:ℝ)*t)).summable.mul_right O).add (clockWeight_tail_summable ha m))
  rw [Summable.tsum_add ((clockWeight_hasSum ((n:ℝ)*t)).summable.mul_right O)
    (clockWeight_tail_summable ha m),tsum_mul_right,clockWeight_sum,one_mul] at H
  exact H

theorem eighth_le_stripOccupation_of_continuous_tv {n : ℕ} (hn : 0 < n) (β : ℝ) (J : Disorder n)
    (v : Config n) {a₀ a₁ : ℝ} (ha₀ : 0 < a₀) (hgap : 2/(n:ℝ) < a₁-a₀)
    (L : ℝ) (hL : (n:ℝ)*Real.exp (-L) ≤ (1/8:ℝ)) (x : Config n) (hx : a₁ < overlap v x)
    (hTV : continuousDistance β J x (Real.exp L) ≤ (1/4:ℝ)) :
    (1/8:ℝ) ≤ occupation β J (fun y => a₀ ≤ overlap v y ∧ overlap v y ≤ a₁)
      ⌈Real.exp (2*L)⌉₊ x := by
  have H₁ := continuous_sign_mass_of_tv hn β J x v (le_of_lt (Real.exp_pos L)) hTV
  have H₂ := continuous_sign_le_stripOccupation_tail hn β J v ha₀ hgap
    (le_of_lt (Real.exp_pos L)) ⌈Real.exp (2*L)⌉₊ x hx
  have H₃ := attempt_horizon_tail n L
  linarith

theorem mass_continuous_mixed_high_le_strip {n : ℕ} (hn : 0 < n) (β : ℝ) (J : Disorder n)
    (v : Config n) {a₀ a₁ : ℝ} (ha₀ : 0 < a₀) (hgap : 2/(n:ℝ) < a₁-a₀)
    (L : ℝ) (hL : (n:ℝ)*Real.exp (-L) ≤ (1/8:ℝ)) :
    (∑ x : Config n, if a₁ < overlap v x ∧ continuousDistance β J x (Real.exp L) ≤ (1/4:ℝ)
      then gibbs β J x else 0) ≤ 8*((⌈Real.exp (2*L)⌉₊+1:ℕ):ℝ)*
        (∑ y : Config n, if a₀ ≤ overlap v y ∧ overlap v y ≤ a₁ then gibbs β J y else 0) := by
  have HH := Finset.sum_le_sum (s := (Finset.univ : Finset (Config n)))
    (f := fun x => if a₁ < overlap v x ∧ continuousDistance β J x (Real.exp L) ≤ (1/4:ℝ)
      then gibbs β J x else 0)
    (g := fun x => 8*(gibbs β J x*occupation β J (fun y => a₀ ≤ overlap v y ∧ overlap v y ≤ a₁)
      ⌈Real.exp (2*L)⌉₊ x))
    (fun x _ => show _ ≤ _ from by
      split_ifs with hx
      · have H := eighth_le_stripOccupation_of_continuous_tv hn β J v ha₀ hgap L hL x hx.1 hx.2
        nlinarith [mul_le_mul_of_nonneg_left H (le_of_lt (gibbs_pos β J x))]
      · exact mul_nonneg (by norm_num) (mul_nonneg (le_of_lt (gibbs_pos β J x))
          (occupation_nonneg _ _ _ _ _)))
  rw [← Finset.mul_sum,occupation_stationary hn] at HH
  simpa only [mul_assoc] using HH

end SK.Analytic

end
end

end

end OAI
