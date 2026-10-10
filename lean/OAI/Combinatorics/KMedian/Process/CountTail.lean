import Mathlib
import OAI.Combinatorics.KMedian.Process.CountVariance

namespace OAI

section
section
namespace MetricKMedian.CountStatistic
open Finset
variable {I : Type*} [Fintype I] [DecidableEq I]

theorem overlap_budget {p φ g A D M : ℝ}
    (hp : 0 ≤ p) (hg : 0 < g) (hA : 0 ≤ A) (hD : 1 ≤ D) (hM : 0 ≤ M)
    (hmass : M ≤ 2*A/g) (hsmall : 8*p*D ≤ φ*g) :
    (1/2)*(2*p)^2*(D-1)*M ≤ p*φ*A/2 := by
  have hD0 : 0 ≤ D := by linarith only [hD]
  have hmg : M*g ≤ 2*A := (le_div_iff₀ hg).mp hmass
  have h1 := mul_le_mul_of_nonneg_left hmg (show 0 ≤ 2*p^2*D by positivity)
  have h2 := mul_le_mul_of_nonneg_right hsmall (show 0 ≤ p*A by positivity)
  have h3 : 0 ≤ p^2*M*g := by positivity
  apply (mul_le_mul_iff_right₀ hg).mp
  nlinarith only [h1,h2,h3]

theorem conditional_count_tail (q a m : I → ℝ) (c : I → I → ℝ)
    (hq0 : ∀ i, 0 ≤ q i) (hq1 : ∀ i, q i ≤ 1) {D p φ g A b : ℝ}
    (hD : 1 ≤ D) (hp : 0 < p) (hφ : 0 < φ) (hg : 0 < g) (hb : 0 < b)
    (hlarge : 1 < b*A) (hq : ∀ i, q i ≤ 2*p)
    (ha : ∀ i, 0 ≤ a i) (hm : ∀ i, 0 ≤ m i) (hsize : ∀ i, a i+m i ≤ b*A+2)
    (hc : ∀ i j, c i j=c j i) (hdiag : ∀ i, c i i=0) (hc0 : ∀ i j, 0 ≤ c i j)
    (hrow : ∀ i, ∑ j, c i j ≤ (D-1)*m i)
    (hmass : (∑ i, m i) ≤ 2*A/g) (htotal : (∑ i, (a i+m i)) ≤ 4*A/g)
    (hsmall : 8*p*D ≤ φ*g) (hlinear : (∑ i, (a i-m i)*q i) ≤ -p*φ*A) :
    (FiniteLaw.bernoulli q hq0 hq1).prob (fun ω => 0 < statistic (fun i => a i-m i) c ω) ≤
      96*D^2*b/(p*φ^2*g) := by
  have hA : 0 < A := (mul_pos_iff_of_pos_left hb).mp (lt_trans (by norm_num) hlarge)
  have ht : 0 < p*φ*A/2 := by positivity
  have hM : 0 ≤ ∑ i, m i := sum_nonneg (fun i _ => hm i)
  have hov := overlap_budget hp.le hg hA.le hD hM hmass hsmall
  have hlin : (∑ i, (a i-m i)*q i) ≤ -(p*φ*A/2)-(1/2)*(2*p)^2*(D-1)*∑ i, m i :=
    by linarith only [hlinear,hov]
  have hprob := positive_probability_bound q a m c hq0 hq1 hD (by positivity) ht hq ha hm
    hsize hc hdiag hc0 hrow hlin
  apply hprob.trans
  have hsum : 0 ≤ ∑ i, (a i+m i) := sum_nonneg (fun i _ => add_nonneg (ha i) (hm i))
  have hB : b*A+2 ≤ 3*b*A := by linarith only [hlarge]
  calc
    (2*p)*D^2*(b*A+2)*(∑ i, (a i+m i))/(p*φ*A/2)^2 ≤
        (2*p)*D^2*(3*b*A)*(4*A/g)/(p*φ*A/2)^2 := by
      apply div_le_div_of_nonneg_right _ (sq_nonneg _)
      exact mul_le_mul (mul_le_mul_of_nonneg_left hB (by positivity)) htotal hsum (by positivity)
    _ = 96*D^2*b/(p*φ^2*g) := by
      field_simp
      ring

end MetricKMedian.CountStatistic
end
end

end OAI
