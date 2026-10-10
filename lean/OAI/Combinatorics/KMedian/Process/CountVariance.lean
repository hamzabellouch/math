import Mathlib
import OAI.Combinatorics.KMedian.Process.QuadraticCount
import OAI.Combinatorics.KMedian.Probability.BernoulliReindex

namespace OAI

section
section
namespace MetricKMedian.CountStatistic

open Finset
variable {I : Type*} [Fintype I] [DecidableEq I]

theorem action_difference_bound (a m : I → ℝ) (c : I → I → ℝ)
    {D : ℝ} (hD : 1 ≤ D) (ha : ∀ i, 0 ≤ a i) (hm : ∀ i, 0 ≤ m i)
    (hc : ∀ i j, c i j=c j i) (hdiag : ∀ i, c i i=0) (hc0 : ∀ i j, 0 ≤ c i j)
    (hrow : ∀ i, ∑ j, c i j ≤ (D-1)*m i) (ω : I → Bool) (e : I) :
    |statistic (fun i => a i-m i) c (Function.update ω e true)-
      statistic (fun i => a i-m i) c (Function.update ω e false)| ≤ D*(a e+m e) := by
  have hd := difference_bound (fun i => a i-m i) c hc hdiag hc0 ω e
  have habs : |a e-m e| ≤ a e+m e := by
    apply abs_le.mpr
    constructor <;> linarith only [ha e, hm e]
  have hda : a e ≤ D*a e := le_mul_of_one_le_left (ha e) hD
  linarith [hrow e]

theorem variance_bound (p a m : I → ℝ) (c : I → I → ℝ)
    (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    {D P B : ℝ} (hD : 1 ≤ D) (hP : 0 ≤ P)
    (hpP : ∀ i, p i ≤ P) (ha : ∀ i, 0 ≤ a i) (hm : ∀ i, 0 ≤ m i)
    (hsize : ∀ i, a i+m i ≤ B)
    (hc : ∀ i j, c i j=c j i) (hdiag : ∀ i, c i i=0) (hc0 : ∀ i j, 0 ≤ c i j)
    (hrow : ∀ i, ∑ j, c i j ≤ (D-1)*m i) :
    (FiniteLaw.bernoulli p hp0 hp1).variance (statistic (fun i => a i-m i) c) ≤
      P*D^2*B*(∑ i : I, (a i+m i)) := by
  have hD0 : 0 ≤ D := by linarith only [hD]
  apply (FiniteLaw.bernoulli_variance_bounded_differences_fintype p (fun i => D*(a i+m i))
    hp0 hp1 (fun i => mul_nonneg hD0 (add_nonneg (ha i) (hm i))) _
    (fun e ω => action_difference_bound a m c hD ha hm hc hdiag hc0 hrow ω e)).trans
  rw [mul_sum]
  apply sum_le_sum
  intro i _
  have hsum0 := add_nonneg (ha i) (hm i)
  have hbase : p i*(1-p i) ≤ P := by
    calc
      _ ≤ p i := mul_le_of_le_one_right (hp0 i) (by linarith only [hp0 i])
      _ ≤ P := hpP i
  have hsq : (a i+m i)^2 ≤ B*(a i+m i) := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr (hsize i)) hsum0]
  calc
    p i*(1-p i)*(D*(a i+m i))^2 ≤ P*(D*(a i+m i))^2 :=
      mul_le_mul_of_nonneg_right hbase (sq_nonneg _)
    _ = P*D^2*(a i+m i)^2 := by ring
    _ ≤ P*D^2*(B*(a i+m i)) :=
      mul_le_mul_of_nonneg_left hsq (mul_nonneg hP (sq_nonneg _))
    _ = P*D^2*B*(a i+m i) := by ring

theorem expectation_bound (p a m : I → ℝ) (c : I → I → ℝ)
    (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    {P D L : ℝ} (hP : 0 ≤ P) (_hD : 1 ≤ D) (hpP : ∀ i, p i ≤ P)
    (_hm : ∀ i, 0 ≤ m i) (hdiag : ∀ i, c i i=0) (hc0 : ∀ i j, 0 ≤ c i j)
    (hrow : ∀ i, ∑ j, c i j ≤ (D-1)*m i)
    (hlinear : (∑ i, (a i-m i)*p i) ≤ L) :
    (FiniteLaw.bernoulli p hp0 hp1).expect (statistic (fun i => a i-m i) c) ≤
      L+(1/2)*P^2*(D-1)*∑ i, m i := by
  rw [expectation p hp0 hp1 _ c hdiag]
  have hov : (∑ i, ∑ j, c i j*p i*p j) ≤ P^2*(D-1)*∑ i, m i := by
    calc
      _ ≤ ∑ i, ∑ j, P^2*c i j := by
        apply sum_le_sum
        intro i _
        apply sum_le_sum
        intro j _
        have hprod := mul_le_mul (hpP i) (hpP j) (hp0 j) hP
        have hh := mul_le_mul_of_nonneg_left hprod (hc0 i j)
        nlinarith only [hh]
      _ = P^2*∑ i, ∑ j, c i j := by simp only [mul_sum]
      _ ≤ P^2*∑ i, (D-1)*m i :=
        mul_le_mul_of_nonneg_left (sum_le_sum (fun i _ => hrow i)) (sq_nonneg _)
      _ = _ := by rw [← mul_sum]; ring
  nlinarith only [hlinear, hov]

theorem positive_probability_bound (p a m : I → ℝ)
    (c : I → I → ℝ) (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    {D P B t : ℝ} (hD : 1 ≤ D) (hP : 0 ≤ P) (ht : 0 < t)
    (hpP : ∀ i, p i ≤ P) (ha : ∀ i, 0 ≤ a i) (hm : ∀ i, 0 ≤ m i)
    (hsize : ∀ i, a i+m i ≤ B)
    (hc : ∀ i j, c i j=c j i) (hdiag : ∀ i, c i i=0) (hc0 : ∀ i j, 0 ≤ c i j)
    (hrow : ∀ i, ∑ j, c i j ≤ (D-1)*m i)
    (hlinear : (∑ i, (a i-m i)*p i) ≤ -t-(1/2)*P^2*(D-1)*∑ i, m i) :
    (FiniteLaw.bernoulli p hp0 hp1).prob (fun ω =>
      0 < statistic (fun i => a i-m i) c ω) ≤ (P*D^2*B*(∑ i : I, (a i+m i)))/t^2 := by
  have he := expectation_bound p a m c hp0 hp1 hP hD hpP hm hdiag hc0 hrow hlinear
  have hv := variance_bound p a m c hp0 hp1 hD hP hpP ha hm hsize hc hdiag hc0 hrow
  exact (FiniteLaw.prob_positive_le _ _ ht (by linarith only [he])).trans
    (div_le_div_of_nonneg_right hv (sq_nonneg t))

end MetricKMedian.CountStatistic
end
end

end OAI
