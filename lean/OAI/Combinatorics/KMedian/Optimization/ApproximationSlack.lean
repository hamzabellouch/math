import Mathlib

namespace OAI


                                          
section
namespace MetricKMedian

 theorem threshold_bounds : 1 < 1+2/Real.exp 1 ∧ 1+2/Real.exp 1 ≤ 3 := by
  have he : 0 < Real.exp 1 := Real.exp_pos _
  have he1 : 1 ≤ Real.exp 1 := by exact Real.one_le_exp (by norm_num)
  have h := (div_le_iff₀ he).mpr (show (2:ℝ) ≤ 2*Real.exp 1 by linarith only [he1])
  exact ⟨lt_add_of_pos_right 1 (div_pos (by norm_num) he),by linarith only [h]⟩

 theorem slack_product (A s t : ℝ) (hA0 : 0 ≤ A) (hA : A ≤ 3)
    (hs : 0 ≤ s) (hs1 : s ≤ 1/2) (ht : 0 ≤ t) (ht1 : t ≤ s) :
    ((A+s)/(1-s))*(1+s)*(1+t) ≤ A+41*s := by
  have hden : 0 < 1-s := by linarith only [hs1]
  have hd : (A+s)/(1-s) ≤ A+8*s := by
    apply (div_le_iff₀ hden).mpr
    nlinarith [mul_nonneg hs (show 0 ≤ 7-A-8*s by linarith only [hA,hs1])]
  have hss : s*s ≤ s := by nlinarith
  have hsq : (1+s)*(1+s) ≤ 1+3*s := by nlinarith
  calc
    _  ≤  (A+8*s)*(1+s)*(1+t) := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hd (by linarith only [hs])) (by linarith only [ht])
    _  ≤  (A+8*s)*((1+s)*(1+s)) := by
      rw [← mul_assoc]
      apply mul_le_mul_of_nonneg_left (by linarith only [ht1])
      exact mul_nonneg (by linarith only [hA0,hs]) (by linarith only [hs])
    _  ≤  (A+8*s)*(1+3*s) := mul_le_mul_of_nonneg_left hsq (by linarith only [hA0,hs])
    _  ≤  A+41*s := by
      have hAs := mul_le_mul_of_nonneg_right hA hs
      nlinarith only [hss,hAs]

 theorem exists_approximation_slack (ε : ℝ) (hε : 0 < ε) :
    ∃ (s : ℝ) (r : ℕ), 0 < s ∧ s < 1 ∧ 0 < r ∧
      1 < ((1+2/Real.exp 1+s)/(1-s))*(1+s)*(1+3/(r:ℝ)) ∧
      ((1+2/Real.exp 1+s)/(1-s))*(1+s)*(1+3/(r:ℝ))+ε/2 ≤ 1+2/Real.exp 1+ε := by
  let s := min (1/2:ℝ) (ε/100)
  have hs : 0 < s := lt_min (by norm_num) (by positivity)
  have hs1 : s ≤ 1/2 := min_le_left _ _
  have hsε : s ≤ ε/100 := min_le_right _ _
  obtain ⟨r,hr⟩ := exists_nat_gt (3/s)
  have hrR : 0 < (r:ℝ) := lt_trans (by positivity) hr
  have hrN : 0 < r := by exact_mod_cast hrR
  have ht : 3/(r:ℝ) ≤ s := (div_le_iff₀ hrR).mpr (by
    have hh := (div_lt_iff₀ hs).mp hr
    linarith only [hh])
  obtain ⟨hA,hA3⟩ := threshold_bounds
  have hp := slack_product (1+2/Real.exp 1) s (3/(r:ℝ)) (by linarith only [hA]) hA3 hs.le hs1
    (by positivity) ht
  have hbase : 1 < (1+2/Real.exp 1+s)/(1-s) := by
    apply (lt_div_iff₀ (by linarith only [hs1])).mpr
    linarith only [hA,hs]
  have hmul : 1 < ((1+2/Real.exp 1+s)/(1-s))*(1+s)*(1+3/(r:ℝ)) := by
    have ht0 : 0 ≤ 3/(r:ℝ) := by positivity
    have hp1 : 1 < ((1+2/Real.exp 1+s)/(1-s))*(1+s) := by nlinarith only [hbase,hs]
    nlinarith only [hp1,ht0]
  exact ⟨s,r,hs,by linarith only [hs1],hrN,hmul,by linarith only [hp,hsε,hε]⟩

end MetricKMedian
end

end OAI
