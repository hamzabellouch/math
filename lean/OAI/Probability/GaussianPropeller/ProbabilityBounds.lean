import OAI.Probability.GaussianPropeller.Taylor

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
open Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
open scoped RealInnerProductSpace
open Set Filter
open scoped Topology RealInnerProductSpace
open scoped NNReal
open Set Filter
open scoped Topology RealInnerProductSpace NNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology BigOperators

namespace GaussianPropeller.ProbabilityBounds
open OneCell Mills Taylor
noncomputable def p (x : ℝ) : ℝ := gaussianConst*tail x

lemma gaussianConst_tight : (398942/1000000:ℝ) ≤ gaussianConst ∧ gaussianConst ≤ 398943/1000000 := by
  refine ⟨?_, gaussianConst_bounds.2⟩
  have hs := Real.sq_sqrt (show 0 ≤ 2*Real.pi by positivity)
  have hspos : 0 < Real.sqrt (2*Real.pi) := by positivity
  rw [gaussianConst, inv_eq_one_div, le_div_iff₀ hspos]
  have hh := Real.pi_lt_d6
  nlinarith

lemma p_pos (x : ℝ) : 0 < p x :=
  mul_pos (lt_of_lt_of_le (by norm_num) gaussianConst_tight.1) (tail_pos x)

lemma hasDerivAt_p (x : ℝ) : HasDerivAt p (-gaussianConst*density x) x := by
  convert (hasDerivAt_tail x).const_mul gaussianConst using 1 <;> first | rfl | ring

lemma p_antitone : Antitone p := by
  apply antitone_of_hasDerivAt_nonpos (fun x => hasDerivAt_p x)
  intro x
  exact mul_nonpos_of_nonpos_of_nonneg (by linarith [gaussianConst_tight.1]) (Real.exp_pos _).le

lemma p_le_half {x : ℝ} (hx : 0 ≤ x) : p x ≤ 1/2 := by
  have hh := p_antitone hx
  simpa only [p,tail_zero] using hh

lemma p_taylor_lower {x : ℝ} (hx : 0 ≤ x) (n : ℕ) (hJ : 0 ≤ J (2*n) x) :
    1/2-(398943/1000000:ℝ)*J (2*n) x ≤ p x := by
  have hh := (integral_exp_bounds n hx).2
  change (∫ t in (0:ℝ)..x, density t) ≤ J (2*n) x at hh
  have hmul := mul_le_mul_of_nonneg_left hh
    (lt_of_lt_of_le (by norm_num) gaussianConst_tight.1).le
  have hmul' := mul_le_mul_of_nonneg_right gaussianConst_tight.2 hJ
  unfold p
  rw [tail_sub hx, mul_sub, tail_zero]
  linarith only [hmul,hmul']

lemma p_taylor_upper {x : ℝ} (hx : 0 ≤ x) (n : ℕ) (hJ : 0 ≤ J (2*n+1) x) :
    p x ≤ 1/2-(398942/1000000:ℝ)*J (2*n+1) x := by
  have hh := (integral_exp_bounds n hx).1
  change J (2*n+1) x ≤ ∫ t in (0:ℝ)..x, density t at hh
  have hmul := mul_le_mul_of_nonneg_left hh
    (lt_of_lt_of_le (by norm_num) gaussianConst_tight.1).le
  have hmul' := mul_le_mul_of_nonneg_right gaussianConst_tight.1 hJ
  unfold p
  rw [tail_sub hx, mul_sub, tail_zero]
  linarith only [hmul,hmul']

lemma lambda_taylor_upper {x : ℝ} (hx : 0 ≤ x) (n : ℕ) {L : ℝ} (hL : 0 ≤ L)
    (hJ : 0 ≤ J (2*n) x)
    (hc : (398943/1000000:ℝ)*E (2*n) (x^2/2) ≤
      L*(1/2-(398943/1000000:ℝ)*J (2*n) x)) : lambda x ≤ L := by
  have he := exp_le_E_even n (show 0 ≤ x^2/2 by positivity)
  rw [← neg_div] at he
  change density x ≤ E (2*n) (x^2/2) at he
  have hd : 0 ≤ density x := (Real.exp_pos _).le
  have hmul := mul_le_mul he gaussianConst_tight.2
    (le_trans (by norm_num) gaussianConst_tight.1) (hd.trans he)
  have ht := mul_le_mul_of_nonneg_left (p_taylor_lower hx n hJ) hL
  have hpos : 0 < gaussianConst := lt_of_lt_of_le (by norm_num) gaussianConst_tight.1
  rw [lambda, div_le_iff₀ (tail_pos x)]
  apply (mul_le_mul_iff_right₀ hpos).mp
  dsimp [p] at ht
  nlinarith only [hmul,hc,ht]

lemma G_upper_of_lambda {x L U : ℝ} (hx : 0 ≤ x) (h : lambda x ≤ L)
    (hLU : L*(L-x) ≤ U) : G x ≤ U := by
  have hl : 0 ≤ lambda x-x := (mul_nonneg_iff_of_pos_left (lambda_pos x)).mp (G_nonneg hx)
  have hh := mul_nonneg (sub_nonneg.mpr h)
    (show 0 ≤ L+lambda x-x by linarith [lambda_pos x])
  unfold G
  nlinarith only [hh,hLU]

lemma certificate_005 : p (2.1) < (0.415+0.15*0.05)*0.05 ∧ G (2.1) ≤ 0.91 := by
  have hj12 : 0 ≤ J 12 (2.1) := by norm_num [J, Finset.sum_range_succ, Nat.factorial]
  have hj13 : 0 ≤ J 13 (2.1) := by norm_num [J, Finset.sum_range_succ, Nat.factorial]
  constructor
  · have ht := p_taylor_upper (by norm_num : (0:ℝ) ≤ 2.1) 6 hj13
    have hc : 1/2-(398942/1000000:ℝ)*J 13 (2.1) < (0.415+0.15*0.05)*0.05 := by
      norm_num [J, Finset.sum_range_succ, Nat.factorial]
    exact lt_of_le_of_lt ht hc
  · apply G_upper_of_lambda (by norm_num : (0:ℝ) ≤ 2.1) (L := 2.463)
    · apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj12
      norm_num [E,J, Finset.sum_range_succ, Nat.factorial]
    · norm_num

lemma certificate_014 : p (1.6) < (0.415+0.15*0.14)*0.14 ∧ G (1.6) ≤ 0.87 := by
  have hj12 : 0 ≤ J 12 (1.6) := by norm_num [J, Finset.sum_range_succ, Nat.factorial]
  have hj13 : 0 ≤ J 13 (1.6) := by norm_num [J, Finset.sum_range_succ, Nat.factorial]
  constructor
  · have ht := p_taylor_upper (by norm_num : (0:ℝ) ≤ 1.6) 6 hj13
    have hc : 1/2-(398942/1000000:ℝ)*J 13 (1.6) < (0.415+0.15*0.14)*0.14 := by
      norm_num [J, Finset.sum_range_succ, Nat.factorial]
    exact lt_of_le_of_lt ht hc
  · apply G_upper_of_lambda (by norm_num : (0:ℝ) ≤ 1.6) (L := 2.025)
    · apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj12
      norm_num [E,J, Finset.sum_range_succ, Nat.factorial]
    · norm_num

lemma certificate_024 : p (1.3) < (0.415+0.15*0.24)*0.24 ∧ G (1.3) ≤ 0.836 := by
  have hj12 : 0 ≤ J 12 (1.3) := by norm_num [J, Finset.sum_range_succ, Nat.factorial]
  have hj13 : 0 ≤ J 13 (1.3) := by norm_num [J, Finset.sum_range_succ, Nat.factorial]
  constructor
  · have ht := p_taylor_upper (by norm_num : (0:ℝ) ≤ 1.3) 6 hj13
    have hc : 1/2-(398942/1000000:ℝ)*J 13 (1.3) < (0.415+0.15*0.24)*0.24 := by
      norm_num [J, Finset.sum_range_succ, Nat.factorial]
    exact lt_of_le_of_lt ht hc
  · apply G_upper_of_lambda (by norm_num : (0:ℝ) ≤ 1.3) (L := 1.771)
    · apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj12
      norm_num [E,J, Finset.sum_range_succ, Nat.factorial]
    · norm_num

lemma certificate_033 : p (1.04) < (0.415+0.15*0.33)*0.33 ∧ G (1.04) ≤ 0.809 := by
  have hj12 : 0 ≤ J 12 (1.04) := by norm_num [J, Finset.sum_range_succ, Nat.factorial]
  have hj13 : 0 ≤ J 13 (1.04) := by norm_num [J, Finset.sum_range_succ, Nat.factorial]
  constructor
  · have ht := p_taylor_upper (by norm_num : (0:ℝ) ≤ 1.04) 6 hj13
    have hc : 1/2-(398942/1000000:ℝ)*J 13 (1.04) < (0.415+0.15*0.33)*0.33 := by
      norm_num [J, Finset.sum_range_succ, Nat.factorial]
    exact lt_of_le_of_lt ht hc
  · apply G_upper_of_lambda (by norm_num : (0:ℝ) ≤ 1.04) (L := 1.558)
    · apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj12
      norm_num [E,J, Finset.sum_range_succ, Nat.factorial]
    · norm_num

lemma certificate_041 : p (0.87) < (0.415+0.15*0.41)*0.41 ∧ G (0.87) ≤ 0.788 := by
  have hj12 : 0 ≤ J 12 (0.87) := by norm_num [J, Finset.sum_range_succ, Nat.factorial]
  have hj13 : 0 ≤ J 13 (0.87) := by norm_num [J, Finset.sum_range_succ, Nat.factorial]
  constructor
  · have ht := p_taylor_upper (by norm_num : (0:ℝ) ≤ 0.87) 6 hj13
    have hc : 1/2-(398942/1000000:ℝ)*J 13 (0.87) < (0.415+0.15*0.41)*0.41 := by
      norm_num [J, Finset.sum_range_succ, Nat.factorial]
    exact lt_of_le_of_lt ht hc
  · apply G_upper_of_lambda (by norm_num : (0:ℝ) ≤ 0.87) (L := 1.423)
    · apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj12
      norm_num [E,J, Finset.sum_range_succ, Nat.factorial]
    · norm_num

lemma certificate_048 : p (0.74) < (0.415+0.15*0.48)*0.48 ∧ G (0.74) ≤ 0.771 := by
  have hj12 : 0 ≤ J 12 (0.74) := by norm_num [J, Finset.sum_range_succ, Nat.factorial]
  have hj13 : 0 ≤ J 13 (0.74) := by norm_num [J, Finset.sum_range_succ, Nat.factorial]
  constructor
  · have ht := p_taylor_upper (by norm_num : (0:ℝ) ≤ 0.74) 6 hj13
    have hc : 1/2-(398942/1000000:ℝ)*J 13 (0.74) < (0.415+0.15*0.48)*0.48 := by
      norm_num [J, Finset.sum_range_succ, Nat.factorial]
    exact lt_of_le_of_lt ht hc
  · apply G_upper_of_lambda (by norm_num : (0:ℝ) ≤ 0.74) (L := 1.322)
    · apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj12
      norm_num [E,J, Finset.sum_range_succ, Nat.factorial]
    · norm_num

lemma certificate_054 : p (0.63) < (0.415+0.15*0.54)*0.54 ∧ G (0.63) ≤ 0.756 := by
  have hj12 : 0 ≤ J 12 (0.63) := by norm_num [J, Finset.sum_range_succ, Nat.factorial]
  have hj13 : 0 ≤ J 13 (0.63) := by norm_num [J, Finset.sum_range_succ, Nat.factorial]
  constructor
  · have ht := p_taylor_upper (by norm_num : (0:ℝ) ≤ 0.63) 6 hj13
    have hc : 1/2-(398942/1000000:ℝ)*J 13 (0.63) < (0.415+0.15*0.54)*0.54 := by
      norm_num [J, Finset.sum_range_succ, Nat.factorial]
    exact lt_of_le_of_lt ht hc
  · apply G_upper_of_lambda (by norm_num : (0:ℝ) ≤ 0.63) (L := 1.238)
    · apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj12
      norm_num [E,J, Finset.sum_range_succ, Nat.factorial]
    · norm_num

lemma certificate_059 : p (0.55) < (0.415+0.15*0.59)*0.59 ∧ G (0.55) ≤ 0.743 := by
  have hj12 : 0 ≤ J 12 (0.55) := by norm_num [J, Finset.sum_range_succ, Nat.factorial]
  have hj13 : 0 ≤ J 13 (0.55) := by norm_num [J, Finset.sum_range_succ, Nat.factorial]
  constructor
  · have ht := p_taylor_upper (by norm_num : (0:ℝ) ≤ 0.55) 6 hj13
    have hc : 1/2-(398942/1000000:ℝ)*J 13 (0.55) < (0.415+0.15*0.59)*0.59 := by
      norm_num [J, Finset.sum_range_succ, Nat.factorial]
    exact lt_of_le_of_lt ht hc
  · apply G_upper_of_lambda (by norm_num : (0:ℝ) ≤ 0.55) (L := 1.178)
    · apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj12
      norm_num [E,J, Finset.sum_range_succ, Nat.factorial]
    · norm_num

lemma certificate_064 : p (0.47) < (0.415+0.15*0.64)*0.64 ∧ G (0.47) ≤ 0.73 := by
  have hj12 : 0 ≤ J 12 (0.47) := by norm_num [J, Finset.sum_range_succ, Nat.factorial]
  have hj13 : 0 ≤ J 13 (0.47) := by norm_num [J, Finset.sum_range_succ, Nat.factorial]
  constructor
  · have ht := p_taylor_upper (by norm_num : (0:ℝ) ≤ 0.47) 6 hj13
    have hc : 1/2-(398942/1000000:ℝ)*J 13 (0.47) < (0.415+0.15*0.64)*0.64 := by
      norm_num [J, Finset.sum_range_succ, Nat.factorial]
    exact lt_of_le_of_lt ht hc
  · apply G_upper_of_lambda (by norm_num : (0:ℝ) ≤ 0.47) (L := 1.120)
    · apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj12
      norm_num [E,J, Finset.sum_range_succ, Nat.factorial]
    · norm_num

lemma exists_p {P : ℝ} (hP : 0 < P) (hPh : P ≤ 1/2) : ∃ x ≥ (0:ℝ), p x=P := by
  have ht : Tendsto p atTop (𝓝 0) := by
    convert! (tendsto_integral_Ioi_zero (f := density) (μ := volume) tendsto_id).const_mul gaussianConst using 1
    simp only [mul_zero]
  have hh := isPreconnected_Ici.intermediate_value_Ioc (a := (0:ℝ)) self_mem_Ici
    (le_principal_iff.mpr (Ici_mem_atTop (0:ℝ)))
    (show ContinuousOn p (Ici 0) from fun x _ => (hasDerivAt_p x).continuousAt.continuousWithinAt) ht
  have hm : P ∈ Ioc 0 (p 0) := by exact ⟨hP, by simpa [p,tail_zero] using hPh⟩
  exact hh hm

noncomputable def loss (x : ℝ) : ℝ := p x^2*G x

lemma loss_eq (x : ℝ) : loss x=gaussianConst^2*density x*(density x-x*tail x) := by
  unfold loss p G lambda
  field_simp [(tail_pos x).ne']

lemma hasDerivAt_loss (x : ℝ) : HasDerivAt loss
    (gaussianConst^2*density x*(x^2*tail x-x*density x-tail x)) x := by
  have he : loss = fun x => gaussianConst^2*density x*(density x-x*tail x) := funext loss_eq
  rw [he]
  convert ((hasDerivAt_density x).const_mul (gaussianConst^2)).mul
    ((hasDerivAt_density x).sub ((hasDerivAt_id x).mul (hasDerivAt_tail x))) using 1 <;>
      first | rfl | (simp only [Pi.sub_apply, Pi.mul_apply, id_eq]; ring)

lemma loss_antitone : AntitoneOn loss (Ici 0) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici 0)
    (fun x _ => (hasDerivAt_loss x).continuousAt.continuousWithinAt)
    (fun x _ => (hasDerivAt_loss x).hasDerivWithinAt)
  intro x hx
  have hx' : 0 ≤ x := interior_subset hx
  have hl : x ≤ lambda x := by
    have hh := (mul_nonneg_iff_of_pos_left (lambda_pos x)).mp (G_nonneg hx')
    linarith only [hh]
  rw [lambda, le_div_iff₀ (tail_pos x)] at hl
  apply mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)
  have hh := mul_le_mul_of_nonneg_left hl hx'
  have ht : 0 < tail x := tail_pos x
  have hm : 0 ≤ x*density x := mul_nonneg hx' (Real.exp_pos _).le
  nlinarith only [hh,ht,hm]

lemma G_test_bound {a r x w U : ℝ} (ha : 0 ≤ a) (har : a ≤ r)
    (hx : 0 ≤ x) (hw : 0 ≤ w) (hp : p x=(0.415+0.15*r)*r)
    (hc : p w < (0.415+0.15*a)*a ∧ G w ≤ U) : G x ≤ U := by
  have hpw : p w < p x := by
    rw [hp]
    have hm := mul_nonneg (sub_nonneg.mpr har) (show 0 ≤ r+a by linarith)
    nlinarith only [hc.1,har,hm]
  have hxw : x ≤ w := by
    by_contra! hgt
    exact (not_lt_of_ge (p_antitone hgt.le)) hpw
  exact (G_monotone hx hw hxw).trans hc.2

lemma row_margin {a b r x U S : ℝ} (ha : 0 ≤ a) (har : a ≤ r) (hrb : r ≤ b)
    (hb : b ≤ 2/3) (hU : 0 ≤ U) (hG : G x ≤ U) (hS : 0 ≤ S)
    (hSsq : 1-a^2 ≤ S^2)
    (hc : U*(0.415+0.15*b)^2 < (9/(8*3.1416:ℝ))/(1+S)) :
    (0.415+0.15*r)^2*G x < (9/(8*Real.pi))/(1+Real.sqrt (1-r^2)) := by
  have hr : 0 ≤ r := ha.trans har
  have hr2 : r^2 ≤ (1:ℝ) := by nlinarith only [hr,hrb,hb]
  have hs := Real.sq_sqrt (show 0 ≤ 1-r^2 by linarith only [hr2])
  have hsp := Real.sqrt_nonneg (1-r^2)
  have hsq : Real.sqrt (1-r^2) ≤ S := by
    have hm := mul_nonneg (sub_nonneg.mpr har) (show 0 ≤ r+a by positivity)
    nlinarith only [hs,hsp,hSsq,hS,hm]
  have hbcoef : (0.415+0.15*r)^2 ≤ (0.415+0.15*b)^2 := by
    nlinarith only [hr,hrb, sq_nonneg (b-r)]
  have hh₁ := mul_le_mul_of_nonneg_left hG (sq_nonneg (0.415+0.15*r))
  have hh₂ := mul_le_mul_of_nonneg_right hbcoef hU
  have hB : (9/(8*3.1416:ℝ)) ≤ 9/(8*Real.pi) :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith [Real.pi_lt_d4])
  have hd₁ := div_le_div_of_nonneg_left (by norm_num : (0:ℝ) ≤ 9/(8*3.1416))
    (show 0 < 1+Real.sqrt (1-r^2) by positivity) (show 1+Real.sqrt (1-r^2) ≤ 1+S by linarith only [hsq])
  have hd₂ := div_le_div_of_nonneg_right hB (show 0 ≤ 1+Real.sqrt (1-r^2) by positivity)
  have hc' : (0.415+0.15*b)^2*U < (9/(8*3.1416:ℝ))/(1+S) := by simpa only [mul_comm] using hc
  exact lt_of_le_of_lt (hh₁.trans hh₂) (lt_of_lt_of_le hc' (hd₁.trans hd₂))

lemma test_probability {r x : ℝ} (hr : 0 < r) (hrcap : r ≤ 2/3) (hx : 0 ≤ x)
    (hp : p x=(0.415+0.15*r)*r) :
    (0.415+0.15*r)^2*G x < (9/(8*Real.pi))/(1+Real.sqrt (1-r^2)) := by
  by_cases h0 : r ≤ 0.05
  · apply row_margin (a := 0) (b := 0.05) (U := 1) (S := 1)
    · norm_num
    · exact hr.le
    · exact h0
    · norm_num
    · norm_num
    · exact G_le_one x
    · norm_num
    · norm_num
    · norm_num
  by_cases h1 : r ≤ 0.14
  · apply row_margin (a := 0.05) (b := 0.14) (U := 0.91) (S := 0.99875)
    · norm_num
    · exact (lt_of_not_ge h0).le
    · exact h1
    · norm_num
    · norm_num
    · exact G_test_bound (by norm_num) (lt_of_not_ge h0).le hx (by norm_num) hp certificate_005
    · norm_num
    · norm_num
    · norm_num
  by_cases h2 : r ≤ 0.24
  · apply row_margin (a := 0.14) (b := 0.24) (U := 0.87) (S := 0.99016)
    · norm_num
    · exact (lt_of_not_ge h1).le
    · exact h2
    · norm_num
    · norm_num
    · exact G_test_bound (by norm_num) (lt_of_not_ge h1).le hx (by norm_num) hp certificate_014
    · norm_num
    · norm_num
    · norm_num
  by_cases h3 : r ≤ 0.33
  · apply row_margin (a := 0.24) (b := 0.33) (U := 0.836) (S := 0.97078)
    · norm_num
    · exact (lt_of_not_ge h2).le
    · exact h3
    · norm_num
    · norm_num
    · exact G_test_bound (by norm_num) (lt_of_not_ge h2).le hx (by norm_num) hp certificate_024
    · norm_num
    · norm_num
    · norm_num
  by_cases h4 : r ≤ 0.41
  · apply row_margin (a := 0.33) (b := 0.41) (U := 0.809) (S := 0.94399)
    · norm_num
    · exact (lt_of_not_ge h3).le
    · exact h4
    · norm_num
    · norm_num
    · exact G_test_bound (by norm_num) (lt_of_not_ge h3).le hx (by norm_num) hp certificate_033
    · norm_num
    · norm_num
    · norm_num
  by_cases h5 : r ≤ 0.48
  · apply row_margin (a := 0.41) (b := 0.48) (U := 0.788) (S := 0.91209)
    · norm_num
    · exact (lt_of_not_ge h4).le
    · exact h5
    · norm_num
    · norm_num
    · exact G_test_bound (by norm_num) (lt_of_not_ge h4).le hx (by norm_num) hp certificate_041
    · norm_num
    · norm_num
    · norm_num
  by_cases h6 : r ≤ 0.54
  · apply row_margin (a := 0.48) (b := 0.54) (U := 0.771) (S := 0.87727)
    · norm_num
    · exact (lt_of_not_ge h5).le
    · exact h6
    · norm_num
    · norm_num
    · exact G_test_bound (by norm_num) (lt_of_not_ge h5).le hx (by norm_num) hp certificate_048
    · norm_num
    · norm_num
    · norm_num
  by_cases h7 : r ≤ 0.59
  · apply row_margin (a := 0.54) (b := 0.59) (U := 0.756) (S := 0.84167)
    · norm_num
    · exact (lt_of_not_ge h6).le
    · exact h7
    · norm_num
    · norm_num
    · exact G_test_bound (by norm_num) (lt_of_not_ge h6).le hx (by norm_num) hp certificate_054
    · norm_num
    · norm_num
    · norm_num
  by_cases h8 : r ≤ 0.64
  · apply row_margin (a := 0.59) (b := 0.64) (U := 0.743) (S := 0.80741)
    · norm_num
    · exact (lt_of_not_ge h7).le
    · exact h8
    · norm_num
    · norm_num
    · exact G_test_bound (by norm_num) (lt_of_not_ge h7).le hx (by norm_num) hp certificate_059
    · norm_num
    · norm_num
    · norm_num
  apply row_margin (a := 0.64) (b := (2/3)) (U := 0.73) (S := 0.76838)
  · norm_num
  · exact (lt_of_not_ge h8).le
  · exact hrcap
  · norm_num
  · norm_num
  · exact G_test_bound (by norm_num) (lt_of_not_ge h8).le hx (by norm_num) hp certificate_064
  · norm_num
  · norm_num
  · norm_num

lemma linear_quadratic_of_loss {r x : ℝ} (hr : 0 < r) (hrcap : r ≤ 2/3) (hx : 0 ≤ x)
    (hc : (9/(8*Real.pi))*r^2/(1+Real.sqrt (1-r^2)) ≤ loss x) :
    0.415*r+0.15*r^2 < p x := by
  let P₀ := (0.415+0.15*r)*r
  have hP₀ : 0 < P₀ := by dsimp [P₀]; positivity
  have hP₀h : P₀ ≤ 1/2 := by dsimp [P₀]; nlinarith only [hr,hrcap]
  obtain ⟨y,hy,hPy⟩ := exists_p hP₀ hP₀h
  have ht := test_probability hr hrcap hy hPy
  have ht' := mul_lt_mul_of_pos_right ht (sq_pos_of_pos hr)
  have htest : loss y < (9/(8*Real.pi))*r^2/(1+Real.sqrt (1-r^2)) := by
    unfold loss
    rw [hPy]
    dsimp [P₀] at *
    calc
      _ = (0.415+0.15*r)^2*G y*r^2 := by ring
      _ < (9/(8*Real.pi))/(1+Real.sqrt (1-r^2))*r^2 := ht'
      _ = _ := by ring
  by_contra! hh
  have hpx : p x ≤ p y := by rw [hPy]; dsimp [P₀]; nlinarith only [hh]
  have hyx : y ≤ x := by
    by_contra! hgt
    have hd : StrictAnti p := strictAnti_of_hasDerivAt_neg (fun z => hasDerivAt_p z)
      (fun z => mul_neg_of_neg_of_pos (by linarith [gaussianConst_tight.1]) (Real.exp_pos _))
    exact (not_lt_of_ge hpx) (hd hgt)
  have hh' := loss_antitone hy hx hyx
  exact (not_lt_of_ge (hc.trans hh')) htest

end GaussianPropeller.ProbabilityBounds

end OAI
