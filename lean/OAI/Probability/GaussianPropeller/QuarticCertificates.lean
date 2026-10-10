import OAI.Probability.GaussianPropeller.FourReduction

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
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal
open Metric
open MeasureTheory ProbabilityTheory Set
open scoped RealInnerProductSpace ENNReal

namespace GaussianPropeller.FourCertificates
open OneCell ProbabilityBounds Mills Taylor

lemma loss_bound {x pu gu : ℝ} (hx:0≤x) (hp:p x≤pu) (hg:G x≤gu) : loss x≤pu^2*gu := by
  have hp0 := p_pos x
  have hg0 := G_nonneg hx
  have hsq : (p x)^2≤pu^2 := sq_le_sq₀ hp0.le (hp0.le.trans hp) |>.mpr hp
  exact (mul_le_mul_of_nonneg_right hsq hg0).trans (mul_le_mul_of_nonneg_left hg (sq_nonneg pu))

lemma loss_row {r x lo q v u : ℝ} (hlo:0≤lo) (hr:lo≤r) (hx:0≤x)
    (hq:0≤q) (hv:0≤v) (hs:1-(4/3:ℝ)*lo^2≤v^2)
    (hnum : u*(1+v) < (9/(8*(31416/10000:ℝ)))*lo^2)
    (hL:loss q≤u) (hP:p x≤p q)
    (h : (9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : False := by
  have hC : (9/(8*(31416/10000:ℝ))) ≤ 9/(8*Real.pi) := by
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    have hh := Real.pi_lt_d6
    linarith only [hh]
  have hrr : lo^2≤r^2 := sq_le_sq₀ hlo (hlo.trans hr) |>.mpr hr
  have hsv : Real.sqrt (1-(4/3:ℝ)*r^2)≤v := Real.sqrt_le_iff.mpr ⟨hv,by nlinarith only [hs,hrr]⟩
  have hxq : q≤x := by
    by_contra hh
    have hxq : x<q := lt_of_not_ge hh
    have hpstrict : p q<p x := by
      apply strictAnti_of_deriv_neg (fun y => ?_) hxq
      rw [(hasDerivAt_p y).deriv]
      have hc : 0<gaussianConst := by dsimp [gaussianConst]; positivity
      exact mul_neg_of_neg_of_pos (neg_neg_of_pos hc) (Real.exp_pos _)
    linarith only [hpstrict,hP]
  have hlxu := (loss_antitone hq hx hxq).trans hL
  have hh := (div_le_iff₀ (show 0<1+Real.sqrt (1-(4/3:ℝ)*r^2) by positivity)).mp (h.trans hlxu)
  have hl0 : 0 ≤ loss q := by unfold loss; exact mul_nonneg (sq_nonneg _) (G_nonneg hq)
  have hu : 0≤u := hl0.trans hL
  have hm := mul_le_mul_of_nonneg_left hsv hu
  have hc := mul_le_mul hC hrr (sq_nonneg lo) (by positivity : (0:ℝ)≤9/(8*Real.pi))
  nlinarith only [hnum,hh,hm,hc]

noncomputable def quartic (r:ℝ) := (3/5:ℝ)*r^4+(237/500:ℝ)*r^2+(3679/40000:ℝ)
noncomputable def small (r:ℝ) := (217/500:ℝ)*r+(3/20:ℝ)*r^2
noncomputable def large (r:ℝ) := (13/20:ℝ)*r^2+(9/100:ℝ)

lemma quartic_mono : MonotoneOn quartic (Ici 0) := by
  intro a ha b hb hab
  have h2:=pow_le_pow_left₀ ha hab 2
  have h4:=pow_le_pow_left₀ ha hab 4
  unfold quartic; linarith only [h2,h4]
lemma small_mono : MonotoneOn small (Ici 0) := by
  intro a ha b hb hab
  have h2:=pow_le_pow_left₀ ha hab 2
  unfold small; linarith only [h2,hab]
lemma large_mono : MonotoneOn large (Ici 0) := by
  intro a ha b hb hab
  have h2:=pow_le_pow_left₀ ha hab 2
  unfold large; linarith only [h2]

lemma quartic_0 {r x:ℝ} (hr:r∈Icc (147/500:ℝ) (251/840:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : quartic r < p x := by
  by_contra hn
  have hP : p x ≤ quartic (251/840:ℝ) := (le_of_not_gt hn).trans (quartic_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (21689/20000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (21689/20000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : quartic (251/840:ℝ) ≤ p (21689/20000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [quartic,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (21689/20000:ℝ)≤(27817/200000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (21689/20000:ℝ)≤(1593231/1000000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (21689/20000:ℝ)≤(405303/500000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(147/500:ℝ)) (q:=(21689/20000:ℝ)) (v:=(940613/1000000:ℝ))
    (u:=(27817/200000:ℝ)^2*(405303/500000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma quartic_1 {r x:ℝ} (hr:r∈Icc (251/840:ℝ) (797/2625:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : quartic r < p x := by
  by_contra hn
  have hP : p x ≤ quartic (797/2625:ℝ) := (le_of_not_gt hn).trans (quartic_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (21537/20000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (21537/20000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : quartic (797/2625:ℝ) ≤ p (21537/20000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [quartic,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (21537/20000:ℝ)≤(17597/125000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (21537/20000:ℝ)≤(793537/500000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (21537/20000:ℝ)≤(202441/250000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(251/840:ℝ)) (q:=(21537/20000:ℝ)) (v:=(93859/100000:ℝ))
    (u:=(17597/125000:ℝ)^2*(202441/250000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma quartic_2 {r x:ℝ} (hr:r∈Icc (797/2625:ℝ) (2159/7000:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : quartic r < p x := by
  by_contra hn
  have hP : p x ≤ quartic (2159/7000:ℝ) := (le_of_not_gt hn).trans (quartic_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (26729/25000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (26729/25000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : quartic (2159/7000:ℝ) ≤ p (26729/25000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [quartic,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (26729/25000:ℝ)≤(142501/1000000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (26729/25000:ℝ)≤(395213/250000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (26729/25000:ℝ)≤(80891/100000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(797/2625:ℝ)) (q:=(26729/25000:ℝ)) (v:=(93653/100000:ℝ))
    (u:=(142501/1000000:ℝ)^2*(80891/100000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma quartic_3 {r x:ℝ} (hr:r∈Icc (2159/7000:ℝ) (3289/10500:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : quartic r < p x := by
  by_contra hn
  have hP : p x ≤ quartic (3289/10500:ℝ) := (le_of_not_gt hn).trans (quartic_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (13267/12500:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (13267/12500:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : quartic (3289/10500:ℝ) ≤ p (13267/12500:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [quartic,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (13267/12500:ℝ)≤(72133/500000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (13267/12500:ℝ)≤(787273/500000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (13267/12500:ℝ)≤(161607/200000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(2159/7000:ℝ)) (q:=(13267/12500:ℝ)) (v:=(29201/31250:ℝ))
    (u:=(72133/500000:ℝ)^2*(161607/200000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma quartic_4 {r x:ℝ} (hr:r∈Icc (3289/10500:ℝ) (6679/21000:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : quartic r < p x := by
  by_contra hn
  have hP : p x ≤ quartic (6679/21000:ℝ) := (le_of_not_gt hn).trans (quartic_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (52673/50000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (52673/50000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : quartic (6679/21000:ℝ) ≤ p (52673/50000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [quartic,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (52673/50000:ℝ)≤(36517/250000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (52673/50000:ℝ)≤(1568167/1000000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (52673/50000:ℝ)≤(807147/1000000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(3289/10500:ℝ)) (q:=(52673/50000:ℝ)) (v:=(932297/1000000:ℝ))
    (u:=(36517/250000:ℝ)^2*(807147/1000000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma quartic_5 {r x:ℝ} (hr:r∈Icc (6679/21000:ℝ) (113/350:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : quartic r < p x := by
  by_contra hn
  have hP : p x ≤ quartic (113/350:ℝ) := (le_of_not_gt hn).trans (quartic_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (52273/50000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (52273/50000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : quartic (113/350:ℝ) ≤ p (52273/50000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [quartic,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (52273/50000:ℝ)≤(36977/250000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (52273/50000:ℝ)≤(780857/500000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (52273/50000:ℝ)≤(403121/500000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(6679/21000:ℝ)) (q:=(52273/50000:ℝ)) (v:=(930123/1000000:ℝ))
    (u:=(36977/250000:ℝ)^2*(403121/500000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma quartic_6 {r x:ℝ} (hr:r∈Icc (113/350:ℝ) (983/3000:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : quartic r < p x := by
  by_contra hn
  have hP : p x ≤ quartic (983/3000:ℝ) := (le_of_not_gt hn).trans (quartic_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (20747/20000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (20747/20000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : quartic (983/3000:ℝ) ≤ p (20747/20000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [quartic,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (20747/20000:ℝ)≤(149789/1000000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (20747/20000:ℝ)≤(77759/50000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (20747/20000:ℝ)≤(805319/1000000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(113/350:ℝ)) (q:=(20747/20000:ℝ)) (v:=(927911/1000000:ℝ))
    (u:=(149789/1000000:ℝ)^2*(805319/1000000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma quartic_7 {r x:ℝ} (hr:r∈Icc (983/3000:ℝ) (3491/10500:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : quartic r < p x := by
  by_contra hn
  have hP : p x ≤ quartic (3491/10500:ℝ) := (le_of_not_gt hn).trans (quartic_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (51457/50000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (51457/50000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : quartic (3491/10500:ℝ) ≤ p (51457/50000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [quartic,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (51457/50000:ℝ)≤(151709/1000000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (51457/50000:ℝ)≤(1548573/1000000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (51457/50000:ℝ)≤(40219/50000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(983/3000:ℝ)) (q:=(51457/50000:ℝ)) (v:=(46283/50000:ℝ))
    (u:=(151709/1000000:ℝ)^2*(40219/50000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma quartic_8 {r x:ℝ} (hr:r∈Icc (3491/10500:ℝ) (2361/7000:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : quartic r < p x := by
  by_contra hn
  have hP : p x ≤ quartic (2361/7000:ℝ) := (le_of_not_gt hn).trans (quartic_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (102083/100000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (102083/100000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : quartic (2361/7000:ℝ) ≤ p (102083/100000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [quartic,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (102083/100000:ℝ)≤(15367/100000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (102083/100000:ℝ)≤(770947/500000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (102083/100000:ℝ)≤(401713/500000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(3491/10500:ℝ)) (q:=(102083/100000:ℝ)) (v:=(923371/1000000:ℝ))
    (u:=(15367/100000:ℝ)^2*(401713/500000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma quartic_9 {r x:ℝ} (hr:r∈Icc (2361/7000:ℝ) (898/2625:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : quartic r < p x := by
  by_contra hn
  have hP : p x ≤ quartic (898/2625:ℝ) := (le_of_not_gt hn).trans (quartic_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (50621/50000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (50621/50000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : quartic (898/2625:ℝ) ≤ p (50621/50000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [quartic,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (50621/50000:ℝ)≤(155671/1000000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (50621/50000:ℝ)≤(767571/500000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (50621/50000:ℝ)≤(802453/1000000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(2361/7000:ℝ)) (q:=(50621/50000:ℝ)) (v:=(460521/500000:ℝ))
    (u:=(155671/1000000:ℝ)^2*(802453/1000000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma quartic_10 {r x:ℝ} (hr:r∈Icc (898/2625:ℝ) (1457/4200:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : quartic r < p x := by
  by_contra hn
  have hP : p x ≤ quartic (1457/4200:ℝ) := (le_of_not_gt hn).trans (quartic_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (100391/100000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (100391/100000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : quartic (1457/4200:ℝ) ≤ p (100391/100000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [quartic,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (100391/100000:ℝ)≤(157713/1000000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (100391/100000:ℝ)≤(764159/500000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (100391/100000:ℝ)≤(801463/1000000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(898/2625:ℝ)) (q:=(100391/100000:ℝ)) (v:=(459337/500000:ℝ))
    (u:=(157713/1000000:ℝ)^2*(801463/1000000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma quartic_11 {r x:ℝ} (hr:r∈Icc (1457/4200:ℝ) (1231/3500:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : quartic r < p x := by
  by_contra hn
  have hP : p x ≤ quartic (1231/3500:ℝ) := (le_of_not_gt hn).trans (quartic_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (9953/10000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (9953/10000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : quartic (1231/3500:ℝ) ≤ p (9953/10000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [quartic,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (9953/10000:ℝ)≤(79899/500000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (9953/10000:ℝ)≤(1521423/1000000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (9953/10000:ℝ)≤(100057/125000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(1457/4200:ℝ)) (q:=(9953/10000:ℝ)) (v:=(458133/500000:ℝ))
    (u:=(79899/500000:ℝ)^2*(100057/125000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma quartic_12 {r x:ℝ} (hr:r∈Icc (1231/3500:ℝ) (7487/21000:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : quartic r < p x := by
  by_contra hn
  have hP : p x ≤ quartic (7487/21000:ℝ) := (le_of_not_gt hn).trans (quartic_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (98659/100000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (98659/100000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : quartic (7487/21000:ℝ) ≤ p (98659/100000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [quartic,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (98659/100000:ℝ)≤(40481/250000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (98659/100000:ℝ)≤(189307/125000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (98659/100000:ℝ)≤(79943/100000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(1231/3500:ℝ)) (q:=(98659/100000:ℝ)) (v:=(456909/500000:ℝ))
    (u:=(40481/250000:ℝ)^2*(79943/100000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma quartic_13 {r x:ℝ} (hr:r∈Icc (7487/21000:ℝ) (271/750:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : quartic r < p x := by
  by_contra hn
  have hP : p x ≤ quartic (271/750:ℝ) := (le_of_not_gt hn).trans (quartic_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (97777/100000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (97777/100000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : quartic (271/750:ℝ) ≤ p (97777/100000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [quartic,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (97777/100000:ℝ)≤(164097/1000000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (97777/100000:ℝ)≤(1507411/1000000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (97777/100000:ℝ)≤(798387/1000000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(7487/21000:ℝ)) (q:=(97777/100000:ℝ)) (v:=(91133/100000:ℝ))
    (u:=(164097/1000000:ℝ)^2*(798387/1000000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma quartic_14 {r x:ℝ} (hr:r∈Icc (271/750:ℝ) (2563/7000:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : quartic r < p x := by
  by_contra hn
  have hP : p x ≤ quartic (2563/7000:ℝ) := (le_of_not_gt hn).trans (quartic_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (48443/50000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (48443/50000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : quartic (2563/7000:ℝ) ≤ p (48443/50000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [quartic,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (48443/50000:ℝ)≤(16631/100000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (48443/50000:ℝ)≤(1500303/1000000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (48443/50000:ℝ)≤(398663/500000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(271/750:ℝ)) (q:=(48443/50000:ℝ)) (v:=(908801/1000000:ℝ))
    (u:=(16631/100000:ℝ)^2*(398663/500000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma quartic_15 {r x:ℝ} (hr:r∈Icc (2563/7000:ℝ) (779/2100:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : quartic r < p x := by
  by_contra hn
  have hP : p x ≤ quartic (779/2100:ℝ) := (le_of_not_gt hn).trans (quartic_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (19197/20000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (19197/20000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : quartic (779/2100:ℝ) ≤ p (19197/20000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [quartic,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (19197/20000:ℝ)≤(21071/125000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (19197/20000:ℝ)≤(2389/1600:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (19197/20000:ℝ)≤(796247/1000000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(2563/7000:ℝ)) (q:=(19197/20000:ℝ)) (v:=(90623/100000:ℝ))
    (u:=(21071/125000:ℝ)^2*(796247/1000000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma quartic_16 {r x:ℝ} (hr:r∈Icc (779/2100:ℝ) (7891/21000:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : quartic r < p x := by
  by_contra hn
  have hP : p x ≤ quartic (7891/21000:ℝ) := (le_of_not_gt hn).trans (quartic_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (47537/50000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (47537/50000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : quartic (7891/21000:ℝ) ≤ p (47537/50000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [quartic,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (47537/50000:ℝ)≤(170871/1000000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (47537/50000:ℝ)≤(1485877/1000000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (47537/50000:ℝ)≤(198787/250000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(779/2100:ℝ)) (q:=(47537/50000:ℝ)) (v:=(903619/1000000:ℝ))
    (u:=(170871/1000000:ℝ)^2*(198787/250000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma quartic_17 {r x:ℝ} (hr:r∈Icc (7891/21000:ℝ) (333/875:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : quartic r < p x := by
  by_contra hn
  have hP : p x ≤ quartic (333/875:ℝ) := (le_of_not_gt hn).trans (quartic_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (94153/100000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (94153/100000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : quartic (333/875:ℝ) ≤ p (94153/100000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [quartic,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (94153/100000:ℝ)≤(173219/1000000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (94153/100000:ℝ)≤(9241/6250:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (94153/100000:ℝ)≤(49627/62500:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(7891/21000:ℝ)) (q:=(94153/100000:ℝ)) (v:=(180193/200000:ℝ))
    (u:=(173219/1000000:ℝ)^2*(49627/62500:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma quartic_18 {r x:ℝ} (hr:r∈Icc (333/875:ℝ) (8093/21000:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : quartic r < p x := by
  by_contra hn
  have hP : p x ≤ quartic (8093/21000:ℝ) := (le_of_not_gt hn).trans (quartic_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (46611/50000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (46611/50000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : quartic (8093/21000:ℝ) ≤ p (46611/50000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [quartic,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (46611/50000:ℝ)≤(87807/500000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (46611/50000:ℝ)≤(1471173/1000000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (46611/50000:ℝ)≤(396447/500000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(333/875:ℝ)) (q:=(46611/50000:ℝ)) (v:=(898269/1000000:ℝ))
    (u:=(87807/500000:ℝ)^2*(396447/500000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma quartic_19 {r x:ℝ} (hr:r∈Icc (8093/21000:ℝ) (4097/10500:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : quartic r < p x := by
  by_contra hn
  have hP : p x ≤ quartic (4097/10500:ℝ) := (le_of_not_gt hn).trans (quartic_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (92281/100000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (92281/100000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : quartic (4097/10500:ℝ) ≤ p (92281/100000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [quartic,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (92281/100000:ℝ)≤(22257/125000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (92281/100000:ℝ)≤(1463719/1000000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (92281/100000:ℝ)≤(791739/1000000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(8093/21000:ℝ)) (q:=(92281/100000:ℝ)) (v:=(895531/1000000:ℝ))
    (u:=(22257/125000:ℝ)^2*(791739/1000000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma quartic_20 {r x:ℝ} (hr:r∈Icc (4097/10500:ℝ) (79/200:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : quartic r < p x := by
  by_contra hn
  have hP : p x ≤ quartic (79/200:ℝ) := (le_of_not_gt hn).trans (quartic_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (91331/100000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (91331/100000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : quartic (79/200:ℝ) ≤ p (91331/100000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [quartic,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (91331/100000:ℝ)≤(90271/500000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (91331/100000:ℝ)≤(364051/250000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (91331/100000:ℝ)≤(158113/200000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(4097/10500:ℝ)) (q:=(91331/100000:ℝ)) (v:=(3571/4000:ℝ))
    (u:=(90271/500000:ℝ)^2*(158113/200000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma quartic_of_loss {r x:ℝ} (hr:r∈Icc (147/500:ℝ) (79/200:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : quartic r < p x := by
  by_cases h0 : r≤(251/840:ℝ)
  · exact quartic_0 ⟨by linarith only [hr.1],h0⟩ hx hl
  by_cases h1 : r≤(797/2625:ℝ)
  · exact quartic_1 ⟨by linarith only [h0],h1⟩ hx hl
  by_cases h2 : r≤(2159/7000:ℝ)
  · exact quartic_2 ⟨by linarith only [h1],h2⟩ hx hl
  by_cases h3 : r≤(3289/10500:ℝ)
  · exact quartic_3 ⟨by linarith only [h2],h3⟩ hx hl
  by_cases h4 : r≤(6679/21000:ℝ)
  · exact quartic_4 ⟨by linarith only [h3],h4⟩ hx hl
  by_cases h5 : r≤(113/350:ℝ)
  · exact quartic_5 ⟨by linarith only [h4],h5⟩ hx hl
  by_cases h6 : r≤(983/3000:ℝ)
  · exact quartic_6 ⟨by linarith only [h5],h6⟩ hx hl
  by_cases h7 : r≤(3491/10500:ℝ)
  · exact quartic_7 ⟨by linarith only [h6],h7⟩ hx hl
  by_cases h8 : r≤(2361/7000:ℝ)
  · exact quartic_8 ⟨by linarith only [h7],h8⟩ hx hl
  by_cases h9 : r≤(898/2625:ℝ)
  · exact quartic_9 ⟨by linarith only [h8],h9⟩ hx hl
  by_cases h10 : r≤(1457/4200:ℝ)
  · exact quartic_10 ⟨by linarith only [h9],h10⟩ hx hl
  by_cases h11 : r≤(1231/3500:ℝ)
  · exact quartic_11 ⟨by linarith only [h10],h11⟩ hx hl
  by_cases h12 : r≤(7487/21000:ℝ)
  · exact quartic_12 ⟨by linarith only [h11],h12⟩ hx hl
  by_cases h13 : r≤(271/750:ℝ)
  · exact quartic_13 ⟨by linarith only [h12],h13⟩ hx hl
  by_cases h14 : r≤(2563/7000:ℝ)
  · exact quartic_14 ⟨by linarith only [h13],h14⟩ hx hl
  by_cases h15 : r≤(779/2100:ℝ)
  · exact quartic_15 ⟨by linarith only [h14],h15⟩ hx hl
  by_cases h16 : r≤(7891/21000:ℝ)
  · exact quartic_16 ⟨by linarith only [h15],h16⟩ hx hl
  by_cases h17 : r≤(333/875:ℝ)
  · exact quartic_17 ⟨by linarith only [h16],h17⟩ hx hl
  by_cases h18 : r≤(8093/21000:ℝ)
  · exact quartic_18 ⟨by linarith only [h17],h18⟩ hx hl
  by_cases h19 : r≤(4097/10500:ℝ)
  · exact quartic_19 ⟨by linarith only [h18],h19⟩ hx hl
  exact quartic_20 ⟨by linarith only [h19],hr.2⟩ hx hl

end GaussianPropeller.FourCertificates

end OAI
