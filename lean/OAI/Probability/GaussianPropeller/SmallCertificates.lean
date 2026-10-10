import OAI.Probability.GaussianPropeller.QuarticCertificates

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

lemma small_0 {r x:ℝ} (hr:r∈Icc (39/250:ℝ) (157/1000:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : small r < p x := by
  by_contra hn
  have hP : p x ≤ small (157/1000:ℝ) := (le_of_not_gt hn).trans (small_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (9139/6250:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (9139/6250:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : small (157/1000:ℝ) ≤ p (9139/6250:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [small,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (9139/6250:ℝ)≤(449/6250:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (9139/6250:ℝ)≤(953337/500000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (9139/6250:ℝ)≤(847391/1000000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(39/250:ℝ)) (q:=(9139/6250:ℝ)) (v:=(983643/1000000:ℝ))
    (u:=(449/6250:ℝ)^2*(847391/1000000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma small_1 {r x:ℝ} (hr:r∈Icc (157/1000:ℝ) (79/500:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : small r < p x := by
  by_contra hn
  have hP : p x ≤ small (79/500:ℝ) := (le_of_not_gt hn).trans (small_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (72937/50000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (72937/50000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : small (79/500:ℝ) ≤ p (72937/50000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [small,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (72937/50000:ℝ)≤(72321/1000000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (72937/50000:ℝ)≤(1903709/1000000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (72937/50000:ℝ)≤(211773/250000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(157/1000:ℝ)) (q:=(72937/50000:ℝ)) (v:=(983431/1000000:ℝ))
    (u:=(72321/1000000:ℝ)^2*(211773/250000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma small_2 {r x:ℝ} (hr:r∈Icc (79/500:ℝ) (159/1000:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : small r < p x := by
  by_contra hn
  have hP : p x ≤ small (159/1000:ℝ) := (le_of_not_gt hn).trans (small_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (5821/4000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (5821/4000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : small (159/1000:ℝ) ≤ p (5821/4000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [small,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (5821/4000:ℝ)≤(72803/1000000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (5821/4000:ℝ)≤(950377/500000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (5821/4000:ℝ)≤(423397/500000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(79/500:ℝ)) (q:=(5821/4000:ℝ)) (v:=(983217/1000000:ℝ))
    (u:=(72803/1000000:ℝ)^2*(423397/500000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma small_3 {r x:ℝ} (hr:r∈Icc (159/1000:ℝ) (4/25:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : small r < p x := by
  by_contra hn
  have hP : p x ≤ small (4/25:ℝ) := (le_of_not_gt hn).trans (small_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (72589/50000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (72589/50000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : small (4/25:ℝ) ≤ p (72589/50000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [small,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (72589/50000:ℝ)≤(18321/250000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (72589/50000:ℝ)≤(1897817/1000000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (72589/50000:ℝ)≤(846497/1000000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(159/1000:ℝ)) (q:=(72589/50000:ℝ)) (v:=(491501/500000:ℝ))
    (u:=(18321/250000:ℝ)^2*(846497/1000000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma small_4 {r x:ℝ} (hr:r∈Icc (4/25:ℝ) (161/1000:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : small r < p x := by
  by_contra hn
  have hP : p x ≤ small (161/1000:ℝ) := (le_of_not_gt hn).trans (small_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (4526/3125:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (4526/3125:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : small (161/1000:ℝ) ≤ p (4526/3125:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [small,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (4526/3125:ℝ)≤(36883/500000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (4526/3125:ℝ)≤(1894889/1000000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (4526/3125:ℝ)≤(846199/1000000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(4/25:ℝ)) (q:=(4526/3125:ℝ)) (v:=(491393/500000:ℝ))
    (u:=(36883/500000:ℝ)^2*(846199/1000000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma small_5 {r x:ℝ} (hr:r∈Icc (161/1000:ℝ) (81/500:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : small r < p x := by
  by_contra hn
  have hP : p x ≤ small (81/500:ℝ) := (le_of_not_gt hn).trans (small_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (144487/100000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (144487/100000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : small (81/500:ℝ) ≤ p (144487/100000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [small,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (144487/100000:ℝ)≤(297/4000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (144487/100000:ℝ)≤(189197/100000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (144487/100000:ℝ)≤(8459/10000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(161/1000:ℝ)) (q:=(144487/100000:ℝ)) (v:=(122821/125000:ℝ))
    (u:=(297/4000:ℝ)^2*(8459/10000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma small_6 {r x:ℝ} (hr:r∈Icc (81/500:ℝ) (163/1000:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : small r < p x := by
  by_contra hn
  have hP : p x ≤ small (163/1000:ℝ) := (le_of_not_gt hn).trans (small_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (28829/20000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (28829/20000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : small (163/1000:ℝ) ≤ p (28829/20000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [small,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (28829/20000:ℝ)≤(74731/1000000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (28829/20000:ℝ)≤(944539/500000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (28829/20000:ℝ)≤(169121/200000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(81/500:ℝ)) (q:=(28829/20000:ℝ)) (v:=(982349/1000000:ℝ))
    (u:=(74731/1000000:ℝ)^2*(169121/200000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma small_7 {r x:ℝ} (hr:r∈Icc (163/1000:ℝ) (41/250:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : small r < p x := by
  by_contra hn
  have hP : p x ≤ small (41/250:ℝ) := (le_of_not_gt hn).trans (small_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (143803/100000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (143803/100000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : small (41/250:ℝ) ≤ p (143803/100000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [small,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (143803/100000:ℝ)≤(15043/200000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (143803/100000:ℝ)≤(1886187/1000000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (143803/100000:ℝ)≤(211327/250000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(163/1000:ℝ)) (q:=(143803/100000:ℝ)) (v:=(61383/62500:ℝ))
    (u:=(15043/200000:ℝ)^2*(211327/250000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma small_8 {r x:ℝ} (hr:r∈Icc (41/250:ℝ) (33/200:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : small r < p x := by
  by_contra hn
  have hP : p x ≤ small (33/200:ℝ) := (le_of_not_gt hn).trans (small_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (143463/100000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (143463/100000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : small (33/200:ℝ) ≤ p (143463/100000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [small,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (143463/100000:ℝ)≤(75699/1000000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (143463/100000:ℝ)≤(941657/500000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (143463/100000:ℝ)≤(845013/1000000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(41/250:ℝ)) (q:=(143463/100000:ℝ)) (v:=(490953/500000:ℝ))
    (u:=(75699/1000000:ℝ)^2*(845013/1000000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma small_9 {r x:ℝ} (hr:r∈Icc (33/200:ℝ) (83/500:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : small r < p x := by
  by_contra hn
  have hP : p x ≤ small (83/500:ℝ) := (le_of_not_gt hn).trans (small_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (229/160:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (229/160:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : small (83/500:ℝ) ≤ p (229/160:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [small,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (229/160:ℝ)≤(38091/500000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (229/160:ℝ)≤(1880459/1000000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (229/160:ℝ)≤(10559/12500:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(33/200:ℝ)) (q:=(229/160:ℝ)) (v:=(981683/1000000:ℝ))
    (u:=(38091/500000:ℝ)^2*(10559/12500:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma small_10 {r x:ℝ} (hr:r∈Icc (83/500:ℝ) (167/1000:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : small r < p x := by
  by_contra hn
  have hP : p x ≤ small (167/1000:ℝ) := (le_of_not_gt hn).trans (small_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (35697/25000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (35697/25000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : small (167/1000:ℝ) ≤ p (35697/25000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [small,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (35697/25000:ℝ)≤(38333/500000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (35697/25000:ℝ)≤(1877613/1000000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (35697/25000:ℝ)≤(33777/40000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(83/500:ℝ)) (q:=(35697/25000:ℝ)) (v:=(490729/500000:ℝ))
    (u:=(38333/500000:ℝ)^2*(33777/40000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma small_11 {r x:ℝ} (hr:r∈Icc (167/1000:ℝ) (21/125:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : small r < p x := by
  by_contra hn
  have hP : p x ≤ small (21/125:ℝ) := (le_of_not_gt hn).trans (small_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (35613/25000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (35613/25000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : small (21/125:ℝ) ≤ p (35613/25000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [small,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (35613/25000:ℝ)≤(1543/20000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (35613/25000:ℝ)≤(234347/125000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (35613/25000:ℝ)≤(84413/100000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(167/1000:ℝ)) (q:=(35613/25000:ℝ)) (v:=(61327/62500:ℝ))
    (u:=(1543/20000:ℝ)^2*(84413/100000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma small_12 {r x:ℝ} (hr:r∈Icc (21/125:ℝ) (169/1000:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : small r < p x := by
  by_contra hn
  have hP : p x ≤ small (169/1000:ℝ) := (le_of_not_gt hn).trans (small_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (71059/50000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (71059/50000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : small (169/1000:ℝ) ≤ p (71059/50000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [small,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (71059/50000:ℝ)≤(15527/200000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (71059/50000:ℝ)≤(935979/500000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (71059/50000:ℝ)≤(421919/500000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(21/125:ℝ)) (q:=(71059/50000:ℝ)) (v:=(245251/250000:ℝ))
    (u:=(15527/200000:ℝ)^2*(421919/500000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma small_13 {r x:ℝ} (hr:r∈Icc (169/1000:ℝ) (17/100:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : small r < p x := by
  by_contra hn
  have hP : p x ≤ small (17/100:ℝ) := (le_of_not_gt hn).trans (small_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (28357/20000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (28357/20000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : small (17/100:ℝ) ≤ p (28357/20000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [small,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (28357/20000:ℝ)≤(1953/25000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (28357/20000:ℝ)≤(1869149/1000000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (28357/20000:ℝ)≤(421773/500000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(169/1000:ℝ)) (q:=(28357/20000:ℝ)) (v:=(39231/40000:ℝ))
    (u:=(1953/25000:ℝ)^2*(421773/500000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma small_14 {r x:ℝ} (hr:r∈Icc (17/100:ℝ) (171/1000:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : small r < p x := by
  by_contra hn
  have hP : p x ≤ small (171/1000:ℝ) := (le_of_not_gt hn).trans (small_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (70727/50000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (70727/50000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : small (171/1000:ℝ) ≤ p (70727/50000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [small,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (70727/50000:ℝ)≤(19651/250000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (70727/50000:ℝ)≤(933179/500000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (70727/50000:ℝ)≤(168651/200000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(17/100:ℝ)) (q:=(70727/50000:ℝ)) (v:=(196109/200000:ℝ))
    (u:=(19651/250000:ℝ)^2*(168651/200000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma small_15 {r x:ℝ} (hr:r∈Icc (171/1000:ℝ) (43/250:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : small r < p x := by
  by_contra hn
  have hP : p x ≤ small (43/250:ℝ) := (le_of_not_gt hn).trans (small_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (141123/100000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (141123/100000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : small (43/250:ℝ) ≤ p (141123/100000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [small,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (141123/100000:ℝ)≤(79091/1000000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (141123/100000:ℝ)≤(1863567/1000000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (141123/100000:ℝ)≤(842961/1000000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(171/1000:ℝ)) (q:=(141123/100000:ℝ)) (v:=(980313/1000000:ℝ))
    (u:=(79091/1000000:ℝ)^2*(842961/1000000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma small_16 {r x:ℝ} (hr:r∈Icc (43/250:ℝ) (173/1000:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : small r < p x := by
  by_contra hn
  have hP : p x ≤ small (173/1000:ℝ) := (le_of_not_gt hn).trans (small_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (28159/20000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (28159/20000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : small (173/1000:ℝ) ≤ p (28159/20000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [small,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (28159/20000:ℝ)≤(3183/40000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (28159/20000:ℝ)≤(1860803/1000000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (28159/20000:ℝ)≤(842671/1000000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(43/250:ℝ)) (q:=(28159/20000:ℝ)) (v:=(980079/1000000:ℝ))
    (u:=(3183/40000:ℝ)^2*(842671/1000000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma small_17 {r x:ℝ} (hr:r∈Icc (173/1000:ℝ) (87/500:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : small r < p x := by
  by_contra hn
  have hP : p x ≤ small (87/500:ℝ) := (le_of_not_gt hn).trans (small_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (140467/100000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (140467/100000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : small (87/500:ℝ) ≤ p (140467/100000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [small,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (140467/100000:ℝ)≤(40031/500000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (140467/100000:ℝ)≤(46451/25000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (140467/100000:ℝ)≤(42119/50000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(173/1000:ℝ)) (q:=(140467/100000:ℝ)) (v:=(195969/200000:ℝ))
    (u:=(40031/500000:ℝ)^2*(42119/50000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma small_18 {r x:ℝ} (hr:r∈Icc (87/500:ℝ) (7/40:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : small r < p x := by
  by_contra hn
  have hP : p x ≤ small (7/40:ℝ) := (le_of_not_gt hn).trans (small_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (140141/100000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (140141/100000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : small (7/40:ℝ) ≤ p (140141/100000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [small,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (140141/100000:ℝ)≤(20137/250000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (140141/100000:ℝ)≤(371059/200000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (140141/100000:ℝ)≤(842091/1000000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(87/500:ℝ)) (q:=(140141/100000:ℝ)) (v:=(979609/1000000:ℝ))
    (u:=(20137/250000:ℝ)^2*(842091/1000000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma small_19 {r x:ℝ} (hr:r∈Icc (7/40:ℝ) (22/125:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : small r < p x := by
  by_contra hn
  have hP : p x ≤ small (22/125:ℝ) := (le_of_not_gt hn).trans (small_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (17477/12500:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (17477/12500:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : small (22/125:ℝ) ≤ p (17477/12500:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [small,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (17477/12500:ℝ)≤(16207/200000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (17477/12500:ℝ)≤(1852559/1000000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (17477/12500:ℝ)≤(841801/1000000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(7/40:ℝ)) (q:=(17477/12500:ℝ)) (v:=(979371/1000000:ℝ))
    (u:=(16207/200000:ℝ)^2*(841801/1000000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma small_20 {r x:ℝ} (hr:r∈Icc (22/125:ℝ) (177/1000:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : small r < p x := by
  by_contra hn
  have hP : p x ≤ small (177/1000:ℝ) := (le_of_not_gt hn).trans (small_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (34873/25000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (34873/25000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : small (177/1000:ℝ) ≤ p (34873/25000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [small,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (34873/25000:ℝ)≤(40761/500000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (34873/25000:ℝ)≤(231229/125000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (34873/25000:ℝ)≤(841511/1000000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(22/125:ℝ)) (q:=(34873/25000:ℝ)) (v:=(244783/250000:ℝ))
    (u:=(40761/500000:ℝ)^2*(841511/1000000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma small_21 {r x:ℝ} (hr:r∈Icc (177/1000:ℝ) (89/500:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : small r < p x := by
  by_contra hn
  have hP : p x ≤ small (89/500:ℝ) := (le_of_not_gt hn).trans (small_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (13917/10000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (13917/10000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : small (89/500:ℝ) ≤ p (13917/10000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [small,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (13917/10000:ℝ)≤(82009/1000000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (13917/10000:ℝ)≤(1847123/1000000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (13917/10000:ℝ)≤(841223/1000000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(177/1000:ℝ)) (q:=(13917/10000:ℝ)) (v:=(244723/250000:ℝ))
    (u:=(82009/1000000:ℝ)^2*(841223/1000000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma small_22 {r x:ℝ} (hr:r∈Icc (89/500:ℝ) (179/1000:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : small r < p x := by
  by_contra hn
  have hP : p x ≤ small (179/1000:ℝ) := (le_of_not_gt hn).trans (small_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (138849/100000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (138849/100000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : small (179/1000:ℝ) ≤ p (138849/100000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [small,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (138849/100000:ℝ)≤(1289/15625:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (138849/100000:ℝ)≤(230553/125000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (138849/100000:ℝ)≤(105117/125000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(89/500:ℝ)) (q:=(138849/100000:ℝ)) (v:=(19573/20000:ℝ))
    (u:=(1289/15625:ℝ)^2*(105117/125000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma small_23 {r x:ℝ} (hr:r∈Icc (179/1000:ℝ) (9/50:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : small r < p x := by
  by_contra hn
  have hP : p x ≤ small (9/50:ℝ) := (le_of_not_gt hn).trans (small_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (138529/100000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (138529/100000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : small (9/50:ℝ) ≤ p (138529/100000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [small,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (138529/100000:ℝ)≤(10373/125000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (138529/100000:ℝ)≤(920867/500000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (138529/100000:ℝ)≤(840649/1000000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(179/1000:ℝ)) (q:=(138529/100000:ℝ)) (v:=(978407/1000000:ℝ))
    (u:=(10373/125000:ℝ)^2*(840649/1000000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma small_of_loss {r x:ℝ} (hr:r∈Icc (39/250:ℝ) (9/50:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : small r < p x := by
  by_cases h0 : r≤(157/1000:ℝ)
  · exact small_0 ⟨by linarith only [hr.1],h0⟩ hx hl
  by_cases h1 : r≤(79/500:ℝ)
  · exact small_1 ⟨by linarith only [h0],h1⟩ hx hl
  by_cases h2 : r≤(159/1000:ℝ)
  · exact small_2 ⟨by linarith only [h1],h2⟩ hx hl
  by_cases h3 : r≤(4/25:ℝ)
  · exact small_3 ⟨by linarith only [h2],h3⟩ hx hl
  by_cases h4 : r≤(161/1000:ℝ)
  · exact small_4 ⟨by linarith only [h3],h4⟩ hx hl
  by_cases h5 : r≤(81/500:ℝ)
  · exact small_5 ⟨by linarith only [h4],h5⟩ hx hl
  by_cases h6 : r≤(163/1000:ℝ)
  · exact small_6 ⟨by linarith only [h5],h6⟩ hx hl
  by_cases h7 : r≤(41/250:ℝ)
  · exact small_7 ⟨by linarith only [h6],h7⟩ hx hl
  by_cases h8 : r≤(33/200:ℝ)
  · exact small_8 ⟨by linarith only [h7],h8⟩ hx hl
  by_cases h9 : r≤(83/500:ℝ)
  · exact small_9 ⟨by linarith only [h8],h9⟩ hx hl
  by_cases h10 : r≤(167/1000:ℝ)
  · exact small_10 ⟨by linarith only [h9],h10⟩ hx hl
  by_cases h11 : r≤(21/125:ℝ)
  · exact small_11 ⟨by linarith only [h10],h11⟩ hx hl
  by_cases h12 : r≤(169/1000:ℝ)
  · exact small_12 ⟨by linarith only [h11],h12⟩ hx hl
  by_cases h13 : r≤(17/100:ℝ)
  · exact small_13 ⟨by linarith only [h12],h13⟩ hx hl
  by_cases h14 : r≤(171/1000:ℝ)
  · exact small_14 ⟨by linarith only [h13],h14⟩ hx hl
  by_cases h15 : r≤(43/250:ℝ)
  · exact small_15 ⟨by linarith only [h14],h15⟩ hx hl
  by_cases h16 : r≤(173/1000:ℝ)
  · exact small_16 ⟨by linarith only [h15],h16⟩ hx hl
  by_cases h17 : r≤(87/500:ℝ)
  · exact small_17 ⟨by linarith only [h16],h17⟩ hx hl
  by_cases h18 : r≤(7/40:ℝ)
  · exact small_18 ⟨by linarith only [h17],h18⟩ hx hl
  by_cases h19 : r≤(22/125:ℝ)
  · exact small_19 ⟨by linarith only [h18],h19⟩ hx hl
  by_cases h20 : r≤(177/1000:ℝ)
  · exact small_20 ⟨by linarith only [h19],h20⟩ hx hl
  by_cases h21 : r≤(89/500:ℝ)
  · exact small_21 ⟨by linarith only [h20],h21⟩ hx hl
  by_cases h22 : r≤(179/1000:ℝ)
  · exact small_22 ⟨by linarith only [h21],h22⟩ hx hl
  exact small_23 ⟨by linarith only [h22],hr.2⟩ hx hl

end GaussianPropeller.FourCertificates

end OAI
