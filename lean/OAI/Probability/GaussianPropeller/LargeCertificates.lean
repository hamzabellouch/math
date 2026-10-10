import OAI.Probability.GaussianPropeller.SmallCertificates

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

lemma large_0 {r x:ℝ} (hr:r∈Icc (2/5:ℝ) (161/400:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : large r < p x := by
  by_contra hn
  have hP : p x ≤ large (161/400:ℝ) := (le_of_not_gt hn).trans (large_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (1717/2000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (1717/2000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : large (161/400:ℝ) ≤ p (1717/2000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [large,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (1717/2000:ℝ)≤(195311/1000000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (1717/2000:ℝ)≤(1413067/1000000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (1717/2000:ℝ)≤(783641/1000000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(2/5:ℝ)) (q:=(1717/2000:ℝ)) (v:=(886943/1000000:ℝ))
    (u:=(195311/1000000:ℝ)^2*(783641/1000000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma large_1 {r x:ℝ} (hr:r∈Icc (161/400:ℝ) (81/200:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : large r < p x := by
  by_contra hn
  have hP : p x ≤ large (81/200:ℝ) := (le_of_not_gt hn).trans (large_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (683/800:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (683/800:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : large (81/200:ℝ) ≤ p (683/800:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [large,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (683/800:ℝ)≤(12289/62500:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (683/800:ℝ)≤(1409347/1000000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (683/800:ℝ)≤(783029/1000000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(161/400:ℝ)) (q:=(683/800:ℝ)) (v:=(442717/500000:ℝ))
    (u:=(12289/62500:ℝ)^2*(783029/1000000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma large_2 {r x:ℝ} (hr:r∈Icc (81/200:ℝ) (163/400:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : large r < p x := by
  by_contra hn
  have hP : p x ≤ large (163/400:ℝ) := (le_of_not_gt hn).trans (large_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (849/1000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (849/1000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : large (163/400:ℝ) ≤ p (849/1000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [large,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (849/1000:ℝ)≤(197943/1000000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (849/1000:ℝ)≤(1405629/1000000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (849/1000:ℝ)≤(391207/500000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(81/200:ℝ)) (q:=(849/1000:ℝ)) (v:=(110489/125000:ℝ))
    (u:=(197943/1000000:ℝ)^2*(391207/500000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma large_3 {r x:ℝ} (hr:r∈Icc (163/400:ℝ) (41/100:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : large r < p x := by
  by_contra hn
  have hP : p x ≤ large (41/100:ℝ) := (le_of_not_gt hn).trans (large_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (84423/100000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (84423/100000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : large (41/100:ℝ) ≤ p (84423/100000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [large,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (84423/100000:ℝ)≤(199273/1000000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (84423/100000:ℝ)≤(1401899/1000000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (84423/100000:ℝ)≤(195449/250000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(163/400:ℝ)) (q:=(84423/100000:ℝ)) (v:=(882379/1000000:ℝ))
    (u:=(199273/1000000:ℝ)^2*(195449/250000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma large_4 {r x:ℝ} (hr:r∈Icc (41/100:ℝ) (33/80:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : large r < p x := by
  by_contra hn
  have hP : p x ≤ large (33/80:ℝ) := (le_of_not_gt hn).trans (large_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (41973/50000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (41973/50000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : large (33/80:ℝ) ≤ p (41973/50000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [large,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (41973/50000:ℝ)≤(6269/31250:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (41973/50000:ℝ)≤(349543/250000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (41973/50000:ℝ)≤(97647/125000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(41/100:ℝ)) (q:=(41973/50000:ℝ)) (v:=(880833/1000000:ℝ))
    (u:=(6269/31250:ℝ)^2*(97647/125000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma large_5 {r x:ℝ} (hr:r∈Icc (33/80:ℝ) (83/200:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : large r < p x := by
  by_contra hn
  have hP : p x ≤ large (83/200:ℝ) := (le_of_not_gt hn).trans (large_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (83467/100000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (83467/100000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : large (83/200:ℝ) ≤ p (83467/100000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [large,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (83467/100000:ℝ)≤(100977/500000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (83467/100000:ℝ)≤(21788/15625:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (83467/100000:ℝ)≤(780551/1000000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(33/80:ℝ)) (q:=(83467/100000:ℝ)) (v:=(219819/250000:ℝ))
    (u:=(100977/500000:ℝ)^2*(780551/1000000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma large_6 {r x:ℝ} (hr:r∈Icc (83/200:ℝ) (167/400:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : large r < p x := by
  by_contra hn
  have hP : p x ≤ large (167/400:ℝ) := (le_of_not_gt hn).trans (large_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (20747/25000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (20747/25000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : large (167/400:ℝ) ≤ p (20747/25000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [large,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (20747/25000:ℝ)≤(101653/500000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (20747/25000:ℝ)≤(278139/200000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (20747/25000:ℝ)≤(779923/1000000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(83/200:ℝ)) (q:=(20747/25000:ℝ)) (v:=(438853/500000:ℝ))
    (u:=(101653/500000:ℝ)^2*(779923/1000000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma large_7 {r x:ℝ} (hr:r∈Icc (167/400:ℝ) (21/50:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : large r < p x := by
  by_contra hn
  have hP : p x ≤ large (21/50:ℝ) := (le_of_not_gt hn).trans (large_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (20627/25000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (20627/25000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : large (21/50:ℝ) ≤ p (20627/25000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [large,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (20627/25000:ℝ)≤(102333/500000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (20627/25000:ℝ)≤(1386953/1000000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (20627/25000:ℝ)≤(194823/250000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(167/400:ℝ)) (q:=(20627/25000:ℝ)) (v:=(219031/250000:ℝ))
    (u:=(102333/500000:ℝ)^2*(194823/250000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma large_8 {r x:ℝ} (hr:r∈Icc (21/50:ℝ) (169/400:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : large r < p x := by
  by_contra hn
  have hP : p x ≤ large (169/400:ℝ) := (le_of_not_gt hn).trans (large_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (41013/50000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (41013/50000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : large (169/400:ℝ) ≤ p (41013/50000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [large,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (41013/50000:ℝ)≤(51509/250000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (41013/50000:ℝ)≤(1383199/1000000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (41013/50000:ℝ)≤(778657/1000000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(21/50:ℝ)) (q:=(41013/50000:ℝ)) (v:=(874529/1000000:ℝ))
    (u:=(51509/250000:ℝ)^2*(778657/1000000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma large_9 {r x:ℝ} (hr:r∈Icc (169/400:ℝ) (17/40:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : large r < p x := by
  by_contra hn
  have hP : p x ≤ large (17/40:ℝ) := (le_of_not_gt hn).trans (large_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (10193/12500:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (10193/12500:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : large (17/40:ℝ) ≤ p (10193/12500:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [large,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (10193/12500:ℝ)≤(207413/1000000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (10193/12500:ℝ)≤(172431/125000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (10193/12500:ℝ)≤(38901/50000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(169/400:ℝ)) (q:=(10193/12500:ℝ)) (v:=(436461/500000:ℝ))
    (u:=(207413/1000000:ℝ)^2*(38901/50000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma large_10 {r x:ℝ} (hr:r∈Icc (17/40:ℝ) (171/400:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : large r < p x := by
  by_contra hn
  have hP : p x ≤ large (171/400:ℝ) := (le_of_not_gt hn).trans (large_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (81061/100000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (81061/100000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : large (171/400:ℝ) ≤ p (81061/100000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [large,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (81061/100000:ℝ)≤(208797/1000000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (81061/100000:ℝ)≤(343923/250000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (81061/100000:ℝ)≤(777379/1000000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(17/40:ℝ)) (q:=(81061/100000:ℝ)) (v:=(435651/500000:ℝ))
    (u:=(208797/1000000:ℝ)^2*(777379/1000000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma large_11 {r x:ℝ} (hr:r∈Icc (171/400:ℝ) (43/100:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : large r < p x := by
  by_contra hn
  have hP : p x ≤ large (43/100:ℝ) := (le_of_not_gt hn).trans (large_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (2518/3125:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (2518/3125:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : large (43/100:ℝ) ≤ p (2518/3125:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [large,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (2518/3125:ℝ)≤(210193/1000000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (2518/3125:ℝ)≤(342981/250000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (2518/3125:ℝ)≤(388367/500000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(171/400:ℝ)) (q:=(2518/3125:ℝ)) (v:=(86967/100000:ℝ))
    (u:=(210193/1000000:ℝ)^2*(388367/500000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma large_12 {r x:ℝ} (hr:r∈Icc (43/100:ℝ) (173/400:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : large r < p x := by
  by_contra hn
  have hP : p x ≤ large (173/400:ℝ) := (le_of_not_gt hn).trans (large_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (80091/100000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (80091/100000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : large (173/400:ℝ) ≤ p (80091/100000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [large,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (80091/100000:ℝ)≤(105797/500000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (80091/100000:ℝ)≤(1368159/1000000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (80091/100000:ℝ)≤(776087/1000000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(43/100:ℝ)) (q:=(80091/100000:ℝ)) (v:=(34721/40000:ℝ))
    (u:=(105797/500000:ℝ)^2*(776087/1000000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma large_13 {r x:ℝ} (hr:r∈Icc (173/400:ℝ) (87/200:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : large r < p x := by
  by_contra hn
  have hP : p x ≤ large (87/200:ℝ) := (le_of_not_gt hn).trans (large_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (15921/20000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (15921/20000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : large (87/200:ℝ) ≤ p (15921/20000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [large,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (15921/20000:ℝ)≤(53251/250000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (15921/20000:ℝ)≤(1364389/1000000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (15921/20000:ℝ)≤(193859/250000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(173/400:ℝ)) (q:=(15921/20000:ℝ)) (v:=(866367/1000000:ℝ))
    (u:=(53251/250000:ℝ)^2*(193859/250000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma large_14 {r x:ℝ} (hr:r∈Icc (87/200:ℝ) (7/16:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : large r < p x := by
  by_contra hn
  have hP : p x ≤ large (7/16:ℝ) := (le_of_not_gt hn).trans (large_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (39559/50000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (39559/50000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : large (7/16:ℝ) ≤ p (39559/50000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [large,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (39559/50000:ℝ)≤(107211/500000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (39559/50000:ℝ)≤(272123/200000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (39559/50000:ℝ)≤(387391/500000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(87/200:ℝ)) (q:=(39559/50000:ℝ)) (v:=(864697/1000000:ℝ))
    (u:=(107211/500000:ℝ)^2*(387391/500000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma large_15 {r x:ℝ} (hr:r∈Icc (7/16:ℝ) (11/25:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : large r < p x := by
  by_contra hn
  have hP : p x ≤ large (11/25:ℝ) := (le_of_not_gt hn).trans (large_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (78631/100000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (78631/100000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : large (11/25:ℝ) ≤ p (78631/100000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [large,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (78631/100000:ℝ)≤(43169/200000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (78631/100000:ℝ)≤(339211/250000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (78631/100000:ℝ)≤(387063/500000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(7/16:ℝ)) (q:=(78631/100000:ℝ)) (v:=(431507/500000:ℝ))
    (u:=(43169/200000:ℝ)^2*(387063/500000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma large_16 {r x:ℝ} (hr:r∈Icc (11/25:ℝ) (177/400:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : large r < p x := by
  by_contra hn
  have hP : p x ≤ large (177/400:ℝ) := (le_of_not_gt hn).trans (large_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (39071/50000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (39071/50000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : large (177/400:ℝ) ≤ p (39071/50000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [large,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (39071/50000:ℝ)≤(679/3125:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (39071/50000:ℝ)≤(67653/50000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (39071/50000:ℝ)≤(96683/125000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(11/25:ℝ)) (q:=(39071/50000:ℝ)) (v:=(861317/1000000:ℝ))
    (u:=(679/3125:ℝ)^2*(96683/125000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma large_17 {r x:ℝ} (hr:r∈Icc (177/400:ℝ) (89/200:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : large r < p x := by
  by_contra hn
  have hP : p x ≤ large (89/200:ℝ) := (le_of_not_gt hn).trans (large_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (19413/25000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (19413/25000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : large (89/200:ℝ) ≤ p (19413/25000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [large,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (19413/25000:ℝ)≤(54681/250000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (19413/25000:ℝ)≤(168659/125000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (19413/25000:ℝ)≤(772799/1000000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(177/400:ℝ)) (q:=(19413/25000:ℝ)) (v:=(107451/125000:ℝ))
    (u:=(54681/250000:ℝ)^2*(772799/1000000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma large_18 {r x:ℝ} (hr:r∈Icc (89/200:ℝ) (179/400:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : large r < p x := by
  by_contra hn
  have hP : p x ≤ large (179/400:ℝ) := (le_of_not_gt hn).trans (large_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (38581/50000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (38581/50000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : large (179/400:ℝ) ≤ p (38581/50000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [large,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (38581/50000:ℝ)≤(55043/250000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (38581/50000:ℝ)≤(84093/62500:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (38581/50000:ℝ)≤(772133/1000000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(89/200:ℝ)) (q:=(38581/50000:ℝ)) (v:=(171577/200000:ℝ))
    (u:=(55043/250000:ℝ)^2*(772133/1000000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma large_19 {r x:ℝ} (hr:r∈Icc (179/400:ℝ) (9/20:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : large r < p x := by
  by_contra hn
  have hP : p x ≤ large (9/20:ℝ) := (le_of_not_gt hn).trans (large_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (7667/10000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (7667/10000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : large (9/20:ℝ) ≤ p (7667/10000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [large,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (7667/10000:ℝ)≤(3463/15625:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (7667/10000:ℝ)≤(1341691/1000000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (7667/10000:ℝ)≤(771461/1000000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(179/400:ℝ)) (q:=(7667/10000:ℝ)) (v:=(17123/20000:ℝ))
    (u:=(3463/15625:ℝ)^2*(771461/1000000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma large_20 {r x:ℝ} (hr:r∈Icc (9/20:ℝ) (181/400:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : large r < p x := by
  by_contra hn
  have hP : p x ≤ large (181/400:ℝ) := (le_of_not_gt hn).trans (large_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (38089/50000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (38089/50000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : large (181/400:ℝ) ≤ p (38089/50000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [large,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (38089/50000:ℝ)≤(111549/500000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (38089/50000:ℝ)≤(668949/500000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (38089/50000:ℝ)≤(192697/250000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(9/20:ℝ)) (q:=(38089/50000:ℝ)) (v:=(854401/1000000:ℝ))
    (u:=(111549/500000:ℝ)^2*(192697/250000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma large_21 {r x:ℝ} (hr:r∈Icc (181/400:ℝ) (91/200:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : large r < p x := by
  by_contra hn
  have hP : p x ≤ large (91/200:ℝ) := (le_of_not_gt hn).trans (large_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (15137/20000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (15137/20000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : large (91/200:ℝ) ≤ p (15137/20000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [large,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (15137/20000:ℝ)≤(56143/250000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (15137/20000:ℝ)≤(13341/10000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (15137/20000:ℝ)≤(77011/100000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(181/400:ℝ)) (q:=(15137/20000:ℝ)) (v:=(852639/1000000:ℝ))
    (u:=(56143/250000:ℝ)^2*(77011/100000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma large_22 {r x:ℝ} (hr:r∈Icc (91/200:ℝ) (183/400:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : large r < p x := by
  by_contra hn
  have hP : p x ≤ large (183/400:ℝ) := (le_of_not_gt hn).trans (large_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (75191/100000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (75191/100000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : large (183/400:ℝ) ≤ p (75191/100000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [large,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (75191/100000:ℝ)≤(45211/200000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (75191/100000:ℝ)≤(665149/500000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (75191/100000:ℝ)≤(769429/1000000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(91/200:ℝ)) (q:=(75191/100000:ℝ)) (v:=(850863/1000000:ℝ))
    (u:=(45211/200000:ℝ)^2*(769429/1000000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma large_23 {r x:ℝ} (hr:r∈Icc (183/400:ℝ) (23/50:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : large r < p x := by
  by_contra hn
  have hP : p x ≤ large (23/50:ℝ) := (le_of_not_gt hn).trans (large_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (9337/12500:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (9337/12500:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : large (23/50:ℝ) ≤ p (9337/12500:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [large,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (9337/12500:ℝ)≤(113773/500000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (9337/12500:ℝ)≤(1326491/1000000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (9337/12500:ℝ)≤(768743/1000000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(183/400:ℝ)) (q:=(9337/12500:ℝ)) (v:=(424537/500000:ℝ))
    (u:=(113773/500000:ℝ)^2*(768743/1000000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma large_24 {r x:ℝ} (hr:r∈Icc (23/50:ℝ) (37/80:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : large r < p x := by
  by_contra hn
  have hP : p x ≤ large (37/80:ℝ) := (le_of_not_gt hn).trans (large_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (371/500:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (371/500:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : large (37/80:ℝ) ≤ p (371/500:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [large,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (371/500:ℝ)≤(114523/500000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (371/500:ℝ)≤(33067/25000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (371/500:ℝ)≤(384027/500000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(23/50:ℝ)) (q:=(371/500:ℝ)) (v:=(847271/1000000:ℝ))
    (u:=(114523/500000:ℝ)^2*(384027/500000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

end GaussianPropeller.FourCertificates

end OAI
