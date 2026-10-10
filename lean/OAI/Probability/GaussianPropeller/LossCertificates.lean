import OAI.Probability.GaussianPropeller.LargeCertificates

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

lemma large_25 {r x:ℝ} (hr:r∈Icc (37/80:ℝ) (93/200:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : large r < p x := by
  by_contra hn
  have hP : p x ≤ large (93/200:ℝ) := (le_of_not_gt hn).trans (large_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (73703/100000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (73703/100000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : large (93/200:ℝ) ≤ p (73703/100000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [large,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (73703/100000:ℝ)≤(46111/200000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (73703/100000:ℝ)≤(263773/200000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (73703/100000:ℝ)≤(383681/500000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(37/80:ℝ)) (q:=(73703/100000:ℝ)) (v:=(422727/500000:ℝ))
    (u:=(46111/200000:ℝ)^2*(383681/500000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma large_26 {r x:ℝ} (hr:r∈Icc (93/200:ℝ) (187/400:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : large r < p x := by
  by_contra hn
  have hP : p x ≤ large (187/400:ℝ) := (le_of_not_gt hn).trans (large_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (36603/50000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (36603/50000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : large (187/400:ℝ) ≤ p (36603/50000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [large,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (36603/50000:ℝ)≤(58017/250000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (36603/50000:ℝ)≤(657527/500000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (36603/50000:ℝ)≤(766669/1000000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(93/200:ℝ)) (q:=(36603/50000:ℝ)) (v:=(105453/125000:ℝ))
    (u:=(58017/250000:ℝ)^2*(766669/1000000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma large_27 {r x:ℝ} (hr:r∈Icc (187/400:ℝ) (47/100:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : large r < p x := by
  by_contra hn
  have hP : p x ≤ large (47/100:ℝ) := (le_of_not_gt hn).trans (large_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (18177/25000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (18177/25000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : large (47/100:ℝ) ≤ p (18177/25000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [large,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (18177/25000:ℝ)≤(233591/1000000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (18177/25000:ℝ)≤(655619/500000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (18177/25000:ℝ)≤(765971/1000000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(187/400:ℝ)) (q:=(18177/25000:ℝ)) (v:=(841779/1000000:ℝ))
    (u:=(233591/1000000:ℝ)^2*(765971/1000000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma large_28 {r x:ℝ} (hr:r∈Icc (47/100:ℝ) (189/400:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : large r < p x := by
  by_contra hn
  have hP : p x ≤ large (189/400:ℝ) := (le_of_not_gt hn).trans (large_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (4513/6250:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (4513/6250:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : large (189/400:ℝ) ≤ p (4513/6250:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [large,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (4513/6250:ℝ)≤(1881/8000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (4513/6250:ℝ)≤(130741/100000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (4513/6250:ℝ)≤(765267/1000000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(47/100:ℝ)) (q:=(4513/6250:ℝ)) (v:=(839921/1000000:ℝ))
    (u:=(1881/8000:ℝ)^2*(765267/1000000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma large_29 {r x:ℝ} (hr:r∈Icc (189/400:ℝ) (19/40:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : large r < p x := by
  by_contra hn
  have hP : p x ≤ large (19/40:ℝ) := (le_of_not_gt hn).trans (large_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (17927/25000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (17927/25000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : large (19/40:ℝ) ≤ p (17927/25000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [large,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (17927/25000:ℝ)≤(47333/200000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (17927/25000:ℝ)≤(651793/500000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (17927/25000:ℝ)≤(382281/500000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(189/400:ℝ)) (q:=(17927/25000:ℝ)) (v:=(838049/1000000:ℝ))
    (u:=(47333/200000:ℝ)^2*(382281/500000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma large_30 {r x:ℝ} (hr:r∈Icc (19/40:ℝ) (191/400:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : large r < p x := by
  by_contra hn
  have hP : p x ≤ large (191/400:ℝ) := (le_of_not_gt hn).trans (large_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (8901/12500:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (8901/12500:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : large (191/400:ℝ) ≤ p (8901/12500:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [large,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (8901/12500:ℝ)≤(23821/100000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (8901/12500:ℝ)≤(649883/500000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (8901/12500:ℝ)≤(152771/200000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(19/40:ℝ)) (q:=(8901/12500:ℝ)) (v:=(418081/500000:ℝ))
    (u:=(23821/100000:ℝ)^2*(152771/200000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma large_31 {r x:ℝ} (hr:r∈Icc (191/400:ℝ) (12/25:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : large r < p x := by
  by_contra hn
  have hP : p x ≤ large (12/25:ℝ) := (le_of_not_gt hn).trans (large_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (35353/50000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (35353/50000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : large (12/25:ℝ) ≤ p (35353/50000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [large,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (35353/50000:ℝ)≤(239767/1000000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (35353/50000:ℝ)≤(1295933/1000000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (35353/50000:ℝ)≤(38157/50000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(191/400:ℝ)) (q:=(35353/50000:ℝ)) (v:=(417131/500000:ℝ))
    (u:=(239767/1000000:ℝ)^2*(38157/50000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma large_32 {r x:ℝ} (hr:r∈Icc (12/25:ℝ) (193/400:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : large r < p x := by
  by_contra hn
  have hP : p x ≤ large (193/400:ℝ) := (le_of_not_gt hn).trans (large_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (70203/100000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (70203/100000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : large (193/400:ℝ) ≤ p (70203/100000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [large,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (70203/100000:ℝ)≤(241333/1000000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (70203/100000:ℝ)≤(1292097/1000000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (70203/100000:ℝ)≤(95303/125000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(12/25:ℝ)) (q:=(70203/100000:ℝ)) (v:=(832347/1000000:ℝ))
    (u:=(241333/1000000:ℝ)^2*(95303/125000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma large_33 {r x:ℝ} (hr:r∈Icc (193/400:ℝ) (97/200:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : large r < p x := by
  by_contra hn
  have hP : p x ≤ large (97/200:ℝ) := (le_of_not_gt hn).trans (large_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (697/1000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (697/1000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : large (97/200:ℝ) ≤ p (697/1000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [large,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (697/1000:ℝ)≤(30363/125000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (697/1000:ℝ)≤(161033/125000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (697/1000:ℝ)≤(152341/200000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(193/400:ℝ)) (q:=(697/1000:ℝ)) (v:=(830417/1000000:ℝ))
    (u:=(30363/125000:ℝ)^2*(152341/200000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma large_34 {r x:ℝ} (hr:r∈Icc (97/200:ℝ) (39/80:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : large r < p x := by
  by_contra hn
  have hP : p x ≤ large (39/80:ℝ) := (le_of_not_gt hn).trans (large_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (17299/25000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (17299/25000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : large (39/80:ℝ) ≤ p (17299/25000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [large,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (17299/25000:ℝ)≤(61121/250000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (17299/25000:ℝ)≤(321107/250000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (17299/25000:ℝ)≤(760983/1000000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(97/200:ℝ)) (q:=(17299/25000:ℝ)) (v:=(828473/1000000:ℝ))
    (u:=(61121/250000:ℝ)^2*(760983/1000000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma large_35 {r x:ℝ} (hr:r∈Icc (39/80:ℝ) (49/100:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : large r < p x := by
  by_contra hn
  have hP : p x ≤ large (49/100:ℝ) := (le_of_not_gt hn).trans (large_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (68691/100000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (68691/100000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : large (49/100:ℝ) ≤ p (68691/100000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [large,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (68691/100000:ℝ)≤(30759/125000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (68691/100000:ℝ)≤(1280587/1000000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (68691/100000:ℝ)≤(11879/15625:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(39/80:ℝ)) (q:=(68691/100000:ℝ)) (v:=(413257/500000:ℝ))
    (u:=(30759/125000:ℝ)^2*(11879/15625:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma large_36 {r x:ℝ} (hr:r∈Icc (49/100:ℝ) (197/400:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : large r < p x := by
  by_contra hn
  have hP : p x ≤ large (197/400:ℝ) := (le_of_not_gt hn).trans (large_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (13637/20000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (13637/20000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : large (197/400:ℝ) ≤ p (13637/20000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [large,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (13637/20000:ℝ)≤(247669/1000000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (13637/20000:ℝ)≤(638371/500000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (13637/20000:ℝ)≤(189881/250000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(49/100:ℝ)) (q:=(13637/20000:ℝ)) (v:=(824541/1000000:ℝ))
    (u:=(247669/1000000:ℝ)^2*(189881/250000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma large_37 {r x:ℝ} (hr:r∈Icc (197/400:ℝ) (99/200:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : large r < p x := by
  by_contra hn
  have hP : p x ≤ large (99/200:ℝ) := (le_of_not_gt hn).trans (large_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (67679/100000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (67679/100000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : large (99/200:ℝ) ≤ p (67679/100000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [large,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (67679/100000:ℝ)≤(31159/125000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (67679/100000:ℝ)≤(636451/500000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (67679/100000:ℝ)≤(758793/1000000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(197/400:ℝ)) (q:=(67679/100000:ℝ)) (v:=(102819/125000:ℝ))
    (u:=(31159/125000:ℝ)^2*(758793/1000000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma large_38 {r x:ℝ} (hr:r∈Icc (99/200:ℝ) (199/400:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : large r < p x := by
  by_contra hn
  have hP : p x ≤ large (199/400:ℝ) := (le_of_not_gt hn).trans (large_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (67171/100000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (67171/100000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : large (199/400:ℝ) ≤ p (67171/100000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [large,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (67171/100000:ℝ)≤(250887/1000000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (67171/100000:ℝ)≤(1269049/1000000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (67171/100000:ℝ)≤(758053/1000000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(99/200:ℝ)) (q:=(67171/100000:ℝ)) (v:=(820549/1000000:ℝ))
    (u:=(250887/1000000:ℝ)^2*(758053/1000000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma large_39 {r x:ℝ} (hr:r∈Icc (199/400:ℝ) (1/2:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : large r < p x := by
  by_contra hn
  have hP : p x ≤ large (1/2:ℝ) := (le_of_not_gt hn).trans (large_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (66663/100000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (66663/100000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : large (1/2:ℝ) ≤ p (66663/100000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [large,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (66663/100000:ℝ)≤(252507/1000000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (66663/100000:ℝ)≤(1265201/1000000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (66663/100000:ℝ)≤(757313/1000000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(199/400:ℝ)) (q:=(66663/100000:ℝ)) (v:=(818531/1000000:ℝ))
    (u:=(252507/1000000:ℝ)^2*(757313/1000000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma large_40 {r x:ℝ} (hr:r∈Icc (1/2:ℝ) (201/400:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : large r < p x := by
  by_contra hn
  have hP : p x ≤ large (201/400:ℝ) := (le_of_not_gt hn).trans (large_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (33077/50000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (33077/50000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : large (201/400:ℝ) ≤ p (33077/50000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [large,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (33077/50000:ℝ)≤(31767/125000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (33077/50000:ℝ)≤(315337/250000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (33077/50000:ℝ)≤(756567/1000000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(1/2:ℝ)) (q:=(33077/50000:ℝ)) (v:=(816497/1000000:ℝ))
    (u:=(31767/125000:ℝ)^2*(756567/1000000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma large_41 {r x:ℝ} (hr:r∈Icc (201/400:ℝ) (101/200:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : large r < p x := by
  by_contra hn
  have hP : p x ≤ large (101/200:ℝ) := (le_of_not_gt hn).trans (large_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (16411/25000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (16411/25000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : large (101/200:ℝ) ≤ p (16411/25000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [large,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (16411/25000:ℝ)≤(255773/1000000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (16411/25000:ℝ)≤(314373/250000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (16411/25000:ℝ)≤(755819/1000000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(201/400:ℝ)) (q:=(16411/25000:ℝ)) (v:=(50903/62500:ℝ))
    (u:=(255773/1000000:ℝ)^2*(755819/1000000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma large_42 {r x:ℝ} (hr:r∈Icc (101/200:ℝ) (203/400:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : large r < p x := by
  by_contra hn
  have hP : p x ≤ large (203/400:ℝ) := (le_of_not_gt hn).trans (large_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (65133/100000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (65133/100000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : large (203/400:ℝ) ≤ p (65133/100000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [large,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (65133/100000:ℝ)≤(257419/1000000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (65133/100000:ℝ)≤(19588/15625:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (65133/100000:ℝ)≤(377533/500000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(101/200:ℝ)) (q:=(65133/100000:ℝ)) (v:=(25387/31250:ℝ))
    (u:=(257419/1000000:ℝ)^2*(377533/500000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma large_43 {r x:ℝ} (hr:r∈Icc (203/400:ℝ) (51/100:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : large r < p x := by
  by_contra hn
  have hP : p x ≤ large (51/100:ℝ) := (le_of_not_gt hn).trans (large_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (32311/50000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (32311/50000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : large (51/100:ℝ) ≤ p (32311/50000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [large,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (32311/50000:ℝ)≤(259071/1000000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (32311/50000:ℝ)≤(78111/62500:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (32311/50000:ℝ)≤(75431/100000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(203/400:ℝ)) (q:=(32311/50000:ℝ)) (v:=(12661/15625:ℝ))
    (u:=(259071/1000000:ℝ)^2*(75431/100000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma large_44 {r x:ℝ} (hr:r∈Icc (51/100:ℝ) (41/80:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : large r < p x := by
  by_contra hn
  have hP : p x ≤ large (41/80:ℝ) := (le_of_not_gt hn).trans (large_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (64109/100000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (64109/100000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : large (41/80:ℝ) ≤ p (64109/100000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [large,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (64109/100000:ℝ)≤(52147/200000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (64109/100000:ℝ)≤(1245909/1000000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (64109/100000:ℝ)≤(15071/20000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(51/100:ℝ)) (q:=(64109/100000:ℝ)) (v:=(50513/62500:ℝ))
    (u:=(52147/200000:ℝ)^2*(15071/20000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma large_45 {r x:ℝ} (hr:r∈Icc (41/80:ℝ) (103/200:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : large r < p x := by
  by_contra hn
  have hP : p x ≤ large (103/200:ℝ) := (le_of_not_gt hn).trans (large_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (15899/25000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (15899/25000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : large (103/200:ℝ) ≤ p (15899/25000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [large,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (15899/25000:ℝ)≤(65601/250000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (15899/25000:ℝ)≤(621023/500000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (15899/25000:ℝ)≤(752787/1000000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(41/80:ℝ)) (q:=(15899/25000:ℝ)) (v:=(806097/1000000:ℝ))
    (u:=(65601/250000:ℝ)^2*(752787/1000000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma large_46 {r x:ℝ} (hr:r∈Icc (103/200:ℝ) (207/400:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : large r < p x := by
  by_contra hn
  have hP : p x ≤ large (207/400:ℝ) := (le_of_not_gt hn).trans (large_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (31541/50000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (31541/50000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : large (207/400:ℝ) ≤ p (31541/50000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [large,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (31541/50000:ℝ)≤(132041/500000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (31541/50000:ℝ)≤(1238179/1000000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (31541/50000:ℝ)≤(37601/50000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(103/200:ℝ)) (q:=(31541/50000:ℝ)) (v:=(80397/100000:ℝ))
    (u:=(132041/500000:ℝ)^2*(37601/50000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma large_47 {r x:ℝ} (hr:r∈Icc (207/400:ℝ) (13/25:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : large r < p x := by
  by_contra hn
  have hP : p x ≤ large (13/25:ℝ) := (le_of_not_gt hn).trans (large_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (62567/100000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (62567/100000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : large (13/25:ℝ) ≤ p (62567/100000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [large,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (62567/100000:ℝ)≤(33221/125000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (62567/100000:ℝ)≤(1234309/1000000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (62567/100000:ℝ)≤(751249/1000000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(207/400:ℝ)) (q:=(62567/100000:ℝ)) (v:=(801827/1000000:ℝ))
    (u:=(33221/125000:ℝ)^2*(751249/1000000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma large_48 {r x:ℝ} (hr:r∈Icc (13/25:ℝ) (209/400:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : large r < p x := by
  by_contra hn
  have hP : p x ≤ large (209/400:ℝ) := (le_of_not_gt hn).trans (large_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (15513/25000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (15513/25000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : large (209/400:ℝ) ≤ p (15513/25000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [large,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (15513/25000:ℝ)≤(13373/50000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (15513/25000:ℝ)≤(615221/500000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (15513/25000:ℝ)≤(375237/500000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(13/25:ℝ)) (q:=(15513/25000:ℝ)) (v:=(799667/1000000:ℝ))
    (u:=(13373/50000:ℝ)^2*(375237/500000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma large_49 {r x:ℝ} (hr:r∈Icc (209/400:ℝ) (21/40:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : large r < p x := by
  by_contra hn
  have hP : p x ≤ large (21/40:ℝ) := (le_of_not_gt hn).trans (large_mono (by change 0≤r; linarith only [hr.1]) (by norm_num) hr.2)
  have hj : 0≤J 12 (12307/20000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hj' : 0≤J 13 (12307/20000:ℝ) := by norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hpL : large (21/40:ℝ) ≤ p (12307/20000:ℝ) := by
    apply le_trans ?_ (p_taylor_lower (by norm_num) 6 hj)
    norm_num [large,J,Finset.sum_range_succ,Nat.factorial]
  have hpU : p (12307/20000:ℝ)≤(67291/250000:ℝ) := by
    apply le_trans (p_taylor_upper (by norm_num) 6 hj')
    norm_num [J,Finset.sum_range_succ,Nat.factorial]
  have hla : lambda (12307/20000:ℝ)≤(245313/200000:ℝ) := by
    apply lambda_taylor_upper (by norm_num) 6 (by norm_num) hj
    norm_num [E,J,Finset.sum_range_succ,Nat.factorial]
  have hg : G (12307/20000:ℝ)≤(149939/200000:ℝ) := G_upper_of_lambda (by norm_num) hla (by norm_num)
  exact loss_row (lo:=(209/400:ℝ)) (q:=(12307/20000:ℝ)) (v:=(797491/1000000:ℝ))
    (u:=(67291/250000:ℝ)^2*(149939/200000:ℝ)) (by norm_num) hr.1 hx (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (loss_bound (by norm_num) hpU hg) (hP.trans hpL) hl

lemma large_of_loss {r x:ℝ} (hr:r∈Icc (2/5:ℝ) (21/40:ℝ)) (hx:0≤x)
    (hl:(9/(8*Real.pi))*r^2/(1+Real.sqrt (1-(4/3:ℝ)*r^2))≤loss x) : large r < p x := by
  by_cases h0 : r≤(161/400:ℝ)
  · exact large_0 ⟨by linarith only [hr.1],h0⟩ hx hl
  by_cases h1 : r≤(81/200:ℝ)
  · exact large_1 ⟨by linarith only [h0],h1⟩ hx hl
  by_cases h2 : r≤(163/400:ℝ)
  · exact large_2 ⟨by linarith only [h1],h2⟩ hx hl
  by_cases h3 : r≤(41/100:ℝ)
  · exact large_3 ⟨by linarith only [h2],h3⟩ hx hl
  by_cases h4 : r≤(33/80:ℝ)
  · exact large_4 ⟨by linarith only [h3],h4⟩ hx hl
  by_cases h5 : r≤(83/200:ℝ)
  · exact large_5 ⟨by linarith only [h4],h5⟩ hx hl
  by_cases h6 : r≤(167/400:ℝ)
  · exact large_6 ⟨by linarith only [h5],h6⟩ hx hl
  by_cases h7 : r≤(21/50:ℝ)
  · exact large_7 ⟨by linarith only [h6],h7⟩ hx hl
  by_cases h8 : r≤(169/400:ℝ)
  · exact large_8 ⟨by linarith only [h7],h8⟩ hx hl
  by_cases h9 : r≤(17/40:ℝ)
  · exact large_9 ⟨by linarith only [h8],h9⟩ hx hl
  by_cases h10 : r≤(171/400:ℝ)
  · exact large_10 ⟨by linarith only [h9],h10⟩ hx hl
  by_cases h11 : r≤(43/100:ℝ)
  · exact large_11 ⟨by linarith only [h10],h11⟩ hx hl
  by_cases h12 : r≤(173/400:ℝ)
  · exact large_12 ⟨by linarith only [h11],h12⟩ hx hl
  by_cases h13 : r≤(87/200:ℝ)
  · exact large_13 ⟨by linarith only [h12],h13⟩ hx hl
  by_cases h14 : r≤(7/16:ℝ)
  · exact large_14 ⟨by linarith only [h13],h14⟩ hx hl
  by_cases h15 : r≤(11/25:ℝ)
  · exact large_15 ⟨by linarith only [h14],h15⟩ hx hl
  by_cases h16 : r≤(177/400:ℝ)
  · exact large_16 ⟨by linarith only [h15],h16⟩ hx hl
  by_cases h17 : r≤(89/200:ℝ)
  · exact large_17 ⟨by linarith only [h16],h17⟩ hx hl
  by_cases h18 : r≤(179/400:ℝ)
  · exact large_18 ⟨by linarith only [h17],h18⟩ hx hl
  by_cases h19 : r≤(9/20:ℝ)
  · exact large_19 ⟨by linarith only [h18],h19⟩ hx hl
  by_cases h20 : r≤(181/400:ℝ)
  · exact large_20 ⟨by linarith only [h19],h20⟩ hx hl
  by_cases h21 : r≤(91/200:ℝ)
  · exact large_21 ⟨by linarith only [h20],h21⟩ hx hl
  by_cases h22 : r≤(183/400:ℝ)
  · exact large_22 ⟨by linarith only [h21],h22⟩ hx hl
  by_cases h23 : r≤(23/50:ℝ)
  · exact large_23 ⟨by linarith only [h22],h23⟩ hx hl
  by_cases h24 : r≤(37/80:ℝ)
  · exact large_24 ⟨by linarith only [h23],h24⟩ hx hl
  by_cases h25 : r≤(93/200:ℝ)
  · exact large_25 ⟨by linarith only [h24],h25⟩ hx hl
  by_cases h26 : r≤(187/400:ℝ)
  · exact large_26 ⟨by linarith only [h25],h26⟩ hx hl
  by_cases h27 : r≤(47/100:ℝ)
  · exact large_27 ⟨by linarith only [h26],h27⟩ hx hl
  by_cases h28 : r≤(189/400:ℝ)
  · exact large_28 ⟨by linarith only [h27],h28⟩ hx hl
  by_cases h29 : r≤(19/40:ℝ)
  · exact large_29 ⟨by linarith only [h28],h29⟩ hx hl
  by_cases h30 : r≤(191/400:ℝ)
  · exact large_30 ⟨by linarith only [h29],h30⟩ hx hl
  by_cases h31 : r≤(12/25:ℝ)
  · exact large_31 ⟨by linarith only [h30],h31⟩ hx hl
  by_cases h32 : r≤(193/400:ℝ)
  · exact large_32 ⟨by linarith only [h31],h32⟩ hx hl
  by_cases h33 : r≤(97/200:ℝ)
  · exact large_33 ⟨by linarith only [h32],h33⟩ hx hl
  by_cases h34 : r≤(39/80:ℝ)
  · exact large_34 ⟨by linarith only [h33],h34⟩ hx hl
  by_cases h35 : r≤(49/100:ℝ)
  · exact large_35 ⟨by linarith only [h34],h35⟩ hx hl
  by_cases h36 : r≤(197/400:ℝ)
  · exact large_36 ⟨by linarith only [h35],h36⟩ hx hl
  by_cases h37 : r≤(99/200:ℝ)
  · exact large_37 ⟨by linarith only [h36],h37⟩ hx hl
  by_cases h38 : r≤(199/400:ℝ)
  · exact large_38 ⟨by linarith only [h37],h38⟩ hx hl
  by_cases h39 : r≤(1/2:ℝ)
  · exact large_39 ⟨by linarith only [h38],h39⟩ hx hl
  by_cases h40 : r≤(201/400:ℝ)
  · exact large_40 ⟨by linarith only [h39],h40⟩ hx hl
  by_cases h41 : r≤(101/200:ℝ)
  · exact large_41 ⟨by linarith only [h40],h41⟩ hx hl
  by_cases h42 : r≤(203/400:ℝ)
  · exact large_42 ⟨by linarith only [h41],h42⟩ hx hl
  by_cases h43 : r≤(51/100:ℝ)
  · exact large_43 ⟨by linarith only [h42],h43⟩ hx hl
  by_cases h44 : r≤(41/80:ℝ)
  · exact large_44 ⟨by linarith only [h43],h44⟩ hx hl
  by_cases h45 : r≤(103/200:ℝ)
  · exact large_45 ⟨by linarith only [h44],h45⟩ hx hl
  by_cases h46 : r≤(207/400:ℝ)
  · exact large_46 ⟨by linarith only [h45],h46⟩ hx hl
  by_cases h47 : r≤(13/25:ℝ)
  · exact large_47 ⟨by linarith only [h46],h47⟩ hx hl
  by_cases h48 : r≤(209/400:ℝ)
  · exact large_48 ⟨by linarith only [h47],h48⟩ hx hl
  exact large_49 ⟨by linarith only [h48],hr.2⟩ hx hl

end GaussianPropeller.FourCertificates

end OAI
