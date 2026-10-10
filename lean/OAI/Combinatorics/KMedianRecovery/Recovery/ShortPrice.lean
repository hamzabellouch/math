import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.TotalAssignmentExcess
import OAI.Combinatorics.KMedianRecovery.Geometry.ClusterCost
import OAI.Combinatorics.KMedianRecovery.Recovery.Chosen

namespace OAI

namespace MetricKMedianRecovery.Surplus

lemma short_price (lam P e n r : ℝ) (hlam : 0 ≤ lam) (hn : n/4 ≤ r)
    (hremove : lam*r ≤ 2*P+2*(lam/8)*r+e) :
    lam*n ≤ (32/3:ℝ)*P+(16/3:ℝ)*e := by
  have h := mul_le_mul_of_nonneg_left hn hlam
  nlinarith only [h,hremove]

lemma anchoring_scale (lam P e L n xi v : ℝ)
    (hP : 0 ≤ P) (hxi : xi ≤ 1) (hv : v ≤ 1/12) (he : e ≤ v*P)
    (hprice : L*lam ≤ 2*(1+xi)*P+e)
    (hshort : lam*n ≤ (32/3:ℝ)*P+(16/3:ℝ)*e) :
    (lam/8)*(L+n) ≤ 10*P := by
  have hx := mul_le_mul_of_nonneg_right hxi hP
  have hvP := mul_le_mul_of_nonneg_right hv hP
  nlinarith only [hprice,hshort,hx,hvP,he,hP]

lemma small_bad_cost (S P Pb Pg : ℝ) (hPb : Pb ≤ P/10)
    (hpart : Pg+Pb = P) (hS : S ≤ (6/5:ℝ)*(Pg+P/100)+(17/5:ℝ)*Pb) :
    S ≤ (179/125:ℝ)*P := by
  linarith

lemma small_bad_strict (S P c : ℝ) (hP : 0 ≤ P) (hc : c ≤ 1)
    (hS : S ≤ (179/125:ℝ)*P) : S ≤ (2-c/100)*P := by
  have h := mul_le_mul_of_nonneg_right hc hP
  nlinarith only [h,hP,hS]

lemma bounded_mass {I : Type*} (B : Finset I) (p : I → ℝ) (lam C P : ℝ)
    (hC : 0 < C) (hlam : 0 ≤ lam) (hP : 0 < P) (hPb : P/10 < ∑ i ∈ B, p i)
    (hprice : (B.card:ℝ)*lam ≤ 8*C*P) :
    P/20 < ∑ i ∈ B.filter (fun i => lam ≤ 200*C*p i), p i := by
  classical
  let good := B.filter (fun i => lam ≤ 200*C*p i)
  let bad := B.filter (fun i => ¬lam ≤ 200*C*p i)
  have hsplit : (∑ i ∈ good, p i)+(∑ i ∈ bad, p i) = ∑ i ∈ B, p i :=
    Finset.sum_filter_add_sum_filter_not B _ p
  have hbad : (200*C)*(∑ i ∈ bad, p i) ≤ (B.card:ℝ)*lam := by
    have hcard : bad.card ≤ B.card := Finset.card_filter_le _ _
    calc
      _ = ∑ i ∈ bad, (200*C)*p i := by rw [Finset.mul_sum]
      _ ≤ ∑ _i ∈ bad, lam := Finset.sum_le_sum (fun i hi =>
        (not_le.mp (Finset.mem_filter.mp hi).2).le)
      _ = (bad.card:ℝ)*lam := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hlam
  have hh := hbad.trans hprice
  have hmass : (∑ i ∈ bad, p i) ≤ P/25 := by nlinarith only [hh,hC]
  change P/20 < ∑ i ∈ good, p i
  linarith

lemma normal_strict (U P c v e : ℝ) (hP : 0 < P) (hc : 0 < c)
    (hv : 0 < v) (hv1 : v ≤ 1/12) (hvc : v ≤ c/1000) (he : e ≤ v*P)
    (hU : (1-3*v)*U ≤ (2-c/40)*P+e) :
    U ≤ (2-c/100)*P := by
  have ht : 0 < 1-3*v := by linarith
  have hvcP := mul_le_mul_of_nonneg_right hvc hP.le
  have hvP : 0 ≤ v*P := mul_nonneg hv.le hP.le
  have hsmall : (2-c/100)*(3*v)*P ≤ 6*v*P := by
    have hcv : 0 ≤ c*(v*P) := mul_nonneg hc.le hvP
    nlinarith only [hcv]
  have htar : (2-c/40)*P+e ≤ (1-3*v)*((2-c/100)*P) := by
    nlinarith only [hsmall,hvcP,he,hP,hc]
  exact (mul_le_mul_iff_right₀ ht).mp (hU.trans htar)

lemma small_price_strict (U P c v A : ℝ) (hP : 0 ≤ P) (hc : 0 < c)
    (hv : 0 < v) (hv1 : v ≤ 1/12) (hvc : v ≤ c/1000)
    (hpay : (1-3*v)*U ≤ A) (hA : A ≤ (2-c/2+c/200)*P) :
    U ≤ (2-c/100)*P := by
  have ht : 0 < 1-3*v := by linarith
  have hvcP := mul_le_mul_of_nonneg_right hvc hP
  have hcv : 0 ≤ c*(v*P) := mul_nonneg hc.le (mul_nonneg hv.le hP)
  have htar : A ≤ (1-3*v)*((2-c/100)*P) := by
    nlinarith only [hA,hvcP,hcv,hP,hc]
  exact (mul_le_mul_iff_right₀ ht).mp (hpay.trans htar)

end MetricKMedianRecovery.Surplus

namespace MetricKMedianRecovery.Surplus
open MetricKMedianRecovery.LocalSearch MetricKMedianRecovery.Anchoring
variable {V : Type*} [MetricSpace V] [DecidableEq V] [Fintype V]

omit [Fintype V] in
lemma aggregate_gain (D O B : Finset V) (hO : O.Nonempty) (hBO : B ⊆ O)
    (alpha : V → ℝ) (lam c : ℝ)
    (hrow : ∀ i ∈ O, (∑ p ∈ cluster D (nearest O hO) i, alpha p) ≤
      lam+2*clusterCost D (nearest O hO) i)
    (hstrict : ∀ i ∈ B, (∑ p ∈ cluster D (nearest O hO) i, alpha p) ≤
      lam+(2-c/2)*clusterCost D (nearest O hO) i) :
    (∑ p ∈ D, alpha p) ≤ O.card*lam+2*cost D O-(c/2)*partCost D B (nearest O hO) := by
  classical
  let assign := nearest O hO
  have hpoint (i : V) (hi : i ∈ O) : (∑ p ∈ cluster D assign i, alpha p) ≤
      lam+2*clusterCost D assign i-(if i ∈ B then (c/2)*clusterCost D assign i else 0) := by
    by_cases hb : i ∈ B
    · rw [ite_eq_left hb]
      linarith only [hstrict i hb]
    · rw [ite_eq_right hb,sub_zero]
      exact hrow i hi
  have hsum := Finset.sum_le_sum (s := O) hpoint
  have hleft : (∑ i ∈ O, ∑ p ∈ cluster D assign i, alpha p) = ∑ p ∈ D, alpha p :=
    Finset.sum_fiberwise_of_maps_to (fun p _ => nearest_mem O hO p) alpha
  have hf : O.filter (fun i => i ∈ B) = B := by
    ext i
    simp only [Finset.mem_filter]
    exact ⟨fun hi => hi.2,fun hi => ⟨hBO hi,hi⟩⟩
  have hcost : (∑ i ∈ O, clusterCost D assign i) = cost D O := total_cluster_cost D O hO
  rw [hleft,Finset.sum_sub_distrib,Finset.sum_add_distrib,Finset.sum_const,
    nsmul_eq_mul,← Finset.mul_sum,hcost,← Finset.sum_filter,hf,← Finset.mul_sum] at hsum
  exact hsum

theorem low_sensitive_cost (F D O S H : Finset V) (hO : O.Nonempty) (hS : S.Nonempty)
    (hH : H.Nonempty) (hOF : O ⊆ F) (hSF : S ⊆ F) (hHF : H ⊆ F)
    (hO2 : 2 ≤ O.card) (L : ℕ) (hcard : S.card = O.card+L) (hHL : H.card+L = O.card)
    (hlocal : WidthLocalMin F D S 5) (hP : 0 < cost D O)
    (alpha : V → ℝ) (lam Q e xi v c C : ℝ)
    (hlam : 0 < lam) (hQ : 0 ≤ Q) (hSQ : cost D S ≤ Q)
    (hHcost : cost D H ≤ (1+xi)*cost D O) (hxi : xi ≤ 1)
    (hv : 0 < v) (hv1 : v ≤ 1/12) (hvc : v ≤ c/1000) (he : e ≤ v*cost D O)
    (hc : 0 < c) (hc1 : c ≤ 1) (hC : 0 < C) (hCeq : C = countConstant (1/100))
    (hpayment : (1-3*v)*Q+O.card*lam-e ≤ ∑ p ∈ D, alpha p)
    (hdual : ∀ i ∈ F, (∑ p ∈ D, max (alpha p-2*dist i p) 0) ≤ lam)
    (hstrict : ∀ i ∈ O, lam ≤ (200*C)*clusterCost D (nearest O hO) i →
      (∑ p ∈ cluster D (nearest O hO) i, alpha p) ≤
        lam+(2-c/2)*clusterCost D (nearest O hO) i) :
    cost D S ≤ (2-c/100)*cost D O := by
  classical
  let P := cost D O
  let assign := nearest O hO
  let b := lam/8
  have hb : 0 < b := by dsimp [b]; positivity
  have ht : 0 ≤ 1-3*v := by linarith
  have hprice (A : Finset V) (hAF : A ⊆ F) (hA : A.Nonempty) :
      ((O.card:ℝ)-A.card)*lam ≤ 2*cost D A+e := by
    have hh := any_solution_dual F D A hAF hA alpha lam hdual
    have hq := mul_nonneg ht hQ
    nlinarith only [hh,hpayment,hq]
  have hsur : (L:ℝ)*lam ≤ 2*(1+xi)*P+e := by
    have hh := hprice H hHF hH
    have heq : (H.card:ℝ)+L = O.card := by exact_mod_cast hHL
    have heqlam : ((O.card:ℝ)-H.card)*lam = L*lam := by rw [← heq]; ring
    rw [heqlam] at hh
    dsimp [P]
    linarith only [hh,hHcost]
  obtain ⟨R,hRO,hrem,hRcard,hRcost⟩ := short_removal D O hO hO2 b
  have hshort : lam*((shortCenters O (clusterScale D O assign) b).card:ℝ) ≤
      (32/3:ℝ)*P+(16/3:ℝ)*e := by
    have hh := hprice (O \ R) (Finset.sdiff_subset.trans hOF) hrem
    have heq : ((O \ R).card:ℝ)+R.card = O.card := by
      exact_mod_cast Finset.card_sdiff_add_card_eq_card hRO
    have heqlam : ((O.card:ℝ)-(O \ R).card)*lam = R.card*lam := by rw [← heq]; ring
    rw [heqlam] at hh
    have hr : lam*(R.card:ℝ) ≤ 2*P+2*(lam/8)*R.card+e := by
      dsimp [P,b] at *
      nlinarith only [hh,hRcost]
    apply short_price lam P e _ R.card hlam.le _ hr
    exact hRcard
  have hell : (S.card:ℝ)-O.card = L := by
    have hh : (S.card:ℝ) = O.card+L := by exact_mod_cast hcard
    linarith only [hh]
  have hscale : b*((S.card:ℝ)-O.card+(shortCenters O (clusterScale D O assign) b).card) ≤ 10*P := by
    rw [hell]
    exact anchoring_scale lam P e L _ xi v hP.le hxi hv1 he hsur hshort
  obtain ⟨G,B,hpart,hdis,hinj,hproxy,hcharge,hcount⟩ := anchoring F D O S hO hS hO2 hSF hOF
    (by omega) hlocal b (1/100) hb hP (by norm_num) (by norm_num) hscale
  have hp : partCost D G assign+partCost D B assign = P := partition_cost D O G B hO hpart hdis
  have hcharge' : partCharge D G assign (nearest S hS) ≤ partCost D G assign+P/100 := by
    change _ ≤ _+ (1/100:ℝ)*P at hcharge
    simpa only [partCharge,partCost,clusterCost,assign,div_eq_mul_inv,mul_comm,one_mul] using hcharge
  have hrow (i : V) (hi : i ∈ O) : (∑ p ∈ cluster D assign i, alpha p) ≤
      lam+2*clusterCost D assign i :=
    cluster_dual_bound D _ (Finset.filter_subset _ _) alpha lam i (hdual i (hOF hi))
  by_cases hbad : partCost D B assign ≤ P/10
  · have hs := protected_partition_cost F D S O G B hS hO hSF hOF hlocal (by omega) hpart hdis hinj
    have hsub : cost D S ≤ (6/5:ℝ)*(partCost D G assign+P/100)+(17/5:ℝ)*partCost D B assign := by
      change cost D S ≤ (17/5:ℝ)*partCost D B assign+(6/5:ℝ)*partCharge D G assign (nearest S hS) at hs
      linarith
    exact small_bad_strict _ P c hP.le hc1 (small_bad_cost _ P _ _ hbad hp hsub)
  · have hBprice : (B.card:ℝ)*lam ≤ 8*C*P := by
      rw [← hCeq] at hcount
      have hh := (le_div_iff₀ hb).mp hcount
      dsimp [b] at hh
      nlinarith only [hh]
    let BT := B.filter (fun i => lam ≤ 200*C*clusterCost D assign i)
    have hm : P/20 < partCost D BT assign := bounded_mass B (clusterCost D assign) lam C P
      hC hlam.le hP (lt_of_not_ge hbad) hBprice
    have hBO : B ⊆ O := by rw [← hpart]; exact Finset.subset_union_right
    have hBTO : BT ⊆ O := (Finset.filter_subset _ _).trans hBO
    have hgain := aggregate_gain D O BT hO hBTO alpha lam c hrow (fun i hi =>
      hstrict i (hBTO hi) (Finset.mem_filter.mp hi).2)
    have hmass := mul_le_mul_of_nonneg_left hm.le (by positivity : 0 ≤ c/2)
    have hbudget : (∑ p ∈ D, alpha p) ≤ O.card*lam+(2-c/40)*P := by
      change (∑ p ∈ D, alpha p) ≤ O.card*lam+2*P-(c/2)*partCost D BT assign at hgain
      nlinarith only [hgain,hmass]
    have hq : (1-3*v)*Q ≤ (2-c/40)*P+e := by linarith only [hpayment,hbudget]
    exact hSQ.trans (normal_strict Q P c v e hP hc hv hv1 hvc he hq)

end MetricKMedianRecovery.Surplus

end OAI
