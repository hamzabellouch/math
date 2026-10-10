import Mathlib
import OAI.Combinatorics.KMedianRecovery.Geometry.AllBadCostBound
import OAI.Combinatorics.KMedianRecovery.Recovery.IncomingSwapBound

namespace OAI

namespace MetricKMedianRecovery.Anchoring
open MetricKMedianRecovery.LocalSearch
variable {V : Type*} [MetricSpace V] [DecidableEq V]

lemma total_assignment_excess (F D O S G : Finset V) (hS : S.Nonempty)
    (hSF : S ⊆ F) (hOF : O ⊆ F) (hGO : G ⊆ O)
    (hlocal : WidthLocalMin F D S 5) (assign : V → V)
    (hassign : ∀ p ∈ D, assign p ∈ O) (b t : ℝ) (ht : 0 ≤ t) (ht1 : t < 1)
    (hwt : ∀ i ∈ G, clusterWeight D S assign i ≤ t*b)
    (hr : ∀ i ∈ G, dist i (nearest S hS i) ≤ t*separation O i)
    (hball : ∀ i ∈ G, nearest S hS i ∈ ballFacilities O S i) :
    (∑ i ∈ G, ∑ p ∈ cluster D assign i, (dist p (nearest S hS i)-dist p i)) ≤
      t*b*((G.filter (fun i => 2 ≤ (ballFacilities O S i).card)).card:ℝ)+
      (4*t+t/(1-t))*(∑ p ∈ D, (connection S p+dist p (assign p))) := by
  classical
  let cc := t/(1-t)
  let incoming := fun i => D.filter (fun p => assign p ≠ i ∧ nearest S hS p = nearest S hS i)
  let w := fun p => connection S p+dist p (assign p)
  have hcc : 0 ≤ cc := div_nonneg ht (by linarith)
  have hw : ∀ p ∈ D, 0 ≤ w p := fun p _ => add_nonneg (connection_nonneg S p) dist_nonneg
  have hinc : (∑ i ∈ G, ∑ p ∈ incoming i, w p) ≤ ∑ p ∈ D, w p :=
    disjoint_family_sum_le G D incoming w (fun _ _ => Finset.filter_subset _ _)
      (incoming_fibers_disjoint D G S hS assign (proxies_injective O S G hGO hS hball)) hw
  have hweights : (∑ i ∈ G, clusterWeight D S assign i) ≤ ∑ p ∈ D, w p := by
    rw [← all_cluster_weights D O S assign hassign]
    exact Finset.sum_le_sum_of_subset_of_nonneg hGO (fun i _ _ => clusterWeight_nonneg D S assign i)
  have hpoint (i : V) (hi : i ∈ G) :
      (∑ p ∈ cluster D assign i, (dist p (nearest S hS i)-dist p i)) ≤
        (if 2 ≤ (ballFacilities O S i).card then t*b else 0)+
          4*t*clusterWeight D S assign i+cc*(∑ p ∈ incoming i, w p) := by
    by_cases hc : 2 ≤ (ballFacilities O S i).card
    · simp only [hc,ite_true]
      have hE := (cluster_excess_bound D S hS assign i).trans
        ((nearest_cluster_radius D S hS assign i).trans (hwt i hi))
      have h1 : 0 ≤ 4*t*clusterWeight D S assign i :=
        mul_nonneg (by positivity) (clusterWeight_nonneg D S assign i)
      have h2 : 0 ≤ cc*(∑ p ∈ incoming i, w p) := mul_nonneg hcc
        (Finset.sum_nonneg (fun p hp => hw p (Finset.mem_filter.mp hp).1))
      linarith
    · simp only [hc,ite_false,zero_add]
      have hbox : ∀ s ∈ ballFacilities O S i, s = nearest S hS i := by
        intro s hs
        have hcard : (ballFacilities O S i).card ≤ 1 := by omega
        exact Finset.card_le_one.mp hcard s hs _ (hball i hi)
      exact singleton_cluster_charge F D O S hS hSF hlocal assign hassign i
        (hOF (hGO hi)) t ht ht1 (hr i hi) hbox
  have hsum := Finset.sum_le_sum (s := G) hpoint
  have hcount : (∑ i ∈ G, if 2 ≤ (ballFacilities O S i).card then t*b else 0) =
      t*b*((G.filter (fun i => 2 ≤ (ballFacilities O S i).card)).card:ℝ) := by
    rw [← Finset.sum_filter]
    simp [mul_comm]
  simp only [Finset.sum_add_distrib,← Finset.mul_sum] at hsum
  rw [hcount] at hsum
  have hm1 := mul_le_mul_of_nonneg_left hweights (show 0 ≤ 4*t by positivity)
  have hm2 := mul_le_mul_of_nonneg_left hinc hcc
  change _ ≤ t*b*(G.filter (fun i => 2 ≤ (ballFacilities O S i).card)).card+
    (4*t+cc)*(∑ p ∈ D, w p)
  nlinarith

end MetricKMedianRecovery.Anchoring

namespace MetricKMedianRecovery.Anchoring
open MetricKMedianRecovery.LocalSearch
variable {V : Type*} [MetricSpace V] [DecidableEq V]

noncomputable def clusterScale (D O : Finset V) (assign : V → V) (i : V) : ℝ :=
  (cluster D assign i).card * separation O i

theorem anchoring (F D O S : Finset V) (hO : O.Nonempty) (hS : S.Nonempty)
    (hO2 : 2 ≤ O.card) (hSF : S ⊆ F) (hOF : O ⊆ F)
    (hcard : O.card ≤ S.card) (hlocal : WidthLocalMin F D S 5)
    (b mu : ℝ) (hb : 0 < b) (hP : 0 < cost D O) (hmu : 0 < mu) (hmu1 : mu ≤ 1)
    (hscale : b*((S.card:ℝ)-O.card+
      (shortCenters O (clusterScale D O (nearest O hO)) b).card) ≤ 10*cost D O) :
    ∃ G B : Finset V,
      G ∪ B = O ∧ Disjoint G B ∧
      Set.InjOn (nearest S hS) G ∧
      (∀ i ∈ G, nearest S hS i ∈ S) ∧
      (∑ i ∈ G, ∑ p ∈ cluster D (nearest O hO) i, dist p (nearest S hS i)) ≤
        (∑ i ∈ G, ∑ p ∈ cluster D (nearest O hO) i, dist p i)+mu*cost D O ∧
      (B.card:ℝ) ≤ countConstant mu*cost D O/b := by
  classical
  let assign := nearest O hO
  let w := clusterWeight D S assign
  let sc := clusterScale D O assign
  let ell : ℝ := S.card-O.card
  have hell : 0 ≤ ell := sub_nonneg.mpr (by exact_mod_cast hcard)
  have hass : ∀ p ∈ D, assign p ∈ O := fun p _ => nearest_mem O hO p
  have hsum : (∑ i ∈ O, w i) ≤ 6*cost D O := by
    rw [all_cluster_weights D O S assign hass]
    simpa only [assign,nearest_distance] using
      local_combined_cost_bound F D S O hS hO hSF hlocal hOF hcard
  obtain ⟨a,ha,ht,htmu,htcost,hcount⟩ := threshold_with_count O sc w b (cost D O) mu ell
    hb hP hmu hmu1 hell (fun i _ => clusterWeight_nonneg D S assign i) hsum hscale
  let t := threshold mu a
  let B := badCenters O sc w b t
  let G := O \ B
  have hBO : B ⊆ O := Finset.filter_subset _ _
  have hGO : G ⊆ O := Finset.sdiff_subset
  have hpart : G ∪ B = O := Finset.sdiff_union_of_subset hBO
  have hdis : Disjoint G B := Finset.sdiff_disjoint
  have ht01 : t ≤ 1/100 := le_trans htmu (by linarith)
  have ht1 : t < 1 := lt_of_le_of_lt ht01 (by norm_num)
  have hgood (i : V) (hi : i ∈ G) : b ≤ sc i ∧ w i ≤ t*b := by
    have hmem := Finset.mem_sdiff.mp hi
    have hn : ¬ (sc i < b ∨ t*b < w i) := by
      intro hh
      exact hmem.2 (Finset.mem_filter.mpr ⟨hmem.1,hh⟩)
    push Not at hn
    exact hn
  have hr (i : V) (hi : i ∈ G) : dist i (nearest S hS i) ≤ t*separation O i :=
    (good_radius_bound D O S hS assign i b t hb ht.le (hgood i hi).1 (hgood i hi).2).2
  have hball (i : V) (hi : i ∈ G) : nearest S hS i ∈ ballFacilities O S i :=
    proxy_in_ball O S hO2 hS i t ht01 (hr i hi)
  have hinj := proxies_injective O S G hGO hS hball
  have hcrowd := crowded_card_bound G S (ballFacilities O S)
    (fun _ _ => Finset.filter_subset _ _) (fun i hi => ⟨_,hball i hi⟩)
    (fun i hi j hj hij => ballFacilities_disjoint O S (hGO hi) (hGO hj) hij)
  have hparts : G.card+B.card = O.card := by
    rw [← Finset.card_union_of_disjoint hdis,hpart]
  have hcrowdr : ((G.filter (fun i => 2 ≤ (ballFacilities O S i).card)).card:ℝ) ≤
      B.card+ell := by
    have hc : (G.card:ℝ)+(G.filter (fun i => 2 ≤ (ballFacilities O S i).card)).card ≤ S.card :=
      by exact_mod_cast hcrowd
    have hp : (G.card:ℝ)+B.card = O.card := by exact_mod_cast hparts
    dsimp [ell]
    linarith
  have htotal := total_assignment_excess F D O S G hS hSF hOF hGO hlocal assign hass b t
    ht.le ht1 (fun i hi => (hgood i hi).2) hr hball
  have hsumw : (∑ p ∈ D, (connection S p+dist p (assign p))) ≤ 6*cost D O := by
    rw [← all_cluster_weights D O S assign hass]
    exact hsum
  have hct : 0 ≤ 4*t+t/(1-t) := by positivity
  have hfirst : t*b*((G.filter (fun i => 2 ≤ (ballFacilities O S i).card)).card:ℝ) ≤
      mu*cost D O/2 := by
    exact (mul_le_mul_of_nonneg_left hcrowdr (mul_nonneg ht.le hb.le)).trans htcost
  have hfrac : t/(1-t) ≤ 2*t := by
    apply (div_le_iff₀ (by linarith : 0 < 1-t)).mpr
    nlinarith
  have hcoef : (4*t+t/(1-t))*(6*cost D O) ≤ mu*cost D O/2 := by
    have h36 : 36*t ≤ mu/2 := by dsimp [t] at *; linarith
    have hmul := mul_le_mul_of_nonneg_right h36 hP.le
    nlinarith [mul_le_mul_of_nonneg_right hfrac hP.le]
  have hsecond := (mul_le_mul_of_nonneg_left hsumw hct).trans hcoef
  refine ⟨G,B,hpart,hdis,hinj,(fun i _ => nearest_mem S hS i),?_,hcount⟩
  have he : (∑ i ∈ G, ∑ p ∈ cluster D assign i, (dist p (nearest S hS i)-dist p i)) =
      (∑ i ∈ G, ∑ p ∈ cluster D assign i, dist p (nearest S hS i))-
        (∑ i ∈ G, ∑ p ∈ cluster D assign i, dist p i) := by
    simp only [Finset.sum_sub_distrib]
  rw [he] at htotal
  linarith

end MetricKMedianRecovery.Anchoring

end OAI
