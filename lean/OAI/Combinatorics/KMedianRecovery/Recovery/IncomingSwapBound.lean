import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.ThresholdTimesPower

namespace OAI

namespace MetricKMedianRecovery.Anchoring
open MetricKMedianRecovery.LocalSearch
variable {V : Type*} [MetricSpace V] [DecidableEq V]

lemma incoming_swap_bound (F D S : Finset V) (hS : S.Nonempty) (hSF : S ⊆ F)
    (hlocal : WidthLocalMin F D S 5) (assign : V → V) (i proxy : V)
    (hi : i ∈ F) (hproxy : proxy ∈ S) :
    (∑ p ∈ D.filter (fun p => assign p = i ∧ nearest S hS p = proxy),
      (connection S p - dist p i)) ≤
      dist i proxy*((D.filter (fun p => assign p ≠ i ∧ nearest S hS p = proxy)).card:ℝ) := by
  classical
  let T := (S \ {proxy}) ∪ {i}
  have hc : cost D S ≤ cost D T := local_exchange F D S 5 hSF hlocal {proxy} {i}
    (by simpa) (by simpa) (Finset.singleton_nonempty i) (by simp) (by simp) (by simp)
  have hpoint (p : V) : connection T p-connection S p ≤
      (if nearest S hS p = proxy then
        (if assign p = i then dist p i-connection S p else dist i proxy) else 0) := by
    by_cases hp : nearest S hS p = proxy
    · simp only [hp,ite_true]
      have hn : connection T p ≤ dist p i :=
        connection_le (Finset.mem_union_right _ (Finset.mem_singleton_self _))
      by_cases ha : assign p = i
      · simpa only [ha,ite_true] using sub_le_sub_right hn (connection S p)
      · simp only [ha,ite_false]
        have hd : dist p proxy = connection S p := hp ▸ nearest_distance S hS p
        have htri := dist_triangle p proxy i
        rw [hd,dist_comm proxy i] at htri
        linarith
    · simp only [hp,ite_false]
      have hn : connection T p ≤ dist p (nearest S hS p) := connection_le
        (Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨nearest_mem S hS p,by simpa⟩))
      rw [nearest_distance] at hn
      linarith
  have hsum : 0 ≤ ∑ p ∈ D, (if nearest S hS p = proxy then
      (if assign p = i then dist p i-connection S p else dist i proxy) else 0) := by
    have hle := Finset.sum_le_sum (s := D) (fun p _ => hpoint p)
    rw [Finset.sum_sub_distrib] at hle
    change cost D T-cost D S ≤ _ at hle
    linarith
  have he : (∑ p ∈ D, if nearest S hS p = proxy then
      (if assign p = i then dist p i-connection S p else dist i proxy) else 0) =
      -(∑ p ∈ D.filter (fun p => assign p = i ∧ nearest S hS p = proxy),
        (connection S p - dist p i))+
      dist i proxy*((D.filter (fun p => assign p ≠ i ∧ nearest S hS p = proxy)).card:ℝ) := by
    have hconst : dist i proxy*((D.filter (fun p => assign p ≠ i ∧ nearest S hS p = proxy)).card:ℝ) =
        ∑ _p ∈ D.filter (fun p => assign p ≠ i ∧ nearest S hS p = proxy), dist i proxy := by
      simp [mul_comm]
    rw [hconst,← Finset.sum_neg_distrib]
    simp only [Finset.sum_filter]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p _
    by_cases hp : nearest S hS p = proxy <;> by_cases ha : assign p = i <;>
      simp [hp,ha]
  rw [he] at hsum
  linarith

lemma cluster_excess_bound (D S : Finset V) (hS : S.Nonempty) (assign : V → V) (i : V) :
    (∑ p ∈ cluster D assign i, (dist p (nearest S hS i)-dist p i)) ≤
      ((cluster D assign i).card:ℝ)*dist i (nearest S hS i) := by
  have hh := Finset.sum_le_sum (s := cluster D assign i) (fun p _ =>
    (show dist p (nearest S hS i)-dist p i ≤ dist i (nearest S hS i) by
      linarith [dist_triangle p i (nearest S hS i)]))
  simpa using hh

lemma singleton_ball_client_bound (O S : Finset V) (hS : S.Nonempty) (i p : V) (t : ℝ)
    (ht : 0 ≤ t) (hr : dist i (nearest S hS i) ≤ t*separation O i)
    (hbox : ∀ s ∈ ballFacilities O S i, s = nearest S hS i)
    (hp : nearest S hS p ≠ nearest S hS i) :
    dist p (nearest S hS i)-dist p i ≤ 4*t*(dist p i+connection S p) := by
  have hout : nearest S hS p ∉ ballFacilities O S i := fun hm => hp (hbox _ hm)
  have hd : separation O i/4 ≤ dist i (nearest S hS p) := by
    by_contra h
    exact hout (Finset.mem_filter.mpr ⟨nearest_mem S hS p,lt_of_not_ge h⟩)
  have htri := dist_triangle i p (nearest S hS p)
  rw [dist_comm i p,nearest_distance] at htri
  have he := dist_triangle p i (nearest S hS i)
  nlinarith [mul_le_mul_of_nonneg_left (hd.trans htri) (show 0 ≤ 4*t by positivity)]

lemma incoming_charge_bound (O S : Finset V) (hS : S.Nonempty) (assign : V → V)
    (i p : V) (t : ℝ) (ht : 0 ≤ t) (ht1 : t < 1)
    (hr : dist i (nearest S hS i) ≤ t*separation O i)
    (hassign : assign p ∈ O) (hpi : assign p ≠ i)
    (hp : nearest S hS p = nearest S hS i) :
    dist i (nearest S hS i) ≤ (t/(1-t))*(dist p (assign p)+connection S p) := by
  have hsep := separation_le hassign hpi
  have htri1 := dist_triangle i (nearest S hS i) (assign p)
  have htri2 := dist_triangle (nearest S hS i) p (assign p)
  have he : dist (nearest S hS i) p = connection S p := by
    rw [← hp,dist_comm,nearest_distance]
  rw [he] at htri2
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ (by linarith : 0 < 1-t)).mpr
  nlinarith

end MetricKMedianRecovery.Anchoring

namespace MetricKMedianRecovery.Anchoring
open MetricKMedianRecovery.LocalSearch
variable {V : Type*} [MetricSpace V] [DecidableEq V]

lemma cluster_weight_identity (D S : Finset V) (assign : V → V) (i : V) :
    clusterWeight D S assign i =
      ∑ p ∈ cluster D assign i, (connection S p+dist p (assign p)) := by
  apply Finset.sum_congr rfl
  intro p hp
  rw [(Finset.mem_filter.mp hp).2]

lemma all_cluster_weights (D O S : Finset V) (assign : V → V)
    (hassign : ∀ p ∈ D, assign p ∈ O) :
    (∑ i ∈ O, clusterWeight D S assign i) =
      ∑ p ∈ D, (connection S p+dist p (assign p)) := by
  simp_rw [cluster_weight_identity,cluster]
  exact Finset.sum_fiberwise_of_maps_to hassign _

omit [MetricSpace V] in
lemma disjoint_family_sum_le {I : Type*} [DecidableEq I] (G : Finset I) (D : Finset V)
    (boxes : I → Finset V) (f : V → ℝ) (hsub : ∀ i ∈ G, boxes i ⊆ D)
    (hd : (G : Set I).PairwiseDisjoint boxes) (hf : ∀ p ∈ D, 0 ≤ f p) :
    (∑ i ∈ G, ∑ p ∈ boxes i, f p) ≤ ∑ p ∈ D, f p := by
  rw [← Finset.sum_biUnion hd]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro p hp
    obtain ⟨i,hi,hp⟩ := Finset.mem_biUnion.mp hp
    exact hsub i hi hp
  · intro p hp _; exact hf p hp

lemma singleton_cluster_charge (F D O S : Finset V) (hS : S.Nonempty) (hSF : S ⊆ F)
    (hlocal : WidthLocalMin F D S 5) (assign : V → V)
    (hassign : ∀ p ∈ D, assign p ∈ O) (i : V) (hi : i ∈ F) (t : ℝ)
    (ht : 0 ≤ t) (ht1 : t < 1)
    (hr : dist i (nearest S hS i) ≤ t*separation O i)
    (hbox : ∀ s ∈ ballFacilities O S i, s = nearest S hS i) :
    (∑ p ∈ cluster D assign i, (dist p (nearest S hS i)-dist p i)) ≤
      4*t*clusterWeight D S assign i +
      (t/(1-t))*(∑ p ∈ D.filter (fun p => assign p ≠ i ∧
        nearest S hS p = nearest S hS i), (connection S p+dist p (assign p))) := by
  classical
  let proxy := nearest S hS i
  have hextra (p : V) : 0 ≤ 4*t*(connection S p+dist p i) :=
    mul_nonneg (by positivity) (add_nonneg (connection_nonneg _ _) dist_nonneg)
  have hpoint (p : V) : dist p proxy-dist p i ≤
      (if nearest S hS p = proxy then dist p proxy-dist p i else 0)+
        4*t*(connection S p+dist p i) := by
    by_cases hp : nearest S hS p = proxy
    · simp only [hp,ite_true]
      linarith [hextra p]
    · simp only [hp,ite_false,zero_add]
      have h := singleton_ball_client_bound O S hS i p t ht hr hbox hp
      linarith
  have hpoints := Finset.sum_le_sum (s := cluster D assign i) (fun p _ => hpoint p)
  rw [Finset.sum_add_distrib,← Finset.mul_sum] at hpoints
  change (∑ p ∈ cluster D assign i, (dist p proxy-dist p i)) ≤
    (∑ p ∈ cluster D assign i, if nearest S hS p = proxy then dist p proxy-dist p i else 0)+
      4*t*clusterWeight D S assign i at hpoints
  have he : (∑ p ∈ cluster D assign i, if nearest S hS p = proxy then
        dist p proxy-dist p i else 0) =
      ∑ p ∈ D.filter (fun p => assign p = i ∧ nearest S hS p = proxy),
        (connection S p-dist p i) := by
    simp only [cluster,Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro p _
    by_cases ha : assign p = i <;> by_cases hp : nearest S hS p = proxy <;>
      simp only [ha,hp,ite_true,ite_false,true_and,false_and]
    rw [← hp,nearest_distance]
  rw [he] at hpoints
  have hswap := incoming_swap_bound F D S hS hSF hlocal assign i proxy hi (nearest_mem S hS i)
  have hcharges : dist i proxy*((D.filter (fun p => assign p ≠ i ∧
        nearest S hS p = proxy)).card:ℝ) ≤
      (t/(1-t))*(∑ p ∈ D.filter (fun p => assign p ≠ i ∧ nearest S hS p = proxy),
        (connection S p+dist p (assign p))) := by
    have q := Finset.sum_le_sum (s := D.filter (fun p => assign p ≠ i ∧ nearest S hS p = proxy))
      (fun p hp => incoming_charge_bound O S hS assign i p t ht ht1 hr
        (hassign p (Finset.mem_filter.mp hp).1) (Finset.mem_filter.mp hp).2.1
        (Finset.mem_filter.mp hp).2.2)
    simpa only [Finset.sum_const,nsmul_eq_mul,← Finset.mul_sum,add_comm,mul_comm] using q
  linarith

lemma incoming_fibers_disjoint (D G S : Finset V) (hS : S.Nonempty) (assign : V → V)
    (hinj : Set.InjOn (nearest S hS) G) :
    (G : Set V).PairwiseDisjoint (fun i => D.filter (fun p => assign p ≠ i ∧
      nearest S hS p = nearest S hS i)) := by
  intro i hi j hj hij
  apply Finset.disjoint_left.mpr
  intro p hpi hpj
  exact hij (hinj hi hj ((Finset.mem_filter.mp hpi).2.2.symm.trans
    (Finset.mem_filter.mp hpj).2.2))

end MetricKMedianRecovery.Anchoring

end OAI
