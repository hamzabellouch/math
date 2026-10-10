import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.ExchangeAddNonempty
import OAI.Combinatorics.KMedianRecovery.Recovery.ThresholdTimesPower

namespace OAI

namespace MetricKMedianRecovery.Surplus
open MetricKMedianRecovery.LocalSearch MetricKMedianRecovery.Anchoring
variable {V : Type*} [PseudoMetricSpace V] [DecidableEq V]

noncomputable def clusterCost (D : Finset V) (assign : V → V) (i : V) : ℝ :=
  ∑ p ∈ cluster D assign i, dist p i
noncomputable def partCost (D I : Finset V) (assign : V → V) : ℝ :=
  ∑ i ∈ I, clusterCost D assign i
noncomputable def partCharge (D I : Finset V) (assign proxy : V → V) : ℝ :=
  ∑ i ∈ I, ∑ p ∈ cluster D assign i, dist p (proxy i)

omit [PseudoMetricSpace V] in
lemma cluster_sum (D I : Finset V) (assign : V → V) (f : V → V → ℝ) :
    (∑ i ∈ I, ∑ p ∈ cluster D assign i, f p i) =
      ∑ p ∈ D.filter (fun p => assign p ∈ I), f p (assign p) := by
  classical
  calc
    _ = ∑ i ∈ I, ∑ p ∈ D.filter (fun p => assign p = i), f p (assign p) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro p hp
      rw [(Finset.mem_filter.mp hp).2]
    _ = _ := Finset.sum_fiberwise_eq_sum_filter D I assign _

lemma clusterCost_nonneg (D : Finset V) (assign : V → V) (i : V) :
    0 ≤ clusterCost D assign i := Finset.sum_nonneg (fun _ _ => dist_nonneg)
lemma partCost_nonneg (D I : Finset V) (assign : V → V) :
    0 ≤ partCost D I assign := Finset.sum_nonneg (fun _ _ => clusterCost_nonneg D assign _)

lemma total_cluster_cost (D O : Finset V) (hO : O.Nonempty) :
    partCost D O (nearest O hO) = cost D O := by
  classical
  unfold partCost clusterCost
  rw [cluster_sum]
  have hf : D.filter (fun p => nearest O hO p ∈ O) = D :=
    Finset.filter_eq_self.mpr (fun p _ => nearest_mem O hO p)
  rw [hf]
  exact Finset.sum_congr rfl (fun p _ => nearest_distance O hO p)

lemma partition_cost (D O G B : Finset V) (hO : O.Nonempty)
    (hpart : G ∪ B = O) (hdis : Disjoint G B) :
    partCost D G (nearest O hO)+partCost D B (nearest O hO) = cost D O := by
  classical
  rw [← total_cluster_cost D O hO,partCost,partCost,partCost,← Finset.sum_union hdis,hpart]

lemma protected_partition_cost (F D S O G B : Finset V) (hS : S.Nonempty) (hO : O.Nonempty)
    (hSF : S ⊆ F) (hOF : O ⊆ F) (hlocal : WidthLocalMin F D S 5)
    (hcard : O.card ≤ S.card) (hpart : G ∪ B = O) (hdis : Disjoint G B)
    (hinj : Set.InjOn (nearest S hS) G) :
    cost D S ≤ (17/5:ℝ)*partCost D B (nearest O hO)+
      (6/5:ℝ)*partCharge D G (nearest O hO) (nearest S hS) := by
  classical
  let assign := nearest O hO
  let proxy := nearest S hS
  have hBO : B ⊆ O := by rw [← hpart]; exact Finset.subset_union_right
  have hmem (p : V) : assign p ∈ G ∨ assign p ∈ B := by
    have h : assign p ∈ O := nearest_mem O hO p
    rw [← hpart] at h
    exact Finset.mem_union.mp h
  have hiff (p : V) : assign p ∉ B ↔ assign p ∈ G := by
    constructor
    · intro hn; exact (hmem p).resolve_right hn
    · intro hg hb; exact Finset.disjoint_left.mp hdis hg hb
  have hcard' : B.card+G.card ≤ S.card := by
    rw [Nat.add_comm,← Finset.card_union_of_disjoint hdis,hpart]
    exact hcard
  have hswap := protected_swap_bound F D S B G hS hSF hlocal (hBO.trans hOF) hcard'
    assign proxy (fun p _ => (hmem p).symm)
    (fun i _ => nearest_mem S hS i) hinj
  have hbad : (∑ p ∈ D.filter (fun p => assign p ∈ B), dist p (assign p)) =
      partCost D B assign := (cluster_sum D B assign (fun p i => dist p i)).symm
  have hgood : (∑ p ∈ D.filter (fun p => assign p ∉ B), dist p (proxy (assign p))) =
      partCharge D G assign proxy := by
    rw [partCharge,cluster_sum]
    congr 1
    ext p
    simp only [Finset.mem_filter,hiff]
  rw [hbad,hgood] at hswap
  have hsplit : (∑ p ∈ D.filter (fun p => assign p ∈ B), connection S p)+
      (∑ p ∈ D.filter (fun p => assign p ∉ B), connection S p) = cost D S :=
    Finset.sum_filter_add_sum_filter_not D _ _
  have hg0 : 0 ≤ ∑ p ∈ D.filter (fun p => assign p ∉ B), connection S p :=
    Finset.sum_nonneg (fun _ _ => connection_nonneg _ _)
  change cost D S ≤ (17/5:ℝ)*partCost D B assign+(6/5:ℝ)*partCharge D G assign proxy
  linarith

omit [DecidableEq V] in
lemma cluster_dual_bound (D C : Finset V) (hCD : C ⊆ D) (alpha : V → ℝ) (lam : ℝ)
    (i : V) (hdual : (∑ p ∈ D, max (alpha p-2*dist i p) 0) ≤ lam) :
    (∑ p ∈ C, alpha p) ≤ lam+2*(∑ p ∈ C, dist p i) := by
  have hsub : (∑ p ∈ C, max (alpha p-2*dist i p) 0) ≤ lam :=
    (Finset.sum_le_sum_of_subset_of_nonneg hCD (fun _ _ _ => le_max_right _ _)).trans hdual
  have hpoint (p : V) : alpha p ≤ 2*dist p i+max (alpha p-2*dist i p) 0 := by
    rw [dist_comm p i]
    linarith only [le_max_left (alpha p-2*dist i p) 0]
  have hsum := Finset.sum_le_sum (s := C) (fun p _ => hpoint p)
  rw [Finset.sum_add_distrib,← Finset.mul_sum] at hsum
  linarith

lemma any_solution_dual (F D H : Finset V) (hHF : H ⊆ F) (hH : H.Nonempty)
    (alpha : V → ℝ) (lam : ℝ)
    (hdual : ∀ i ∈ F, (∑ p ∈ D, max (alpha p-2*dist i p) 0) ≤ lam) :
    (∑ p ∈ D, alpha p) ≤ H.card*lam+2*cost D H := by
  classical
  let assign := nearest H hH
  have hsum := Finset.sum_le_sum (s := H) (fun i hi => cluster_dual_bound D
    (cluster D assign i) (Finset.filter_subset _ _) alpha lam i (hdual i (hHF hi)))
  have hleft : (∑ i ∈ H, ∑ p ∈ cluster D assign i, alpha p) = ∑ p ∈ D, alpha p :=
    Finset.sum_fiberwise_of_maps_to (fun p _ => nearest_mem H hH p) alpha
  rw [hleft,Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul,← Finset.mul_sum] at hsum
  have he := total_cluster_cost D H hH
  change (∑ i ∈ H, ∑ p ∈ cluster D assign i, dist p i) = cost D H at he
  rwa [he] at hsum

end MetricKMedianRecovery.Surplus

end OAI
