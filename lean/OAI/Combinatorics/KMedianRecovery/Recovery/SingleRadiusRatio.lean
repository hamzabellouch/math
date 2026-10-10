import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.Cluster

namespace OAI

namespace MetricKMedianRecovery.Sampling
variable {V : Type*} [LinearOrder V] [PseudoMetricSpace V]
namespace Comparison
variable {D S O : Finset V}

lemma single_radius_ratio (C : Comparison D S O) (hD : D.Nonempty)
    (hP : 0 < comparisonCost D C.assign) (hm : 0 < C.bad.card)
    (w : V) (hw : w ∈ D)
    (hr : 10*Population.radius D hD (comparisonCost D C.assign) C.bad.card w < dist w (C.assign w)) :
    dist w (C.assign w)/Population.radius D hD (comparisonCost D C.assign) C.bad.card w ≤
      (10/9 : ℝ)*C.bad.card := by
  let q := Population.radius D hD (comparisonCost D C.assign) C.bad.card w
  have hq : 0 < q := Population.radius_pos D hD _ _ w hP hm
  have hcharge : ∀ p ∈ Population.ball D w q, (9/10 : ℝ)*dist w (C.assign w) ≤ dist p (C.assign p) := by
    intro p hp
    have hp' := Finset.mem_filter.mp hp
    have hh := C.comparison_triangle w p hw hp'.1
    linarith [hp'.2]
  have hh := Population.disjoint_population_budget D ({()} : Finset Unit)
    (fun _ => Population.ball D w q) (fun _ => q) (fun _ => dist w (C.assign w))
    (fun p => dist p (C.assign p)) (comparisonCost D C.assign) C.bad.card hP hm
    (fun _ _ => dist_nonneg) rfl (fun _ _ => Finset.filter_subset _ _) (by simp)
    (fun _ _ => hq) (fun _ _ => dist_nonneg)
    (fun _ _ => Population.radius_feasible D hD _ _ w hP hm) (fun _ _ => hcharge)
  simpa only [Finset.sum_singleton] using hh

end Comparison
end MetricKMedianRecovery.Sampling

namespace MetricKMedianRecovery.Sampling.Comparison
variable {V : Type*} [LinearOrder V] [PseudoMetricSpace V] {D S O : Finset V}

noncomputable def leaderPair (C : Comparison D S O) (s : State V) (o : V) : V × ℝ :=
  if h : o ∈ C.covered s then Classical.choose (C.covered_witness s o h) else (o,0)

lemma leaderPair_spec (C : Comparison D S O) (s : State V) (o : V) (ho : o ∈ C.covered s) :
    C.leaderPair s o ∈ s.leaves ∧ C.assign (C.leaderPair s o).1 = o := by
  simp only [leaderPair,dite_eq_left ho]
  exact Classical.choose_spec (C.covered_witness s o ho)

lemma covered_population_sum (C : Comparison D S O) (hD : D.Nonempty)
    (kappa : ℝ) (s : State V) (hs : C.Correct hD kappa s)
    (hP : 0 < comparisonCost D C.assign) (hm : 0 < C.bad.card) :
    (∑ o ∈ C.covered s, (cluster D C.assign o).card *
      Population.radius D hD (comparisonCost D C.assign) C.bad.card (C.leaderPair s o).1) ≤
      (26/5:ℝ)*comparisonCost D C.assign := by
  have hpoint : ∀ o ∈ C.covered s,
      (cluster D C.assign o).card *
        Population.radius D hD (comparisonCost D C.assign) C.bad.card (C.leaderPair s o).1 ≤
          (16/5:ℝ)*clusterCost D C.assign o+2*comparisonCost D C.assign/C.bad.card := by
    intro o ho
    have hp := C.leaderPair_spec s o ho
    have hc := hs.2.2 _ hp.1
    have hC : (cluster D C.assign o).Nonempty :=
      ⟨(C.leaderPair s o).1,(cluster_mem _ _ _ _).mpr ⟨hc.1,hp.2⟩⟩
    have hn : (0:ℝ) < (cluster D C.assign o).card := Nat.cast_pos.mpr (Finset.card_pos.mpr hC)
    have hmR : (0:ℝ) < C.bad.card := Nat.cast_pos.mpr hm
    have hnear : dist (C.leaderPair s o).1 o ≤ (6/5:ℝ)*clusterMean D C.assign o := by
      simpa only [hp.2] using hc.2.2.1
    have hh := Population.leader_radius_le D (cluster D C.assign o) hD hC
      (cluster_subset _ _ _) (comparisonCost D C.assign) C.bad.card (C.leaderPair s o).1 o
      (clusterMean D C.assign o) (6/5) hP hm (by norm_num)
      (clusterMean_mul_card _ _ _).symm hnear
    have he : ((6/5+2:ℝ)*clusterMean D C.assign o+
        2*comparisonCost D C.assign/((C.bad.card:ℝ)*(cluster D C.assign o).card))*
          (cluster D C.assign o).card =
        (16/5:ℝ)*clusterCost D C.assign o+2*comparisonCost D C.assign/C.bad.card := by
      rw [add_mul,mul_assoc,clusterMean_mul_card]
      field_simp
      ring
    have hh' := mul_le_mul_of_nonneg_right hh hn.le
    rw [he] at hh'
    simpa only [mul_comm] using hh'
  have hsum := Finset.sum_le_sum hpoint
  simp only [Finset.sum_add_distrib,← Finset.mul_sum,Finset.sum_const,nsmul_eq_mul] at hsum
  have hsub := C.correct_covered_subset hD kappa s hs
  have hcard : ((C.covered s).card:ℝ) ≤ C.bad.card := by
    exact_mod_cast Finset.card_le_card hsub
  have hmR : (0:ℝ) < C.bad.card := Nat.cast_pos.mpr hm
  have hc := mul_le_mul_of_nonneg_right hcard
    (show 0 ≤ 2*comparisonCost D C.assign/(C.bad.card:ℝ) by positivity)
  have he : (C.bad.card:ℝ)*(2*comparisonCost D C.assign/C.bad.card) =
      2*comparisonCost D C.assign := by field_simp
  rw [he] at hc
  have hPA : (∑ o ∈ C.covered s, clusterCost D C.assign o) ≤ comparisonCost D C.assign := by
    rw [← comparisonCost_eq D O C.assign C.assigned]
    exact Finset.sum_le_sum_of_subset_of_nonneg (hsub.trans Finset.sdiff_subset)
      (fun o _ _ => clusterCost_nonneg _ _ o)
  linarith

lemma covered_completion_sum (C : Comparison D S O) (hD : D.Nonempty)
    (kappa theta : ℝ) (hk : 0 ≤ kappa) (ht : 0 ≤ theta)
    (s : State V) (hs : C.Correct hD kappa s)
    (hP : 0 < comparisonCost D C.assign) (hm : 0 < C.bad.card) :
    (∑ o ∈ C.covered s, ∑ p ∈ cluster D C.assign o,
      (dist p o + theta*(dist (C.leaderPair s o).1 o+(C.leaderPair s o).2))) ≤
      (1+theta*(2+kappa)*(6/5:ℝ))*(∑ o ∈ C.covered s, clusterCost D C.assign o)+
        theta*kappa*(26/5:ℝ)*comparisonCost D C.assign := by
  have hpoint : ∀ o ∈ C.covered s,
      (∑ p ∈ cluster D C.assign o,
        (dist p o+theta*(dist (C.leaderPair s o).1 o+(C.leaderPair s o).2))) ≤
      (1+theta*(2+kappa)*(6/5:ℝ))*clusterCost D C.assign o+
        theta*kappa*((cluster D C.assign o).card *
          Population.radius D hD (comparisonCost D C.assign) C.bad.card (C.leaderPair s o).1) := by
    intro o ho
    have hp := C.leaderPair_spec s o ho
    have hc := hs.2.2 _ hp.1
    have hnear : dist (C.leaderPair s o).1 o ≤ (6/5:ℝ)*clusterMean D C.assign o := by
      simpa only [hp.2] using hc.2.2.1
    have hrad : (C.leaderPair s o).2 ≤ (1+kappa)*dist (C.leaderPair s o).1 o+
        kappa*Population.radius D hD (comparisonCost D C.assign) C.bad.card (C.leaderPair s o).1 := by
      simpa only [hp.2] using hc.2.2.2.2.2
    have hadd : dist (C.leaderPair s o).1 o+(C.leaderPair s o).2 ≤
        (2+kappa)*(6/5:ℝ)*clusterMean D C.assign o+
        kappa*Population.radius D hD (comparisonCost D C.assign) C.bad.card (C.leaderPair s o).1 := by
      have hh := mul_le_mul_of_nonneg_left hnear (show 0 ≤ 2+kappa by linarith)
      nlinarith
    have hh := mul_le_mul_of_nonneg_left hadd
      (mul_nonneg (Nat.cast_nonneg (cluster D C.assign o).card) ht)
    have he : (cluster D C.assign o).card * theta *
        ((2+kappa)*(6/5:ℝ)*clusterMean D C.assign o+
        kappa*Population.radius D hD (comparisonCost D C.assign) C.bad.card (C.leaderPair s o).1) =
      theta*(2+kappa)*(6/5:ℝ)*clusterCost D C.assign o+
        theta*kappa*((cluster D C.assign o).card *
          Population.radius D hD (comparisonCost D C.assign) C.bad.card (C.leaderPair s o).1) := by
      rw [← clusterMean_mul_card D C.assign o]
      ring
    rw [he] at hh
    simp only [Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul]
    change clusterCost D C.assign o + _ ≤ _
    nlinarith
  have hh := Finset.sum_le_sum hpoint
  conv at hh => rhs; rw [Finset.sum_add_distrib,← Finset.mul_sum,← Finset.mul_sum]
  have hp := mul_le_mul_of_nonneg_left (C.covered_population_sum hD kappa s hs hP hm)
    (mul_nonneg ht hk)
  nlinarith

lemma uncovered_completion_sum (C : Comparison D S O) (hD : D.Nonempty)
    (kappa Δ : ℝ) (s : State V) (hs : C.Correct hD kappa s) (hΔ : 0 ≤ Δ)
    (J : Finset V) (o : V) :
    (∑ p ∈ cluster D C.assign o, if p ∈ J then dist p o else reference S Δ s p) ≤
      (37/20:ℝ)*clusterCost D C.assign o+61*(∑ p ∈ C.near o, reference S Δ s p) := by
  classical
  let X := cluster D C.assign o
  let H := reference S Δ s
  have hH : ∀ p, 0 ≤ H p := fun p => reference_nonneg S Δ s p hΔ
    (C.correct_radii_nonneg hD kappa s hs)
  by_cases hX : X.Nonempty
  · have hn : (0:ℝ) < X.card := Nat.cast_pos.mpr (Finset.card_pos.mpr hX)
    let T := ∑ p ∈ C.near o, H p
    have hT : 0 ≤ T := Finset.sum_nonneg (fun p _ => hH p)
    have htpos : 0 ≤ 60*T/(X.card:ℝ) := div_nonneg (by positivity) hn.le
    have hbound : ∀ p ∈ X, (if p ∈ J then dist p o else H p) ≤
        (37/20:ℝ)*dist p o+(if p ∈ C.near o then H p else 0)+60*T/X.card := by
      intro p hp
      by_cases hpJ : p ∈ J
      · rw [ite_eq_left hpJ]
        have hz : 0 ≤ (if p ∈ C.near o then H p else 0) := by
          split_ifs
          · exact hH p
          · exact le_rfl
        nlinarith [dist_nonneg (x:=p) (y:=o)]
      · rw [ite_eq_right hpJ]
        by_cases hpN : p ∈ C.near o
        · rw [ite_eq_left hpN]
          nlinarith [dist_nonneg (x:=p) (y:=o)]
        · rw [ite_eq_right hpN,add_zero]
          have hfar : (6/5:ℝ)*clusterMean D C.assign o < dist p o := by
            apply lt_of_not_ge
            intro hh
            exact hpN (Finset.mem_filter.mpr ⟨hp,hh⟩)
          exact NearClients.main_far_bound X hX o p (clusterMean D C.assign o) H
            (clusterMean_mul_card D C.assign o).symm (fun q _ => hH q)
            (fun q _ => by simpa only [dist_comm o q] using reference_triangle S Δ s o q)
            (reference_triangle S Δ s p o) hfar
    have hh := Finset.sum_le_sum hbound
    simp only [Finset.sum_add_distrib,← Finset.mul_sum,Finset.sum_const,nsmul_eq_mul] at hh
    have hnear : (∑ p ∈ X, if p ∈ C.near o then H p else 0) = T := by
      rw [← Finset.sum_filter]
      have he : X.filter (fun p => p ∈ C.near o) = C.near o := by
        rw [Finset.filter_mem_eq_inter]
        exact Finset.inter_eq_right.mpr (show C.near o ⊆ X from Finset.filter_subset _ _)
      rw [he]
    rw [hnear] at hh
    have he : (X.card:ℝ)*(60*T/X.card) = 60*T := by field_simp
    rw [he] at hh
    change (∑ p ∈ X, if p ∈ J then dist p o else H p) ≤
      (37/20:ℝ)*(∑ p ∈ X, dist p o)+61*T
    linarith
  · have he : cluster D C.assign o = ∅ := Finset.not_nonempty_iff_eq_empty.mp hX
    have ht : 0 ≤ ∑ p ∈ C.near o, reference S Δ s p := Finset.sum_nonneg (fun p _ => hH p)
    simp only [he,Finset.sum_empty,clusterCost,mul_zero,zero_add]
    positivity

end MetricKMedianRecovery.Sampling.Comparison

end OAI
