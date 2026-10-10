import OAI.Combinatorics.KMedianRecovery.Refined.Routes

namespace OAI

/-! The refined bound for total comparison-cluster charge. -/

namespace MetricKMedianRecovery.RefinedRecovery
namespace EndpointData
variable {I : Input} {μ : ℚ} {L₀ : ℝ} {C : Certificate I μ L₀}
variable (E : EndpointData C)
noncomputable def lostCharge (i : I.Point) : ℝ :=
  ∑ p ∈ C.group i ∩ (E.firstInternal \ E.finalInternal), E.firstReference p

noncomputable def nearExternalCharge (i : I.Point) : ℝ :=
  ∑ p ∈ C.near (3/2) i \ E.finalInternal, E.finalReference p

lemma remaining_bad (i : I.Point) (hi : i ∈ E.remaining) : i ∈ C.bad :=
  E.firstRemaining_subset (E.remaining_subset hi)

lemma remaining_not_covered (i : I.Point) (hi : i ∈ E.remaining) : i ∉ E.covered := by
  intro hh
  rcases Finset.mem_union.mp hh with hh | hh
  · exact (Finset.mem_sdiff.mp (E.remaining_subset hi)).2 hh
  · exact (Finset.mem_sdiff.mp hi).2 hh

lemma good_clusterCharge (h : EndpointConditions C E) (θ : ℝ) (hθ : θ ≤ 1)
    (i : I.Point) (hi : i ∈ C.good) :
    E.clusterCharge θ i ≤ ∑ p ∈ C.group i, (I.metric.distance p (C.proxy i) : ℝ) := by
  unfold clusterCharge internalCharge baseCharge
  simp only [ite_eq_left hi]
  exact Analysis.good_charge _ _ _ hθ E.finalReference
    (fun p => (I.metric.distance p (C.proxy i) : ℝ)) _ E.covered
    (fun p _ => E.reference_proxy h i hi p)

lemma good_charge_sum (h : EndpointConditions C E) (θ : ℝ) (hθ : θ ≤ 1) :
    (∑ i ∈ C.good, E.clusterCharge θ i) ≤ (∑ i ∈ C.good, C.partCost i) + (μ : ℝ)*C.price :=
  (Finset.sum_le_sum (E.good_clusterCharge h θ hθ)).trans C.proxy_cost

lemma first_clusterCharge (h : EndpointConditions C E) (θ : ℝ) (ht0 : 0 ≤ θ) (ht1 : θ ≤ 1)
    (hμ : 0 ≤ (μ : ℝ)) (i : I.Point) (hi : i ∈ E.firstCovered) :
    E.clusterCharge θ i ≤
      (1+2*θ*(1+(μ : ℝ)))*C.partCost i + θ*(μ : ℝ)^3*(1+(μ : ℝ))*C.partCost i +
      θ*(μ : ℝ)^3*(C.group i).card*C.populationRadius (E.leader i) := by
  have hiA : i ∈ E.covered := Finset.mem_union_left _ hi
  have hig : i ∉ C.good := (Finset.mem_sdiff.mp (h.first_bad hi)).2
  unfold clusterCharge internalCharge baseCharge
  simp only [ite_eq_right hig, ite_eq_left hiA]
  exact Analysis.first_covered (C.group i) E.finalInternal E.finalReference
    (fun p => (I.metric.distance p i : ℝ)) _ E.covered i hiA θ ((μ : ℝ)^3) (1+(μ : ℝ))
    (C.mean i) (I.metric.distance (E.leader i) i) (E.radius i) (C.populationRadius (E.leader i))
    (C.partCost i) ht0 ht1 (by positivity) (fun _ _ => rfl)
    (fun p _ => E.leaf_route h i hiA p) (C.mean_mul_card i) rfl
    (h.first_near i hi) (h.radius_upper i hiA)

lemma second_clusterCharge (h : EndpointConditions C E) (θ : ℝ) (ht0 : 0 ≤ θ) (ht1 : θ ≤ 1)
    (hμ : 0 < (μ : ℝ)) (hμ1 : (μ : ℝ) ≤ 1/4) (i : I.Point) (hi : i ∈ E.secondCovered) :
    E.clusterCharge θ i ≤ (1+2*θ)*C.partCost i + θ*(μ : ℝ)^3*(3/2)*E.fraction i*C.partCost i +
      θ*(μ : ℝ)^3*E.fraction i*(C.group i).card*C.populationRadius (E.leader i) +
      E.firstMass i/Analysis.q μ := by
  have hiA : i ∈ E.covered := Finset.mem_union_right _ hi
  have hc := E.covered_nonempty h i hiA
  have hig : i ∉ C.good := (Finset.mem_sdiff.mp (E.covered_subset h hiA)).2
  unfold clusterCharge internalCharge baseCharge
  simp only [ite_eq_right hig, ite_eq_left hiA]
  exact Analysis.second_covered (C.group i) E.finalInternal hc E.finalReference
    (fun p => (I.metric.distance p i : ℝ)) _ E.covered i hiA θ ((μ : ℝ)^3) μ (C.mean i)
    (I.metric.distance (E.leader i) i) (E.radius i) (C.populationRadius (E.leader i))
    (C.partCost i) (E.firstMass i) (Analysis.q μ) (E.fraction i)
    ht0 ht1 (by positivity) hμ.le hμ1 (C.partCost_nonneg i) (Analysis.q_pos hμ)
    (E.firstMass_nonneg h i) (E.fraction_nonneg i) (E.fraction_lt_third h i hi).le
    (fun _ _ => rfl) (fun p _ _ => E.first_near_route h hμ i hc p)
    (C.mean_mul_card i) rfl (h.second_near i hi) (h.radius_upper i hiA) (E.fraction_count i hc)

lemma large_clusterCharge (h : EndpointConditions C E) (θ : ℝ) (ht1 : θ ≤ 1)
    (hμ : 0 < (μ : ℝ)) (i : I.Point) (hi : i ∈ E.large) :
    E.clusterCharge θ i ≤ (1+(2/3 : ℝ)*(1+(μ : ℝ)))*C.partCost i +
      E.firstMass i/Analysis.q μ + E.lostCharge i := by
  have hir := E.large_subset hi
  have hig : i ∉ C.good := (Finset.mem_sdiff.mp (E.remaining_bad i hir)).2
  have hiA := E.remaining_not_covered i hir
  by_cases hc : (C.group i).Nonempty
  · unfold clusterCharge internalCharge baseCharge
    simp only [ite_eq_right hig, ite_eq_right hiA]
    exact Analysis.uncovered_large (C.group i) E.finalInternal E.firstInternal hc E.finalInternal_subset
      E.finalReference E.firstReference (fun p => (I.metric.distance p i : ℝ)) _ E.covered
      θ (1+(μ : ℝ)) (C.mean i) (C.partCost i) (E.firstMass i) (Analysis.q μ)
      ht1 (by linarith) (Analysis.q_pos hμ) (E.firstMass_nonneg h i)
      (fun _ _ => Rat.cast_nonneg.mpr (I.metric.distance_nonneg _ _)) rfl (C.mean_mul_card i)
      (fun p _ => E.finalReference_le_first p) (fun p _ => E.first_near_route h hμ i hc p)
      (Finset.mem_filter.mp hi).2
  · have he := Finset.not_nonempty_iff_eq_empty.mp hc
    simp [clusterCharge, he, C.partCost_empty i he, firstMass, Certificate.near, lostCharge]

lemma small_clusterCharge (h : EndpointConditions C E) (θ : ℝ) (ht1 : θ ≤ 1)
    (hμ : 0 < (μ : ℝ)) (i : I.Point) (hi : i ∈ E.small) :
    E.clusterCharge θ i ≤ (1+(2/3 : ℝ)*(1+(μ : ℝ)))*C.partCost i +
      E.firstMass i/Analysis.q μ + E.nearExternalCharge i := by
  have hir := E.small_subset hi
  have hig : i ∉ C.good := (Finset.mem_sdiff.mp (E.remaining_bad i hir)).2
  have hiA := E.remaining_not_covered i hir
  by_cases hc : (C.group i).Nonempty
  · unfold clusterCharge internalCharge baseCharge
    simp only [ite_eq_right hig, ite_eq_right hiA]
    exact Analysis.uncovered_small (C.group i) E.finalInternal hc E.finalReference
      (fun p => (I.metric.distance p i : ℝ)) _ E.covered
      θ (1+(μ : ℝ)) (C.mean i) (C.partCost i) (E.firstMass i) (Analysis.q μ)
      ht1 (by linarith) (Analysis.q_pos hμ) (E.firstMass_nonneg h i)
      (fun _ _ => Rat.cast_nonneg.mpr (I.metric.distance_nonneg _ _)) rfl
      (fun p _ => E.first_near_route h hμ i hc p)
  · have he := Finset.not_nonempty_iff_eq_empty.mp hc
    simp [clusterCharge, he, C.partCost_empty i he, firstMass, Certificate.near, nearExternalCharge]

lemma lostCharge_bound (h : EndpointConditions C E) :
    (∑ i ∈ E.large, E.lostCharge i) ≤ (μ : ℝ)^3*C.price := by
  have hA : E.large ⊆ C.centers := fun i hi => (Finset.mem_sdiff.mp (E.remaining_bad i (E.large_subset hi))).1
  have hh := C.cluster_subsum E.large hA (E.firstInternal \ E.finalInternal) E.firstReference
    (fun p _ => E.first_nonneg h p)
  apply hh.trans
  apply le_trans _ h.internal_stop
  exact Finset.sum_le_sum_of_subset_of_nonneg (fun _ hp => (Finset.mem_sdiff.mp (Finset.mem_inter.mp hp).1).1)
    (fun p _ _ => E.first_nonneg h p)

lemma nearExternalCharge_bound (h : EndpointConditions C E) :
    (∑ i ∈ E.small, E.nearExternalCharge i) ≤ (μ : ℝ)^3*C.price := by
  apply le_trans _ h.second_mass_stop
  apply Finset.sum_le_sum
  intro i _
  exact Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset (fun p _ _ => E.final_nonneg h p)

lemma fraction_cost_bound :
    (∑ i ∈ E.secondCovered, E.fraction i * C.partCost i) ≤ ∑ i ∈ E.secondCovered, C.partCost i := by
  apply Finset.sum_le_sum
  intro i _
  simpa only [one_mul] using mul_le_mul_of_nonneg_right (E.fraction_le_one i) (C.partCost_nonneg i)

lemma weighted_radius_bound (h : EndpointConditions C E) (hμ1 : (μ : ℝ) ≤ 1/4) (hm : 0 < C.bad.card) :
    (∑ i ∈ E.firstCovered, (C.group i).card*C.populationRadius (E.leader i)) +
      (∑ i ∈ E.secondCovered, E.fraction i*(C.group i).card*C.populationRadius (E.leader i)) ≤
      (11/2 : ℝ)*C.price := by
  apply le_trans _ (E.radius_total h hμ1 hm)
  rw [covered, Finset.sum_union (E.covered_disjoint h)]
  apply add_le_add le_rfl (Finset.sum_le_sum _)
  intro i _
  have hh := mul_le_mul_of_nonneg_right (E.fraction_le_one i)
    (mul_nonneg (Nat.cast_nonneg (C.group i).card) (C.populationRadius_nonneg hm (E.leader i)))
  simpa only [one_mul, mul_assoc] using hh

lemma totalCharge_eq_completion (θ : ℝ) :
    E.totalCharge θ = 2*(∑ p ∈ E.finalInternal, E.finalReference p) +
      (∑ p ∈ E.finalInternal, E.internalCharge θ (I.assign C.centers p) p) +
      ∑ p ∈ I.metric.clients \ E.finalInternal, E.baseCharge θ p := by
  classical
  have hc : (∑ i ∈ C.centers, E.clusterCharge θ i) =
      ∑ p ∈ I.metric.clients, if p ∈ E.finalInternal then
        E.internalCharge θ (I.assign C.centers p) p else E.baseCharge θ p := by
    rw [← I.cluster_partition C.centers C.centers_nonempty]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro p hp
    have ha := (I.cluster_mem C.centers p i).mp hp |>.2
    rw [ha]
  rw [totalCharge, hc]
  simp only [Finset.sum_ite, Finset.filter_mem_eq_inter, Finset.filter_notMem_eq_sdiff,
    Finset.inter_eq_right.mpr E.finalInternal_clients, add_assoc]

theorem refined_charge_bound (h : EndpointConditions C E) (θ : ℝ)
    (hμ : 0 < (μ : ℝ)) (hμ1 : (μ : ℝ) ≤ 1/4)
    (ht0 : (1/3 : ℝ) ≤ θ) (ht1 : θ ≤ 1) (hm : 0 < C.bad.card) :
    E.totalCharge θ ≤ (1+2*θ*(1+(μ : ℝ))+(μ : ℝ)+11*(μ : ℝ)^3+(μ : ℝ)^3/Analysis.q μ)*C.price := by
  have ht : 0 ≤ θ := by linarith
  have hcost := (E.sum_partition h C.partCost).symm.trans C.partCost_sum
  have hfirst := Finset.sum_le_sum (E.first_clusterCharge h θ ht ht1 hμ.le)
  have hsecond := Finset.sum_le_sum (E.second_clusterCharge h θ ht ht1 hμ hμ1)
  have hlarge := Finset.sum_le_sum (E.large_clusterCharge h θ ht1 hμ)
  have hsmall := Finset.sum_le_sum (E.small_clusterCharge h θ ht1 hμ)
  have htotal := Analysis.sum_five_charges (μ : ℝ) θ ((μ : ℝ)^3) (Analysis.q μ) C.price
    (∑ i ∈ C.good, C.partCost i) (∑ i ∈ E.firstCovered, C.partCost i)
    (∑ i ∈ E.secondCovered, C.partCost i) (∑ i ∈ E.large, C.partCost i) (∑ i ∈ E.small, C.partCost i)
    (∑ i ∈ E.secondCovered, E.fraction i*C.partCost i)
    (∑ i ∈ E.firstCovered, (C.group i).card*C.populationRadius (E.leader i))
    (∑ i ∈ E.secondCovered, E.fraction i*(C.group i).card*C.populationRadius (E.leader i))
    (∑ i ∈ E.secondCovered, E.firstMass i) (∑ i ∈ E.large, E.firstMass i) (∑ i ∈ E.small, E.firstMass i)
    (∑ i ∈ E.large, E.lostCharge i) (∑ i ∈ E.small, E.nearExternalCharge i)
    (∑ p ∈ E.finalInternal, E.finalReference p)
    (∑ i ∈ C.good, E.clusterCharge θ i) (∑ i ∈ E.firstCovered, E.clusterCharge θ i)
    (∑ i ∈ E.secondCovered, E.clusterCharge θ i) (∑ i ∈ E.large, E.clusterCharge θ i) (∑ i ∈ E.small, E.clusterCharge θ i)
    hμ.le hμ1 ht0 ht1 (by positivity) (Analysis.q_pos hμ)
    (Finset.sum_nonneg (fun i _ => C.partCost_nonneg i))
    (Finset.sum_nonneg (fun i _ => C.partCost_nonneg i))
    (Finset.sum_nonneg (fun i _ => C.partCost_nonneg i))
    (Finset.sum_nonneg (fun i _ => C.partCost_nonneg i))
    (Finset.sum_nonneg (fun i _ => C.partCost_nonneg i))
    hcost E.fraction_cost_bound (E.weighted_radius_bound h hμ1 hm)
    (by rw [E.firstRemaining_sum h]; exact h.first_mass_stop)
    (E.lostCharge_bound h) (E.nearExternalCharge_bound h) (E.internal_bound h)
    (E.good_charge_sum h θ ht1)
    (by simpa only [Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum] using hfirst)
    (by simpa only [Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum, Finset.sum_div] using hsecond)
    (by simpa only [Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum, Finset.sum_div] using hlarge)
    (by simpa only [Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum, Finset.sum_div] using hsmall)
  simpa only [totalCharge, E.sum_partition h (E.clusterCharge θ), add_assoc] using htotal

theorem refined_charge_bound_six_mu (h : EndpointConditions C E) (θ : ℝ)
    (hμ : 0 < (μ : ℝ)) (hμ1 : (μ : ℝ) ≤ 1/4)
    (ht0 : 1/Real.exp 1 < θ) (ht1 : θ ≤ 1/Real.exp 1+(μ : ℝ)) (hm : 0 < C.bad.card) :
    E.totalCharge θ ≤ (1+2/Real.exp 1+6*(μ : ℝ))*C.price := by
  have htthird : (1/3 : ℝ) ≤ θ := (Analysis.third_lt_inverse_e.trans ht0).le
  have htone : θ ≤ 1 := by linarith [Analysis.inverse_e_lt_half]
  exact (E.refined_charge_bound h θ hμ hμ1 htthird htone hm).trans
    (mul_le_mul_of_nonneg_right (Analysis.explicit_coefficient hμ hμ1 ht1) C.positive_cost.le)

end EndpointData
end MetricKMedianRecovery.RefinedRecovery

end OAI
