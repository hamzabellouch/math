import OAI.Combinatorics.KMedianRecovery.Refined.Endpoint

namespace OAI

/-! Reference-distance routes, endpoint partitions, covered centers, and the total radius bound. -/

namespace MetricKMedianRecovery.RefinedRecovery
namespace EndpointData
variable {I : Input} {μ : ℚ} {L₀ : ℝ} {C : Certificate I μ L₀}
variable (E : EndpointData C)

lemma finalReference_le_first (p : I.Point) : E.finalReference p ≤ E.firstReference p := by
  let _ := I.pointMetric
  exact Sampling.reference_extend_le I.anchor E.diameter E.first E.appended p

lemma finalInternal_subset : E.finalInternal ⊆ E.firstInternal := by
  let _ := I.pointMetric
  exact Sampling.assignedOriginals_extend_subset _ _ _ _ _ _

lemma firstInternal_clients : E.firstInternal ⊆ I.metric.clients := by
  intro p hp
  simp only [firstInternal, Sampling.assignedOriginals, Finset.mem_filter] at hp
  exact hp.1
lemma finalInternal_clients : E.finalInternal ⊆ I.metric.clients := by
  intro p hp
  simp only [finalInternal, Sampling.assignedOriginals, Finset.mem_filter] at hp
  exact hp.1

lemma large_subset : E.large ⊆ E.remaining := Finset.filter_subset _ _
lemma small_subset : E.small ⊆ E.remaining := Finset.sdiff_subset
lemma remaining_subset : E.remaining ⊆ E.firstRemaining := Finset.sdiff_subset
lemma firstRemaining_subset : E.firstRemaining ⊆ C.bad := Finset.sdiff_subset

lemma sum_partition (h : EndpointConditions C E) (f : I.Point → ℝ) :
    (∑ i ∈ C.centers, f i) =
      (∑ i ∈ C.good, f i) + (∑ i ∈ E.firstCovered, f i) +
      (∑ i ∈ E.secondCovered, f i) + (∑ i ∈ E.large, f i) + ∑ i ∈ E.small, f i := by
  have h₀ : (∑ i ∈ C.bad, f i) + (∑ i ∈ C.good, f i) = ∑ i ∈ C.centers, f i :=
    Finset.sum_sdiff C.good_subset
  have h₁ : (∑ i ∈ E.firstRemaining, f i) + (∑ i ∈ E.firstCovered, f i) = ∑ i ∈ C.bad, f i :=
    Finset.sum_sdiff h.first_bad
  have h₂ : (∑ i ∈ E.remaining, f i) + (∑ i ∈ E.secondCovered, f i) = ∑ i ∈ E.firstRemaining, f i :=
    Finset.sum_sdiff h.second_bad
  have h₃ : (∑ i ∈ E.small, f i) + (∑ i ∈ E.large, f i) = ∑ i ∈ E.remaining, f i :=
    Finset.sum_sdiff E.large_subset
  linarith

lemma remaining_sum (f : I.Point → ℝ) :
    (∑ i ∈ E.large, f i) + (∑ i ∈ E.small, f i) = ∑ i ∈ E.remaining, f i := by
  have h := Finset.sum_sdiff (f := f) E.large_subset
  change (∑ i ∈ E.small, f i) + (∑ i ∈ E.large, f i) = _ at h
  linarith

lemma firstRemaining_sum (h : EndpointConditions C E) (f : I.Point → ℝ) :
    (∑ i ∈ E.secondCovered, f i) + (∑ i ∈ E.large, f i) + (∑ i ∈ E.small, f i) =
      ∑ i ∈ E.firstRemaining, f i := by
  have hh := Finset.sum_sdiff (f := f) h.second_bad
  change (∑ i ∈ E.remaining, f i) + (∑ i ∈ E.secondCovered, f i) = _ at hh
  linarith [E.remaining_sum f]

lemma covered_subset (h : EndpointConditions C E) : E.covered ⊆ C.bad := by
  exact Finset.union_subset h.first_bad (h.second_bad.trans E.firstRemaining_subset)

lemma covered_nonempty (h : EndpointConditions C E) (i : I.Point) (hi : i ∈ E.covered) :
    (C.group i).Nonempty := ⟨E.leader i, h.leader_mem i hi⟩

lemma covered_disjoint (h : EndpointConditions C E) : Disjoint E.firstCovered E.secondCovered := by
  apply Finset.disjoint_left.mpr
  intro i hi₁ hi₂
  exact (Finset.mem_sdiff.mp (h.second_bad hi₂)).2 hi₁

lemma first_nonneg (h : EndpointConditions C E) (p : I.Point) : 0 ≤ E.firstReference p := by
  let _ := I.pointMetric
  exact Sampling.reference_nonneg I.anchor E.diameter E.first p h.diameter_nonneg h.old_nonneg

lemma final_nonneg (h : EndpointConditions C E) (p : I.Point) : 0 ≤ E.finalReference p := by
  let _ := I.pointMetric
  exact Sampling.reference_nonneg I.anchor E.diameter E.final p h.diameter_nonneg (by
    intro z hz
    rcases List.mem_append.mp hz with hz | hz
    · exact h.old_nonneg z hz
    · exact h.new_nonneg z hz)

lemma firstMass_nonneg (h : EndpointConditions C E) (i : I.Point) : 0 ≤ E.firstMass i :=
  Finset.sum_nonneg (fun p _ => E.first_nonneg h p)

lemma internal_bound (h : EndpointConditions C E) :
    (∑ p ∈ E.finalInternal, E.finalReference p) ≤ (μ : ℝ)^3*C.price := by
  let _ := I.pointMetric
  exact (Sampling.internalCost_extend_le I.metric.clients I.anchor (C.nonproxy \ E.first.deleted)
    E.diameter E.first E.appended h.diameter_nonneg h.old_nonneg).trans h.internal_stop

lemma proxy_available (h : EndpointConditions C E) (i : I.Point) (hi : i ∈ C.good) :
    C.proxy i ∈ I.anchor \ E.first.deleted := by
  refine Finset.mem_sdiff.mpr ⟨C.proxy_mem i hi, ?_⟩
  intro hd
  have ha := h.deleted_subset hd
  exact (Finset.mem_sdiff.mp ha).2 (Finset.mem_image.mpr ⟨i, hi, rfl⟩)

lemma reference_proxy (h : EndpointConditions C E) (i : I.Point) (hi : i ∈ C.good) (p : I.Point) :
    E.finalReference p ≤ (I.metric.distance p (C.proxy i) : ℝ) := by
  let _ := I.pointMetric
  exact Sampling.reference_le_real I.anchor E.diameter E.final p (C.proxy i) (E.proxy_available h i hi)

lemma leaf_route (h : EndpointConditions C E) (i : I.Point) (hi : i ∈ E.covered) (p : I.Point) :
    E.finalReference p ≤ (I.metric.distance p i : ℝ) +
      (I.metric.distance (E.leader i) i : ℝ) + E.radius i := by
  let _ := I.pointMetric
  have hleaf : (E.leader i, E.radius i) ∈ E.final.leaves := by
    rcases Finset.mem_union.mp hi with hi | hi
    · exact List.mem_append_left _ (h.first_leaf i hi)
    · exact List.mem_append_right _ (h.second_leaf i hi)
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hleaf
  have hr := Sampling.reference_le_leaf I.anchor E.diameter E.final p j (E.leader i, E.radius i) hj
  have ht := dist_triangle p i (E.leader i)
  rw [dist_comm i (E.leader i)] at ht
  apply hr.trans
  change dist p (E.leader i) + E.radius i ≤ dist p i + dist (E.leader i) i + E.radius i
  linarith only [ht]

lemma first_near_route (h : EndpointConditions C E) (hμ : 0 < (μ : ℝ))
    (i : I.Point) (hc : (C.group i).Nonempty) (p : I.Point) :
    E.finalReference p ≤ (I.metric.distance p i : ℝ) +
      (1+(μ : ℝ))*C.mean i + E.firstMass i/(Analysis.q μ * (C.group i).card) := by
  let _ := I.pointMetric
  have hb := Analysis.near_bound (C.group i) hc i (C.mean i) μ hμ E.firstReference
    (C.mean_mul_card i).symm (fun p _ => E.first_nonneg h p)
    (fun p _ => by
      have hh := Sampling.reference_triangle I.anchor E.diameter E.first i p
      rwa [dist_comm i p] at hh)
  have ht := Sampling.reference_triangle I.anchor E.diameter E.first p i
  have hm := E.finalReference_le_first p
  change E.firstReference i ≤ (1+(μ : ℝ))*C.mean i + E.firstMass i/(Analysis.q μ * (C.group i).card) at hb
  change E.firstReference p ≤ (I.metric.distance p i : ℝ) + E.firstReference i at ht
  linarith

lemma fraction_nonneg (i : I.Point) : 0 ≤ E.fraction i := by
  unfold fraction
  positivity

lemma fraction_le_one (i : I.Point) : E.fraction i ≤ 1 := by
  unfold fraction
  by_cases he : (C.group i).Nonempty
  · apply (div_le_iff₀ (Nat.cast_pos.mpr he.card_pos : (0 : ℝ) < (C.group i).card)).mpr
    simpa only [one_mul] using (show ((C.group i ∩ E.finalInternal).card : ℝ) ≤ (C.group i).card by
      exact_mod_cast Finset.card_le_card Finset.inter_subset_left)
  · simp [Finset.not_nonempty_iff_eq_empty.mp he]

lemma fraction_count (i : I.Point) (hc : (C.group i).Nonempty) :
    ((C.group i ∩ E.finalInternal).card : ℝ) = E.fraction i * (C.group i).card := by
  exact (div_mul_cancel₀ _ (ne_of_gt (Nat.cast_pos.mpr hc.card_pos : (0 : ℝ) < (C.group i).card))).symm

lemma fraction_lt_third (h : EndpointConditions C E) (i : I.Point) (hi : i ∈ E.secondCovered) :
    E.fraction i < 1/3 := by
  have hiA : i ∈ E.covered := Finset.mem_union_right _ hi
  have hc := E.covered_nonempty h i hiA
  unfold fraction
  apply (div_lt_iff₀ (Nat.cast_pos.mpr hc.card_pos : (0 : ℝ) < (C.group i).card)).mpr
  have hn : ((C.group i ∩ E.finalInternal).card : ℝ) ≤ (C.group i ∩ E.firstInternal).card := by
    exact_mod_cast Finset.card_le_card (Finset.inter_subset_inter_left E.finalInternal_subset)
  linarith [h.eligible i hi]

lemma radius_total (h : EndpointConditions C E) (hμ : (μ : ℝ) ≤ 1/4) (hm : 0 < C.bad.card) :
    (∑ i ∈ E.covered, (C.group i).card * C.populationRadius (E.leader i)) ≤ (11/2 : ℝ)*C.price := by
  let _ := I.pointMetric
  apply Analysis.radius_sum I.metric.clients C.clients_nonempty E.covered C.group id E.leader C.mean
    C.price C.bad.card C.positive_cost hm (Finset.card_le_card (E.covered_subset h))
    (E.covered_nonempty h) (fun _ _ => I.cluster_subset _ _)
    (fun i _ => (C.mean_mul_card i).symm)
  · simpa only [C.mean_mul_card] using C.partCost_subsum E.covered ((E.covered_subset h).trans Finset.sdiff_subset)
  · intro i hi
    rcases Finset.mem_union.mp hi with hi | hi
    · have he := mul_le_mul_of_nonneg_right (show 1+(μ : ℝ) ≤ (3/2 : ℝ) by linarith) (C.mean_nonneg i)
      exact (h.first_near i hi).trans he
    · exact h.second_near i hi

end EndpointData
end MetricKMedianRecovery.RefinedRecovery

end OAI
