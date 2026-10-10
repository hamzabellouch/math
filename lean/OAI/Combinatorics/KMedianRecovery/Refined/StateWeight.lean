import OAI.Combinatorics.KMedianRecovery.Refined.Routes

namespace OAI

/-! The actual sampling-state weight bound and its first-stage and extended-state consequences. -/

namespace MetricKMedianRecovery.RefinedRecovery
namespace Certificate
variable {I : Input} {μ : ℚ} {L₀ : ℝ}

lemma uncovered_weight (C : Certificate I μ L₀) (H : I.Point → ℝ)
    (hH : ∀ p, 0 ≤ H p)
    (htri : ∀ p x, H p ≤ (I.metric.distance p x : ℝ) + H x)
    (hμ : 0 < (μ : ℝ)) (i : I.Point) :
    (∑ p ∈ C.group i, H p) ≤ (2+(μ : ℝ))*C.partCost i +
      (∑ p ∈ C.near (1+(μ : ℝ)) i, H p)/Analysis.q μ := by
  by_cases hc : (C.group i).Nonempty
  · let _ := I.pointMetric
    have hn : (0 : ℝ) < (C.group i).card := Nat.cast_pos.mpr hc.card_pos
    have hb := Analysis.near_bound (C.group i) hc i (C.mean i) μ hμ H
      (C.mean_mul_card i).symm (fun p _ => hH p) (fun p _ => by
        change H i ≤ (I.metric.distance p i : ℝ) + H p
        have hh := htri i p
        simpa only [I.metric.distance_symm i p] using hh)
    change H i ≤ (1+(μ : ℝ))*C.mean i +
      (∑ p ∈ C.near (1+(μ : ℝ)) i, H p)/(Analysis.q μ*(C.group i).card) at hb
    calc
      _ ≤ ∑ p ∈ C.group i, ((I.metric.distance p i : ℝ) +
          ((1+(μ : ℝ))*C.mean i + (∑ p ∈ C.near (1+(μ : ℝ)) i, H p)/(Analysis.q μ*(C.group i).card))) := by
        apply Finset.sum_le_sum
        intro p _
        linarith [htri p i]
      _ = (2+(μ : ℝ))*C.partCost i + (∑ p ∈ C.near (1+(μ : ℝ)) i, H p)/Analysis.q μ := by
        rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
        change C.partCost i + _ = _
        rw [← C.mean_mul_card i]
        field_simp
        ring
  · have he := Finset.not_nonempty_iff_eq_empty.mp hc
    simp [he, C.partCost_empty i he, near]

theorem state_weight_bound (C : Certificate I μ L₀)
    (s : Sampling.State I.Point) (Δ : ℝ) (A : Finset I.Point) (leader : I.Point → I.Point)
    (radius : I.Point → ℝ) (hμ : 0 < (μ : ℝ)) (hμ1 : (μ : ℝ) ≤ 1/4) (hm : 0 < C.bad.card)
    (hΔ : 0 ≤ Δ) (hdel : s.deleted ⊆ C.nonproxy) (hpos : ∀ z ∈ s.leaves, 0 ≤ z.2)
    (hA : A ⊆ C.bad) (hw : ∀ i ∈ A, leader i ∈ C.group i)
    (hl : ∀ i ∈ A, (leader i, radius i) ∈ s.leaves)
    (hn : ∀ i ∈ A, (I.metric.distance (leader i) i : ℝ) ≤ (3/2 : ℝ)*C.mean i)
    (hr : ∀ i ∈ A, radius i ≤ (1+(μ : ℝ)^3)*(I.metric.distance (leader i) i : ℝ) +
      (μ : ℝ)^3*C.populationRadius (leader i)) :
    letI := I.pointMetric
    let H := Sampling.reference I.anchor Δ s
    (∑ p ∈ I.metric.clients, H p) ≤ 6*C.price +
      (∑ i ∈ C.bad \ A, ∑ p ∈ C.near (1+(μ : ℝ)) i, H p)/Analysis.q μ := by
  let _ := I.pointMetric
  let H := Sampling.reference I.anchor Δ s
  change (∑ p ∈ I.metric.clients, H p) ≤ _
  let B : ℝ := 1+(2+(μ : ℝ)^3)*(3/2)
  have hκ : 0 ≤ (μ : ℝ)^3 := by positivity
  have hH : ∀ p, 0 ≤ H p := fun p => Sampling.reference_nonneg _ _ _ _ hΔ hpos
  have hroute : ∀ p x, H p ≤ (I.metric.distance p x : ℝ) + H x :=
    Sampling.reference_triangle I.anchor Δ s
  have hproxy : ∀ i ∈ C.good, ∀ p ∈ C.group i, H p ≤ (I.metric.distance p (C.proxy i) : ℝ) := by
    intro i hi p _
    apply Sampling.reference_le_real
    refine Finset.mem_sdiff.mpr ⟨C.proxy_mem i hi, ?_⟩
    intro hd
    exact (Finset.mem_sdiff.mp (hdel hd)).2 (Finset.mem_image.mpr ⟨i, hi, rfl⟩)
  have hg : (∑ i ∈ C.good, ∑ p ∈ C.group i, H p) ≤
      (∑ i ∈ C.good, C.partCost i) + (μ : ℝ)*C.price :=
    (Finset.sum_le_sum (fun i hi => Finset.sum_le_sum (hproxy i hi))).trans C.proxy_cost
  have hleaf : ∀ i ∈ A, ∀ p, H p ≤ (I.metric.distance p i : ℝ) +
      (I.metric.distance (leader i) i : ℝ) + radius i := by
    intro i hi p
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp (hl i hi)
    have hh := Sampling.reference_le_leaf I.anchor Δ s p j (leader i, radius i) hj
    have ht := dist_triangle p i (leader i)
    rw [dist_comm i (leader i)] at ht
    apply hh.trans
    change dist p (leader i) + radius i ≤ dist p i + dist (leader i) i + radius i
    linarith only [ht]
  have hcovered : ∀ i ∈ A, (∑ p ∈ C.group i, H p) ≤
      B*C.partCost i + (μ : ℝ)^3*(C.group i).card*C.populationRadius (leader i) := by
    intro i hi
    have hh := mul_le_mul_of_nonneg_left (hn i hi) (show 0 ≤ 2+(μ : ℝ)^3 by positivity)
    have hsum := Finset.sum_le_sum (fun p (_ : p ∈ C.group i) => hleaf i hi p)
    have hsum' := Finset.sum_le_sum (fun p (_ : p ∈ C.group i) => show
        (I.metric.distance p i : ℝ) + (I.metric.distance (leader i) i : ℝ) + radius i ≤
          (I.metric.distance p i : ℝ) + ((2+(μ : ℝ)^3)*((3/2 : ℝ)*C.mean i) +
          (μ : ℝ)^3*C.populationRadius (leader i)) by linarith [hr i hi])
    apply (hsum.trans hsum').trans_eq
    rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
    change C.partCost i + _ = _
    rw [← C.mean_mul_card i]
    dsimp [B]
    ring
  have huc := Finset.sum_le_sum (fun i (_ : i ∈ C.bad \ A) => C.uncovered_weight H hH hroute hμ i)
  have hrad : (∑ i ∈ A, (C.group i).card*C.populationRadius (leader i)) ≤ (11/2 : ℝ)*C.price := by
    apply Analysis.radius_sum I.metric.clients C.clients_nonempty A C.group id leader C.mean
      C.price C.bad.card C.positive_cost hm (Finset.card_le_card hA)
      (fun i hi => ⟨leader i, hw i hi⟩) (fun _ _ => I.cluster_subset _ _)
      (fun i _ => (C.mean_mul_card i).symm)
    · simpa only [C.mean_mul_card] using C.partCost_subsum A (hA.trans Finset.sdiff_subset)
    · exact hn
  have hpart : ∀ f : I.Point → ℝ, (∑ i ∈ C.centers, f i) =
      (∑ i ∈ C.good, f i) + (∑ i ∈ A, f i) + ∑ i ∈ C.bad \ A, f i := by
    intro f
    have h₀ : (∑ i ∈ C.bad, f i) + (∑ i ∈ C.good, f i) = ∑ i ∈ C.centers, f i :=
      Finset.sum_sdiff C.good_subset
    have h₁ := Finset.sum_sdiff (f := f) hA
    linarith
  have hP := hpart C.partCost
  rw [C.partCost_sum] at hP
  have hW : (∑ p ∈ I.metric.clients, H p) = (∑ i ∈ C.good, ∑ p ∈ C.group i, H p) +
      (∑ i ∈ A, ∑ p ∈ C.group i, H p) + ∑ i ∈ C.bad \ A, ∑ p ∈ C.group i, H p := by
    rw [← I.cluster_partition C.centers C.centers_nonempty H]
    exact hpart _
  have hc := Finset.sum_le_sum hcovered
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_div, mul_assoc] at huc hc
  have hB1 : 1 ≤ B := by dsimp [B]; linarith
  have hB2 : 2+(μ : ℝ) ≤ B := by dsimp [B]; linarith
  have hPg : 0 ≤ ∑ i ∈ C.good, C.partCost i := Finset.sum_nonneg (fun i _ => C.partCost_nonneg i)
  have hPb : 0 ≤ ∑ i ∈ C.bad \ A, C.partCost i := Finset.sum_nonneg (fun i _ => C.partCost_nonneg i)
  have hgB := mul_le_mul_of_nonneg_right hB1 hPg
  have huB := mul_le_mul_of_nonneg_right hB2 hPb
  have hcoef : (B+(μ : ℝ)+(11/2 : ℝ)*(μ : ℝ)^3)*C.price ≤ 6*C.price :=
    mul_le_mul_of_nonneg_right (Analysis.weight_coefficient_lt hμ.le hμ1).le C.positive_cost.le
  have hrB := mul_le_mul_of_nonneg_left hrad hκ
  have hPB := congrArg (fun x : ℝ => B*x) hP
  have htotal : (∑ p ∈ I.metric.clients, H p) ≤
      (B+(μ : ℝ)+(11/2 : ℝ)*(μ : ℝ)^3)*C.price +
      (∑ i ∈ C.bad \ A, ∑ p ∈ C.near (1+(μ : ℝ)) i, H p)/Analysis.q μ := by
    rw [hW]
    nlinarith only [hg, hc, huc, hrB, hgB, huB, hPB]
  exact htotal.trans (add_le_add hcoef le_rfl)

lemma near_mass_le (C : Certificate I μ L₀) (A : Finset I.Point)
    (hA : A ⊆ C.centers) (a : ℝ) (H : I.Point → ℝ)
    (hH : ∀ p ∈ I.metric.clients, 0 ≤ H p) :
    (∑ i ∈ A, ∑ p ∈ C.near a i, H p) ≤ ∑ p ∈ I.metric.clients, H p := by
  calc
    _ ≤ ∑ i ∈ A, ∑ p ∈ C.group i, H p := by
      apply Finset.sum_le_sum
      intro i _
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun p hp _ => hH p (I.cluster_subset _ _ hp))
    _ ≤ ∑ i ∈ C.centers, ∑ p ∈ C.group i, H p :=
      Finset.sum_le_sum_of_subset_of_nonneg hA (fun i _ _ =>
        Finset.sum_nonneg (fun p hp => hH p (I.cluster_subset _ _ hp)))
    _ = _ := I.cluster_partition C.centers C.centers_nonempty H

end Certificate

namespace EndpointData
variable {I : Input} {μ : ℚ} {L₀ : ℝ} {C : Certificate I μ L₀}
variable (E : EndpointData C)

lemma first_total_weight (h : EndpointConditions C E) (hμ : 0 < (μ : ℝ))
    (hμ1 : (μ : ℝ) ≤ 1/4) (hm : 0 < C.bad.card) :
    (∑ p ∈ I.metric.clients, E.firstReference p) ≤
      (6+(μ : ℝ)^3/Analysis.q μ)*C.price := by
  have hW := C.state_weight_bound E.first E.diameter E.firstCovered E.leader E.radius
    hμ hμ1 hm h.diameter_nonneg h.deleted_subset h.old_nonneg h.first_bad
    (fun i hi => h.leader_mem i (Finset.mem_union_left _ hi)) h.first_leaf
    (fun i hi => (h.first_near i hi).trans
      (mul_le_mul_of_nonneg_right (show 1+(μ : ℝ) ≤ (3/2 : ℝ) by linarith) (C.mean_nonneg i)))
    (fun i hi => h.radius_upper i (Finset.mem_union_left _ hi))
  change (∑ p ∈ I.metric.clients, E.firstReference p) ≤
    6*C.price+(∑ i ∈ E.firstRemaining, E.firstMass i)/Analysis.q μ at hW
  exact Analysis.stopped_weight (Analysis.q_pos hμ) h.first_mass_stop hW

lemma extended_total_weight (h : EndpointConditions C E) (hμ : 0 < (μ : ℝ))
    (hμ1 : (μ : ℝ) ≤ 1/4) (hm : 0 < C.bad.card) (leaves : List (I.Point × ℝ)) :
    letI := I.pointMetric
    (∑ p ∈ I.metric.clients, Sampling.reference I.anchor E.diameter (E.first.extend leaves) p) ≤
      (6+(μ : ℝ)^3/Analysis.q μ)*C.price := by
  let _ := I.pointMetric
  apply le_trans ?_ (E.first_total_weight h hμ hμ1 hm)
  exact Finset.sum_le_sum (fun p _ =>
    Sampling.reference_extend_le I.anchor E.diameter E.first leaves p)

end EndpointData
end MetricKMedianRecovery.RefinedRecovery

end OAI
