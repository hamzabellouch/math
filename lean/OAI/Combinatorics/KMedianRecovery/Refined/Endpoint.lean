import OAI.Combinatorics.KMedianRecovery.Refined.Clusters
import OAI.Combinatorics.KMedianRecovery.Refined.State
import OAI.Combinatorics.KMedianRecovery.Refined.Progress

namespace OAI

/-! Comparison-cluster prices and the geometric data and stopping conditions of two-stage endpoints. -/

namespace MetricKMedianRecovery.RefinedRecovery

namespace Certificate
variable {I : Input} {μ : ℚ} {L₀ : ℝ}

noncomputable def price (C : Certificate I μ L₀) : ℝ := (I.metric.cost C.centers : ℝ)
noncomputable def group (C : Certificate I μ L₀) (i : I.Point) : Finset I.Point :=
  I.cluster C.centers i
noncomputable def partCost (C : Certificate I μ L₀) (i : I.Point) : ℝ :=
  I.clusterCost C.centers i
noncomputable def mean (C : Certificate I μ L₀) (i : I.Point) : ℝ :=
  C.partCost i / (C.group i).card
noncomputable def near (C : Certificate I μ L₀) (a : ℝ) (i : I.Point) : Finset I.Point :=
  (C.group i).filter (fun p => (I.metric.distance p i : ℝ) ≤ a*C.mean i)
noncomputable def populationRadius (C : Certificate I μ L₀) (w : I.Point) : ℝ :=
  letI := I.pointMetric
  Population.radius I.metric.clients C.clients_nonempty C.price C.bad.card w

lemma partCost_nonneg (C : Certificate I μ L₀) (i : I.Point) : 0 ≤ C.partCost i :=
  Finset.sum_nonneg (fun _ _ => Rat.cast_nonneg.mpr (I.metric.distance_nonneg _ _))

lemma partCost_sum (C : Certificate I μ L₀) :
    (∑ i ∈ C.centers, C.partCost i) = C.price := I.sum_clusterCost _ C.centers_nonempty

lemma mean_mul_card (C : Certificate I μ L₀) (i : I.Point) :
    C.mean i * (C.group i).card = C.partCost i := by
  by_cases hc : (C.group i).Nonempty
  · exact div_mul_cancel₀ _ (ne_of_gt (Nat.cast_pos.mpr hc.card_pos : (0 : ℝ) < (C.group i).card))
  · have he := Finset.not_nonempty_iff_eq_empty.mp hc
    have hz : C.partCost i = 0 := by change (∑ p ∈ C.group i, _) = 0; rw [he]; simp
    simp [he, hz]

lemma mean_nonneg (C : Certificate I μ L₀) (i : I.Point) : 0 ≤ C.mean i :=
  div_nonneg (C.partCost_nonneg i) (Nat.cast_nonneg _)

lemma partCost_subsum (C : Certificate I μ L₀) (A : Finset I.Point) (hA : A ⊆ C.centers) :
    (∑ i ∈ A, C.partCost i) ≤ C.price := by
  rw [← C.partCost_sum]
  exact Finset.sum_le_sum_of_subset_of_nonneg hA (fun i _ _ => C.partCost_nonneg i)

lemma cluster_subsum (C : Certificate I μ L₀) (A : Finset I.Point) (hA : A ⊆ C.centers)
    (K : Finset I.Point) (f : I.Point → ℝ) (hf : ∀ p ∈ I.metric.clients, 0 ≤ f p) :
    (∑ i ∈ A, ∑ p ∈ C.group i ∩ K, f p) ≤ ∑ p ∈ K ∩ I.metric.clients, f p := by
  classical
  have hp : (∑ i ∈ C.centers, ∑ p ∈ C.group i ∩ K, f p) =
      ∑ p ∈ I.metric.clients ∩ K, f p := by
    have hh := I.cluster_partition C.centers C.centers_nonempty (fun p => if p ∈ K then f p else 0)
    simpa only [group, Finset.sum_ite, Finset.filter_mem_eq_inter, Finset.sum_const_zero, add_zero] using hh
  rw [Finset.inter_comm K, ← hp]
  exact Finset.sum_le_sum_of_subset_of_nonneg hA
    (fun i _ _ => Finset.sum_nonneg (fun p hp => hf p
      (I.cluster_subset _ _ (Finset.mem_inter.mp hp).1)))

lemma partCost_empty (C : Certificate I μ L₀) (i : I.Point) (he : C.group i = ∅) :
    C.partCost i = 0 := by
  change (∑ p ∈ C.group i, _) = 0
  rw [he]
  simp

lemma populationRadius_nonneg (C : Certificate I μ L₀) (hm : 0 < C.bad.card) (w : I.Point) :
    0 ≤ C.populationRadius w := by
  let _ := I.pointMetric
  exact (Population.radius_pos _ C.clients_nonempty _ _ _ C.positive_cost hm).le

end Certificate

structure EndpointData {I : Input} {μ : ℚ} {L₀ : ℝ} (C : Certificate I μ L₀) where
  diameter : ℝ
  first : Sampling.State I.Point
  appended : List (I.Point × ℝ)
  firstCovered : Finset I.Point
  secondCovered : Finset I.Point
  leader : I.Point → I.Point
  radius : I.Point → ℝ

namespace EndpointData
variable {I : Input} {μ : ℚ} {L₀ : ℝ} {C : Certificate I μ L₀}

def final (E : EndpointData C) : Sampling.State I.Point := E.first.extend E.appended
noncomputable def covered (E : EndpointData C) : Finset I.Point := E.firstCovered ∪ E.secondCovered
noncomputable def firstRemaining (E : EndpointData C) : Finset I.Point := C.bad \ E.firstCovered
noncomputable def remaining (E : EndpointData C) : Finset I.Point := E.firstRemaining \ E.secondCovered
noncomputable def firstReference (E : EndpointData C) : I.Point → ℝ :=
  letI := I.pointMetric
  Sampling.reference I.anchor E.diameter E.first
noncomputable def finalReference (E : EndpointData C) : I.Point → ℝ :=
  letI := I.pointMetric
  Sampling.reference I.anchor E.diameter E.final
noncomputable def firstInternal (E : EndpointData C) : Finset I.Point :=
  letI := I.pointMetric
  Sampling.assignedOriginals I.metric.clients I.anchor (C.nonproxy \ E.first.deleted) E.diameter E.first
noncomputable def finalInternal (E : EndpointData C) : Finset I.Point :=
  letI := I.pointMetric
  Sampling.assignedOriginals I.metric.clients I.anchor (C.nonproxy \ E.first.deleted) E.diameter E.final
noncomputable def large (E : EndpointData C) : Finset I.Point :=
  E.remaining.filter (fun i => ((C.group i).card : ℝ)/3 ≤ (C.group i ∩ E.firstInternal).card)
noncomputable def small (E : EndpointData C) : Finset I.Point := E.remaining \ E.large
noncomputable def firstMass (E : EndpointData C) (i : I.Point) : ℝ :=
  ∑ p ∈ C.near (1+(μ : ℝ)) i, E.firstReference p
noncomputable def secondMass (E : EndpointData C) (i : I.Point) : ℝ :=
  ∑ p ∈ C.near (3/2) i, E.finalReference p
noncomputable def fraction (E : EndpointData C) (i : I.Point) : ℝ :=
  ((C.group i ∩ E.finalInternal).card : ℝ) / (C.group i).card

noncomputable def baseCharge (E : EndpointData C) (θ : ℝ) (p : I.Point) : ℝ :=
  Analysis.baseCharge θ (E.finalReference p) (fun i => (I.metric.distance p i : ℝ)) E.covered

noncomputable def internalCharge (E : EndpointData C) (θ : ℝ) (i p : I.Point) : ℝ :=
  if i ∈ C.good then (I.metric.distance p (C.proxy i) : ℝ)
  else if i ∈ E.covered then (I.metric.distance p i : ℝ) +
    θ*((I.metric.distance (E.leader i) i : ℝ) + E.radius i)
  else (I.metric.distance p i : ℝ)

noncomputable def clusterCharge (E : EndpointData C) (θ : ℝ) (i : I.Point) : ℝ :=
  Analysis.clusterCharge (C.group i) E.finalInternal (E.internalCharge θ i) (E.baseCharge θ)

noncomputable def totalCharge (E : EndpointData C) (θ : ℝ) : ℝ :=
  2*(∑ p ∈ E.finalInternal, E.finalReference p) + ∑ i ∈ C.centers, E.clusterCharge θ i

end EndpointData

structure EndpointConditions {I : Input} {μ : ℚ} {L₀ : ℝ}
    (C : Certificate I μ L₀) (E : EndpointData C) : Prop where
  diameter_nonneg : 0 ≤ E.diameter
  deleted_subset : E.first.deleted ⊆ C.nonproxy
  old_nonneg : ∀ z ∈ E.first.leaves, 0 ≤ z.2
  new_nonneg : ∀ z ∈ E.appended, 0 ≤ z.2
  first_bad : E.firstCovered ⊆ C.bad
  second_bad : E.secondCovered ⊆ E.firstRemaining
  leader_mem : ∀ i ∈ E.covered, E.leader i ∈ C.group i
  first_leaf : ∀ i ∈ E.firstCovered, (E.leader i, E.radius i) ∈ E.first.leaves
  second_leaf : ∀ i ∈ E.secondCovered, (E.leader i, E.radius i) ∈ E.appended
  first_near : ∀ i ∈ E.firstCovered,
    (I.metric.distance (E.leader i) i : ℝ) ≤ (1+(μ : ℝ))*C.mean i
  second_near : ∀ i ∈ E.secondCovered,
    (I.metric.distance (E.leader i) i : ℝ) ≤ (3/2 : ℝ)*C.mean i
  radius_lower : ∀ i ∈ E.covered, (I.metric.distance (E.leader i) i : ℝ) ≤ E.radius i
  radius_upper : ∀ i ∈ E.covered, E.radius i ≤
    (1+(μ : ℝ)^3)*(I.metric.distance (E.leader i) i : ℝ) + (μ : ℝ)^3*C.populationRadius (E.leader i)
  eligible : ∀ i ∈ E.secondCovered,
    ((C.group i ∩ E.firstInternal).card : ℝ) < ((C.group i).card : ℝ)/3
  first_mass_stop : (∑ i ∈ E.firstRemaining, E.firstMass i) ≤ (μ : ℝ)^3*C.price
  internal_stop : (∑ p ∈ E.firstInternal, E.firstReference p) ≤ (μ : ℝ)^3*C.price
  second_mass_stop : (∑ i ∈ E.small, E.secondMass i) ≤ (μ : ℝ)^3*C.price

end MetricKMedianRecovery.RefinedRecovery

end OAI
