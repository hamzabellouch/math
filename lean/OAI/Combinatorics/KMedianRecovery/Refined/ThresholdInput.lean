import OAI.Combinatorics.KMedianRecovery.Refined.Model
import OAI.Combinatorics.KMedian.Geometry.RationalInstanceCost

namespace OAI

namespace MetricKMedianRecovery.RefinedRecovery

namespace Input

abbrev asInstance (I : Input) : MetricKMedian.Instance where
  n := I.metric.pointCount
  distance := I.metric.distance
  clients := I.metric.clients
  facilities := I.metric.facilities
  k := I.metric.budget
  distance_nonneg := I.metric.distance_nonneg
  distance_eq_zero i j := by
    constructor
    · intro h
      by_contra hn
      exact (ne_of_gt (I.positive i j hn)) h
    · rintro rfl
      exact I.metric.distance_self i
  distance_symm := I.metric.distance_symm
  distance_triangle := I.metric.distance_triangle
  k_pos := I.metric.budget_pos
  k_le := I.anchor_card.symm.trans_le (Finset.card_le_card I.anchor_subset)

lemma asInstance_bits (I : Input) :
    MetricKMedian.encodeInstance I.asInstance = I.metric.bits := by
  have hrat (q : ℚ) : MetricKMedian.encodeRat q = RationalMetricInput.rationalBits q := by
    simp only [MetricKMedian.encodeRat, RationalMetricInput.rationalBits,
      MetricKMedian.encodeNat, RationalMetricInput.natBits, Rat.num_neg]
  simp only [MetricKMedian.encodeInstance, RationalMetricInput.bits, asInstance,
    MetricKMedian.encodeNat, RationalMetricInput.natBits, hrat]

lemma asInstance_cost (I : Input) (S : Finset I.Point) :
    MetricKMedian.cost I.asInstance S = (I.metric.cost S : ℝ) := by
  rw [← MetricKMedian.Instance.cast_rationalCost]
  congr 1
  unfold MetricKMedian.rationalCost RationalMetricInput.cost
  by_cases hS : S.Nonempty
  · simp only [dite_eq_left hS]
    apply Finset.sum_congr rfl
    intro p _
    unfold MetricKMedian.rationalNearest
    rw [dite_eq_left hS]
    apply le_antisymm
    · apply Finset.le_inf'
      intro i hi
      exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨i, hi, rfl⟩)
    · apply Finset.le_min'
      intro q hq
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hq
      exact Finset.inf'_le _ hi
  · simp [MetricKMedian.rationalNearest, hS]

lemma optimum_le_comparison (I : Input) {μ : ℚ} {L₀ : ℝ}
    (C : Certificate I μ L₀) :
    MetricKMedian.optimum I.asInstance ≤ (I.metric.cost C.centers : ℝ) := by
  have hn : C.centers.Nonempty := Finset.card_pos.mp (by
    rw [C.same_card, I.anchor_card]
    exact I.metric.budget_pos)
  rw [← I.asInstance_cost]
  exact I.asInstance.optimum_le C.centers_subset hn (C.same_card.trans I.anchor_card).le

lemma decode_mask (I : Input) (S : Finset I.Point) (hS : S ⊆ I.metric.facilities) :
    I.metric.decodeOutput (List.ofFn (fun i : I.Point => decide (i ∈ S))) = S := by
  ext i
  simp only [RationalMetricInput.decodeOutput, Finset.mem_filter,
    List.getElem?_ofFn, dite_eq_left i.isLt, Option.getD_some, Fin.eta, decide_eq_true_eq]
  exact and_iff_right_of_imp (fun hi => hS hi)

end Input

end MetricKMedianRecovery.RefinedRecovery

end OAI
