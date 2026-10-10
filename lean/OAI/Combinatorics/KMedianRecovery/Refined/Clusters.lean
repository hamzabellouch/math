import OAI.Combinatorics.KMedianRecovery.Refined.Model

namespace OAI

/-! Nearest-center clusters, integral metric costs, certificate cardinalities, and precision estimates. -/

namespace MetricKMedianRecovery.RefinedRecovery

namespace Input

@[instance_reducible]
noncomputable def pointMetric (I : Input) : MetricSpace I.Point where
  dist x y := (I.metric.distance x y : ℝ)
  dist_self x := by exact_mod_cast I.metric.distance_self x
  dist_comm x y := by exact_mod_cast I.metric.distance_symm x y
  dist_triangle x y z := by exact_mod_cast I.metric.distance_triangle x y z
  eq_of_dist_eq_zero := by
    intro x y he
    by_contra hn
    have hp : (0 : ℝ) < (I.metric.distance x y : ℝ) := by exact_mod_cast I.positive x y hn
    exact ne_of_gt hp he

lemma pointMetric_dist (I : Input) (p i : I.Point) :
    letI := I.pointMetric
    dist p i = (I.metric.distance p i : ℝ) := rfl

lemma pointMetric_clusterCost (I : Input) (O : Finset I.Point) (i : I.Point) :
    letI := I.pointMetric
    I.clusterCost O i = ∑ p ∈ I.cluster O i, dist p i := rfl

lemma size_eq_pointCount (I : Input) : I.size = I.metric.pointCount := by
  rw [size, RationalMetricInput.size, ← Finset.card_union_of_disjoint I.disjoint,
    I.metric.covered, Finset.card_univ, Fintype.card_fin]

lemma assign_mem (I : Input) (O : Finset I.Point) (hO : O.Nonempty) (p : I.Point) :
    I.assign O p ∈ O := by
  rw [assign, dite_eq_left hO]
  exact (Classical.choose_spec (Finset.exists_min_image O
    (fun i => toLex (I.metric.distance p i, i)) hO)).1

lemma assign_key_le (I : Input) (O : Finset I.Point) (hO : O.Nonempty) (p i : I.Point)
    (hi : i ∈ O) :
    toLex (I.metric.distance p (I.assign O p), I.assign O p) ≤
      toLex (I.metric.distance p i, i) := by
  rw [assign, dite_eq_left hO]
  exact (Classical.choose_spec (Finset.exists_min_image O
    (fun i => toLex (I.metric.distance p i, i)) hO)).2 i hi

lemma assign_nearest (I : Input) (O : Finset I.Point) (hO : O.Nonempty) (p i : I.Point)
    (hi : i ∈ O) : I.metric.distance p (I.assign O p) ≤ I.metric.distance p i :=
  Prod.Lex.monotone_fst _ _ (I.assign_key_le O hO p i hi)

lemma cost_eq_assigned (I : Input) (O : Finset I.Point) (hO : O.Nonempty) :
    I.metric.cost O = ∑ p ∈ I.metric.clients, I.metric.distance p (I.assign O p) := by
  rw [RationalMetricInput.cost, dite_eq_left hO]
  apply Finset.sum_congr rfl
  intro p _
  apply le_antisymm
  · exact Finset.inf'_le _ (I.assign_mem O hO p)
  · exact Finset.le_inf' hO _ (fun i hi => I.assign_nearest O hO p i hi)

lemma cluster_mem (I : Input) (O : Finset I.Point) (p i : I.Point) :
    p ∈ I.cluster O i ↔ p ∈ I.metric.clients ∧ I.assign O p = i := Finset.mem_filter

lemma cluster_subset (I : Input) (O : Finset I.Point) (i : I.Point) :
    I.cluster O i ⊆ I.metric.clients := Finset.filter_subset _ _

lemma cluster_partition (I : Input) (O : Finset I.Point) (hO : O.Nonempty) (f : I.Point → ℝ) :
    (∑ i ∈ O, ∑ p ∈ I.cluster O i, f p) = ∑ p ∈ I.metric.clients, f p := by
  classical
  simp only [cluster, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  simp [I.assign_mem O hO p]

lemma sum_clusterCost (I : Input) (O : Finset I.Point) (hO : O.Nonempty) :
    (∑ i ∈ O, I.clusterCost O i) = (I.metric.cost O : ℝ) := by
  rw [I.cost_eq_assigned O hO, Rat.cast_sum]
  calc
    _ = ∑ i ∈ O, ∑ p ∈ I.cluster O i, (I.metric.distance p (I.assign O p) : ℝ) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro p hp
      rw [(I.cluster_mem O p i).mp hp |>.2]
    _ = _ := I.cluster_partition O hO _

lemma cost_nonneg (I : Input) (S : Finset I.Point) : 0 ≤ (I.metric.cost S : ℝ) := by
  by_cases hS : S.Nonempty
  · rw [I.cost_eq_assigned S hS, Rat.cast_sum]
    exact Finset.sum_nonneg (fun p _ => Rat.cast_nonneg.mpr (I.metric.distance_nonneg _ _))
  · simp [RationalMetricInput.cost, hS]

lemma separated (I : Input) (p i : I.Point) (hp : p ∈ I.metric.clients)
    (hi : i ∈ I.metric.facilities) : (1 : ℚ) ≤ I.metric.distance p i := by
  have hpi : p ≠ i := by
    intro h
    exact (Finset.disjoint_left.mp I.disjoint hp) (h ▸ hi)
  obtain ⟨z, hz⟩ := I.integral p i
  have hz0 : 0 < z := by exact_mod_cast (hz ▸ I.positive p i hpi)
  rw [hz]
  exact_mod_cast hz0

lemma integer_cost (I : Input) (O : Finset I.Point) (hO : O.Nonempty)
    (bound : Polynomial ℕ) (hb : I.Bounded bound)
    (hP : 0 < (I.metric.cost O : ℝ)) :
    ∃ p : ℕ, I.metric.cost O = (p : ℚ) ∧ 1 ≤ p ∧ p ≤ I.metric.clients.card * bound.eval I.size := by
  classical
  let f : I.Point → ℕ := fun p => (I.integral p (I.assign O p)).choose
  have hf : ∀ p, I.metric.distance p (I.assign O p) = (f p : ℚ) :=
    fun p => (I.integral p (I.assign O p)).choose_spec
  let p : ℕ := ∑ x ∈ I.metric.clients, f x
  have he : I.metric.cost O = (p : ℚ) := by
    rw [I.cost_eq_assigned O hO]
    simp only [hf, p, Nat.cast_sum]
  refine ⟨p, he, ?_, ?_⟩
  · have hpR : (0 : ℝ) < p := by simpa only [he, Rat.cast_natCast] using hP
    exact_mod_cast hpR
  · have hf' : ∀ x ∈ I.metric.clients, f x ≤ bound.eval I.size := by
      intro x _
      have h := hb x (I.assign O x)
      rw [hf] at h
      exact_mod_cast h
    calc
      p ≤ ∑ x ∈ I.metric.clients, bound.eval I.size := Finset.sum_le_sum hf'
      _ = _ := by simp
end Input

namespace Certificate
variable {I : Input} {μ : ℚ} {L₀ : ℝ}
lemma centers_nonempty (C : Certificate I μ L₀) : C.centers.Nonempty := by
  apply Finset.card_pos.mp
  rw [C.same_card]
  exact I.anchor_nonempty.card_pos

lemma clients_nonempty (C : Certificate I μ L₀) : I.metric.clients.Nonempty := by
  by_contra hh
  have hempty := Finset.not_nonempty_iff_eq_empty.mp hh
  have hp := C.positive_cost
  rw [I.cost_eq_assigned C.centers C.centers_nonempty, hempty, Finset.sum_empty,
    Rat.cast_zero] at hp
  exact lt_irrefl _ hp

lemma size_ge_two (C : Certificate I μ L₀) : 2 ≤ I.size := by
  have hd := C.clients_nonempty.card_pos
  have hf := I.metric.facilities_nonempty.card_pos
  change 2 ≤ I.metric.clients.card + I.metric.facilities.card
  omega

lemma nonproxy_card (C : Certificate I μ L₀) : C.nonproxy.card = C.bad.card := by
  have hsub : C.good.image C.proxy ⊆ I.anchor := Finset.image_subset_iff.mpr C.proxy_mem
  rw [nonproxy, Finset.card_sdiff_of_subset hsub, bad,
    Finset.card_sdiff_of_subset C.good_subset, C.same_card,
    Finset.card_image_of_injOn C.proxy_inj]

lemma bad_card_le (C : Certificate I μ L₀) : C.bad.card ≤ I.metric.budget := by
  rw [← I.anchor_card, ← C.same_card]
  exact Finset.card_le_card Finset.sdiff_subset

theorem zero_bad_anchor (C : Certificate I μ L₀) (hm : C.bad.card = 0) :
    (I.metric.cost I.anchor : ℝ) ≤ (1 + (μ : ℝ)) * (I.metric.cost C.centers : ℝ) := by
  have hempty : C.centers \ C.good = ∅ := Finset.card_eq_zero.mp hm
  have hgood : C.good = C.centers :=
    Finset.Subset.antisymm C.good_subset (Finset.sdiff_eq_empty_iff_subset.mp hempty)
  have hsum : (I.metric.cost I.anchor : ℝ) =
      ∑ i ∈ C.good, ∑ p ∈ I.cluster C.centers i,
        (I.metric.distance p (I.assign I.anchor p) : ℝ) := by
    rw [hgood, I.cluster_partition _ C.centers_nonempty,
      I.cost_eq_assigned I.anchor I.anchor_nonempty, Rat.cast_sum]
  have hpoint : (I.metric.cost I.anchor : ℝ) ≤
      ∑ i ∈ C.good, ∑ p ∈ I.cluster C.centers i,
        (I.metric.distance p (C.proxy i) : ℝ) := by
    rw [hsum]
    apply Finset.sum_le_sum
    intro i hi
    apply Finset.sum_le_sum
    intro p _
    exact_mod_cast I.assign_nearest I.anchor I.anchor_nonempty p (C.proxy i) (C.proxy_mem i hi)
  have hh := C.proxy_cost
  rw [hgood, I.sum_clusterCost _ C.centers_nonempty] at hh
  rw [hgood] at hpoint
  nlinarith

lemma zero_bad_target (C : Certificate I μ L₀) (hm : C.bad.card = 0)
    {ε : ℝ} (hε : 0 < ε) (hμ : (μ : ℝ) ≤ ε/12) :
    (I.metric.cost I.anchor : ℝ) ≤
      (1 + 2 / Real.exp 1 + ε) * (I.metric.cost C.centers : ℝ) := by
  have hf := C.zero_bad_anchor hm
  have hc : 1 + (μ : ℝ) ≤ 1 + 2 / Real.exp 1 + ε := by
    have he : 0 < 2 / Real.exp 1 := div_pos (by norm_num) (Real.exp_pos _)
    linarith
  exact hf.trans (mul_le_mul_of_nonneg_right hc C.positive_cost.le)
end Certificate

lemma precision_lt {ζ : ℝ} (hζ : 0 < ζ) (hζ1 : ζ < 1) :
    (precision ζ : ℝ) < Real.log (1/ζ) / Real.log 2 + 1 := by
  apply Nat.ceil_lt_add_one
  apply div_nonneg
  · exact Real.log_nonneg ((le_div_iff₀ hζ).mpr (by linarith))
  · exact (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le

lemma precision_error_le {ζ : ℝ} (hζ : 0 < ζ) :
    1 / (2 : ℝ) ^ precision ζ ≤ ζ := by
  have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hceil := (Nat.le_ceil (Real.log (1/ζ) / Real.log 2))
  have hmul : Real.log (1/ζ) ≤ (precision ζ : ℝ) * Real.log 2 :=
    (div_le_iff₀ hlog).mp hceil
  have he : Real.exp (-(precision ζ : ℝ) * Real.log 2) = 1 / (2 : ℝ) ^ precision ζ := by
    rw [neg_mul, Real.exp_neg, Real.exp_nat_mul,
      Real.exp_log (by norm_num : (0 : ℝ) < 2), one_div]
  rw [← he]
  calc
    Real.exp (-(precision ζ : ℝ) * Real.log 2) ≤ Real.exp (Real.log ζ) := by
      apply Real.exp_le_exp.mpr
      simpa only [one_div, Real.log_inv, neg_neg, neg_mul] using neg_le_neg hmul
    _ = ζ := Real.exp_log hζ

end MetricKMedianRecovery.RefinedRecovery

end OAI
