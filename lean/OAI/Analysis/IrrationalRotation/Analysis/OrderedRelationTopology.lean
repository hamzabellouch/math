import OAI.Analysis.IrrationalRotation.Analysis.OrderedHaarRigidity

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped Topology

namespace Invariant233.ProductModel.OrderedRigidity

theorem orderedRelation_measurable :
    MeasurableSet {xy : Base × Base | Ordered xy.1 xy.2} := by
  unfold Ordered
  simp only [ofPred_forall]
  apply MeasurableSet.iInter
  intro i
  exact measurableSet_le
    (representative_measurable.comp ((measurable_pi_apply i).comp measurable_fst))
    (representative_measurable.comp ((measurable_pi_apply i).comp measurable_snd))

theorem representative_coe {t : ℝ} (ht : t ∈ Ico (0 : ℝ) 1) :
    circleRepresentative (t : Circle) = t := by
  exact AddCircle.equivIco_coe_of_mem (by simpa using ht)

def orderedApproximant (n : ℕ) : Base × Base :=
  ((fun _ => ((1 / 2 : ℝ) : Circle)),
    fun _ => ((1 - 1 / ((n : ℝ) + 2) : ℝ) : Circle))

def unorderedLimit : Base × Base :=
  ((fun _ => ((1 / 2 : ℝ) : Circle)), fun _ => 0)

theorem orderedApproximant_ordered (n : ℕ) :
    Ordered (orderedApproximant n).1 (orderedApproximant n).2 := by
  have hd : 0 < (n : ℝ) + 2 := by positivity
  have hsmall : 1 / ((n : ℝ) + 2) ≤ 1 / 2 := by
    apply (div_le_iff₀ hd).2
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have hpos : 0 < 1 / ((n : ℝ) + 2) := one_div_pos.mpr hd
  intro i
  change circleRepresentative ((1 / 2 : ℝ) : Circle) ≤
    circleRepresentative ((1 - 1 / ((n : ℝ) + 2) : ℝ) : Circle)
  rw [representative_coe (by norm_num), representative_coe (by
    constructor <;> linarith)]
  linarith

theorem unorderedLimit_not_ordered :
    ¬ Ordered unorderedLimit.1 unorderedLimit.2 := by
  intro h
  have h0 := h 0
  change circleRepresentative ((1 / 2 : ℝ) : Circle) ≤
    circleRepresentative ((0 : ℝ) : Circle) at h0
  rw [representative_coe (by norm_num), representative_coe (by norm_num)] at h0
  norm_num at h0

theorem orderedApproximant_tendsto :
    Tendsto orderedApproximant atTop (𝓝 unorderedLimit) := by
  have hfrac : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 2)) atTop (𝓝 0) := by
    have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp
      (tendsto_add_atTop_nat 1)
    simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one, add_assoc,
      one_add_one_eq_two] using h
  have hreal : Tendsto (fun n : ℕ => 1 - 1 / ((n : ℝ) + 2)) atTop (𝓝 (1 : ℝ)) := by
    simpa using tendsto_const_nhds.sub hfrac
  have hcircle : Tendsto
      (fun n : ℕ => ((1 - 1 / ((n : ℝ) + 2) : ℝ) : Circle)) atTop (𝓝 0) := by
    have h := (AddCircle.continuous_mk' (1 : ℝ)).continuousAt.tendsto.comp hreal
    change Tendsto (fun n : ℕ => ((1 - 1 / ((n : ℝ) + 2) : ℝ) : Circle))
      atTop (𝓝 ((1 : ℝ) : Circle)) at h
    simpa only [AddCircle.coe_period] using h
  apply Tendsto.prodMk_nhds
  · exact tendsto_const_nhds
  · exact tendsto_pi_nhds.2 (fun _ => hcircle)

theorem orderedRelation_not_isClosed :
    ¬ IsClosed {xy : Base × Base | Ordered xy.1 xy.2} := by
  intro hclosed
  exact unorderedLimit_not_ordered
    (hclosed.mem_of_tendsto orderedApproximant_tendsto
      (Filter.Eventually.of_forall orderedApproximant_ordered))

end Invariant233.ProductModel.OrderedRigidity

end

end OAI
