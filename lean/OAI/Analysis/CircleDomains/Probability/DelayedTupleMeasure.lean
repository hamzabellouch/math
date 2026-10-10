import OAI.Analysis.CircleDomains.Selection.TagDelay

namespace OAI

/-! Delaying tags scales their weighted tuple measure, allowing every finite
tuple cost of a fixed allowed path to become arbitrarily small. -/

open Set Filter MeasureTheory
open scoped Topology ENNReal

noncomputable section

namespace CircleDomainRigidity

theorem slotWeight_add (N k : ℕ) : slotWeight (N + k) = slotWeight N * slotWeight k :=
  pow_add _ _ _

theorem weightedTupleMeasure_delay (N : ℕ) (θ : ℕ → TagSlot) :
    weightedTupleMeasure (delayTags N θ) = slotWeight N • weightedTupleMeasure θ := by
  ext A hA
  rw [weightedTupleMeasure_apply _ hA, Measure.smul_apply, smul_eq_mul,
    weightedTupleMeasure_apply _ hA]
  let F : ℕ → ℝ≥0∞ := fun k => slotWeight k * slotTupleMeasure (delayTags N θ k) A
  have hsum : (∑ k ∈ Finset.range N, F k) + ∑' k, F (k + N) = ∑' k, F k :=
    Summable.sum_add_tsum_nat_add' (k := N) ENNReal.summable
  change (∑' k, F k) = _
  rw [← hsum]
  have hzero : (∑ k ∈ Finset.range N, F k) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    have hk' := Finset.mem_range.mp hk
    simp only [F, delayTags_before N θ hk', inactiveTag, slotTupleMeasure, Sum.elim_inl]
    simp
  rw [hzero, zero_add]
  have heq : ∀ k, F (k + N) = slotWeight N * (slotWeight k * slotTupleMeasure (θ k) A) := by
    intro k
    dsimp only [F]
    rw [Nat.add_comm k N, delayTags_add, slotWeight_add, mul_assoc]
  simp_rw [heq]
  exact ENNReal.tsum_mul_left

theorem lintegral_weightedTupleMeasure_delay (N : ℕ) (θ : ℕ → TagSlot)
    (f : LevelTuple → ℝ≥0∞) :
    ∫⁻ t, f t ∂weightedTupleMeasure (delayTags N θ) =
      slotWeight N * ∫⁻ t, f t ∂weightedTupleMeasure θ := by
  rw [weightedTupleMeasure_delay, lintegral_smul_measure, smul_eq_mul]

theorem tendsto_delayedTupleCost (θ : ℕ → TagSlot) (f : LevelTuple → ℝ≥0∞)
    (hf : (∫⁻ t, f t ∂weightedTupleMeasure θ) < ∞) :
    Tendsto (fun N => ∫⁻ t, f t ∂weightedTupleMeasure (delayTags N θ)) atTop (𝓝 0) := by
  simp_rw [lintegral_weightedTupleMeasure_delay]
  have hw : Tendsto slotWeight atTop (𝓝 0) :=
    ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num)
  simpa only [zero_mul] using ENNReal.Tendsto.mul_const hw (Or.inr (ne_of_lt hf))

end CircleDomainRigidity

end

end OAI
