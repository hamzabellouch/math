import OAI.Analysis.CircleDomains.Selection.SparseTags
import OAI.Analysis.CircleDomains.Probability.DelayedTupleMeasure
import Mathlib.Data.Nat.Pairing

namespace OAI

/-! Finite individual tuple costs suffice for arbitrarily small total cost
after an injective reassignment of slots. No summability of the original
weighted tuple costs is required. -/

open Set Function Filter MeasureTheory
open scoped Topology ENNReal Classical

noncomputable section

namespace CircleDomainRigidity

theorem lintegral_weightedTupleMeasure (θ : ℕ → TagSlot) (f : LevelTuple → ℝ≥0∞) :
    ∫⁻ t, f t ∂weightedTupleMeasure θ =
      ∑' k, slotWeight k * ∫⁻ t, f t ∂slotTupleMeasure (θ k) := by
  rw [weightedTupleMeasure, lintegral_sum_measure]
  simp only [lintegral_smul_measure, smul_eq_mul]

theorem lintegral_weightedTupleMeasure_sparse (e : ℕ ↪ ℕ)
    (θ : ℕ → TagSlot) (f : LevelTuple → ℝ≥0∞) :
    ∫⁻ t, f t ∂weightedTupleMeasure (sparseTags e θ) =
      ∑' i, slotWeight (e i) * ∫⁻ t, f t ∂slotTupleMeasure (θ i) := by
  rw [lintegral_weightedTupleMeasure]
  let F := fun k => slotWeight k * ∫⁻ t, f t ∂slotTupleMeasure (sparseTags e θ k)
  have hs : Function.support F ⊆ Set.range e := by
    intro k hk
    by_contra hnot
    apply hk
    simp only [F, sparseTags_outside e θ hnot, inactiveTag, slotTupleMeasure,
      Sum.elim_inl, lintegral_zero_measure, mul_zero]
  calc
    ∑' k, F k = ∑' i, F (e i) := (e.injective.tsum_eq hs).symm
    _ = _ := by simp only [F, sparseTags_at]

theorem slotWeight_antitone : Antitone slotWeight := by
  intro n m hnm
  exact pow_le_pow_right_of_le_one' (by norm_num) hnm

theorem exists_sparse_weighted_sum_le (a : ℕ → ℝ≥0∞) (ha : ∀ k, a k < ∞)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ e : ℕ ↪ ℕ, (∑' k, slotWeight (e k) * a k) ≤ ε := by
  have hex : ∀ k, ∃ n, slotWeight n * a k < (ε / 2) * slotWeight k := by
    intro k
    have ht : 0 < (ε / 2) * slotWeight k :=
      ENNReal.mul_pos (ENNReal.div_pos_iff.mpr ⟨hε.ne', by norm_num⟩).ne'
        (slotWeight_pos k).ne'
    have hw : Tendsto slotWeight atTop (𝓝 0) :=
      ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num)
    have hc : Tendsto (fun n => slotWeight n * a k) atTop (𝓝 0) := by
      simpa only [zero_mul] using ENNReal.Tendsto.mul_const hw (Or.inr (ne_of_lt (ha k)))
    exact ((tendsto_order.mp hc).2 _ ht).exists
  choose n hn using hex
  let e : ℕ ↪ ℕ := ⟨fun k => Nat.pair k (n k), fun i j hij => (Nat.pair_eq_pair.mp hij).1⟩
  refine ⟨e, ?_⟩
  calc
    ∑' k, slotWeight (e k) * a k ≤ ∑' k, (ε / 2) * slotWeight k := by
      apply ENNReal.tsum_le_tsum
      intro k
      exact le_trans (mul_le_mul' (slotWeight_antitone (Nat.right_le_pair k (n k))) le_rfl)
        (hn k).le
    _ = (ε / 2) * 2 := by rw [ENNReal.tsum_mul_left, tsum_slotWeight]
    _ = ε := ENNReal.div_mul_cancel (by norm_num) (by norm_num)

theorem exists_sparse_tuple_cost_le (θ : ℕ → TagSlot) (f : LevelTuple → ℝ≥0∞)
    (hf : ∀ k, (∫⁻ t, f t ∂slotTupleMeasure (θ k)) < ∞)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ e : ℕ ↪ ℕ, (∫⁻ t, f t ∂weightedTupleMeasure (sparseTags e θ)) ≤ ε := by
  obtain ⟨e, he⟩ := exists_sparse_weighted_sum_le _ hf hε
  exact ⟨e, by rwa [lintegral_weightedTupleMeasure_sparse]⟩

end CircleDomainRigidity

end

end OAI
