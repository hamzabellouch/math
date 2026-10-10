import OAI.NumberTheory.Ostmann.Arithmetic.FrequencyBulkNorm
import OAI.NumberTheory.Ostmann.Arithmetic.FrozenSupportedArithmetic

namespace OAI

/-! # The frequency norm with the original fixed nonbulk masks -/

namespace Ostmann
open scoped Classical BigOperators

section
variable {σ : Type*} (base : σ → ℕ) (tier : σ → ℕ) (S : Finset ℤ) (n m R : ℕ)
  [NeZero (R ^ (n - 1 + 2))] (t : FrequencyTree (S × S) n)
  (hS : ∀ s ∈ S, s ≠ 0) (hR : ∀ b (j : Fin (2 ^ n - 1)),
    (singleTreeNodeFrequencies S n (frequencyPairProjection S n b t) j.val).root.natAbs ∣ R)
  (slot : (TreeLeafIndex n × Fin m) ↪ σ)
  (small : Bool → TreeLeafTuple (List σ) n) (a : Bool → MovingSampleSlots σ n)
  (hslot : ∀ j, n ≤ tier (slot j))
  (hsmall : ∀ b i, i ∈ flattenMovingSlots n (small b) → i ∉ Set.range slot)
  (ha : ∀ b, (a b).Levels tier)
  (hbase : ∀ i ∉ Set.range slot, IsCoprime (base i : ℤ) (R : ℤ))
  (F : Bool → {k : ℕ} → MovingSlotData σ k → ℤ → ℂ)
  (E : Bool → {k : ℕ} → MovingSlotData σ k → ℤ → ℤ → ℤ → ℝ)
  (N : ℕ) (D : ℝ) (hD : 0 ≤ D) (hN : ∀ s ∈ S, s.natAbs ≤ N)
  (hdiv : ∀ q : ℕ, q ≠ 0 → q ≤ N ^ 2 → (q.divisors.card : ℝ) ≤ D)
  (hm : 0 < m)

include hslot hsmall ha hbase hS hR hD hN hdiv hm in
/-- The retained fixed support mask can only decrease the bulk norm. -/
theorem frozenBulkFrequencyFactor_mean_le
    (outside : List ℕ) (childBound : ℕ → ℕ) (input : PublishedProgressionInput)
    (Q : ℕ) (Y : ℝ) (hY : 0 ≤ Y) :
    let T := fun b => buildMovingSlotData n
      (frequencyTreeMap Subtype.val n (frequencyPairProjection S n b t))
      (small b) (bulkSlotLeaves n m slot) (a b)
    (Fintype.card (TreeLeafIndex n × Fin m → (ZMod (R ^ (n - 1 + 2)))ˣ) : ℝ)⁻¹ *
        (∑ z : TreeLeafIndex n × Fin m → (ZMod (R ^ (n - 1 + 2)))ˣ,
          ‖frozenBulkFrequencyFactor base slot outside F E T childBound R
            (R ^ (n - 1 + 2)) input Q Y z‖) ≤
      2 * ((‖movingDataWeight (F false) (E false) (T false)‖ *
        ‖movingDataWeight (F true) (E true) (T true)‖) *
      ((frequencySplitList S n t).map (pairFrequencySupportBound D)).prod) := by
  intro T
  apply le_trans _ (frequencyModelBulkPage_mean_le base tier S n m R t hS hR slot small a
    hslot hsmall ha hbase F E N D hD hN hdiv hm input Q Y hY)
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg _))
  apply Finset.sum_le_sum
  intro z _
  unfold frozenBulkFrequencyFactor
  split_ifs
  · rw [one_mul]
  · simpa only [zero_mul, norm_zero] using norm_nonneg
      (movingFrequencyCorePageAverage (Function.extend slot (fun j => (z j).val.val) base)
        F E T R (R ^ (n - 1 + 2)) input Q Y)

end
end Ostmann

end OAI
