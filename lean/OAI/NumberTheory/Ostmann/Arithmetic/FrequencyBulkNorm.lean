import OAI.NumberTheory.Ostmann.Arithmetic.FrequencyBulkSupport
import OAI.NumberTheory.Ostmann.Arithmetic.FrozenFrequencyAverage

namespace OAI

/-! # Sharp arithmetic probability retained in the bulk frequency norm -/

namespace Ostmann
open scoped Classical BigOperators

theorem arithmeticLeafSupport_mean_le {Q : ℕ} [NeZero Q]
    (S : Finset ℤ) (N n : ℕ) (D : ℝ) (hD : 0 ≤ D)
    (hS : ∀ s ∈ S, s ≠ 0 ∧ s.natAbs ≤ N)
    (hdiv : ∀ q : ℕ, q ≠ 0 → q ≤ N ^ 2 → (q.divisors.card : ℝ) ≤ D)
    (t : FrequencyTree (S × S) n)
    (data : (ZMod Q)ˣ → List (ZMod Q)ˣ → Option (ArithmeticSplitData Q × ArithmeticSplitData Q))
    (hmatch : ∀ P past d e, data P past = some (d, e) →
      d.hasFrequencies (treeNodeFrequencies S n t past.length).1 ∧
        e.hasFrequencies (treeNodeFrequencies S n t past.length).2) :
    (Fintype.card (TreeLeafTuple (ZMod Q)ˣ n) : ℝ)⁻¹ *
        (∑ z : TreeLeafTuple (ZMod Q)ˣ n, arithmeticLeafSupport n data z) ≤
      ((frequencySplitList S n t).map (pairFrequencySupportBound D)).prod := by
  have he : (∏ j ∈ Finset.range (2 ^ n - 1),
      pairFrequencySupportBound D (treeNodeFrequencies S n t j)) =
      ((frequencySplitList S n t).map (pairFrequencySupportBound D)).prod := by
    rw [← frequencySplitList_length S n t]
    exact prod_range_list_getD _ _ _
  unfold arithmeticLeafSupport
  apply treeLeaf_average_le (G := (ZMod Q)ˣ) n
    (fun P x => sequentialSupport (fun past y => arithmeticPairSplitTest (data P past) y)
      [] (2 ^ n - 1) (treeLeafSplitEquiv n P x)) _
  intro P
  exact (arithmetic_leaf_support_fixed_frequencies (data P) (treeNodeFrequencies S n t)
    D hD (hmatch P) (treeNodeFrequencies_divisor_bound S N D hD hS hdiv n t) n P).trans_eq he

theorem uniform_average_norm_average_mul_le {A B : Type*} [Fintype A] [Fintype B] [Nonempty B]
    (f : A → B → ℂ) (w : B → ℂ) (C K : ℝ) (hC : 0 ≤ C)
    (hw : ∀ b, ‖w b‖ ≤ C)
    (hf : ∀ b, (Fintype.card A : ℝ)⁻¹ * ∑ a, ‖f a b‖ ≤ K) :
    (Fintype.card A : ℝ)⁻¹ *
      (∑ a, ‖(Fintype.card B : ℂ)⁻¹ * ∑ b, f a b * w b‖) ≤ C * K := by
  have hpoint (a : A) : ‖(Fintype.card B : ℂ)⁻¹ * ∑ b, f a b * w b‖ ≤
      (Fintype.card B : ℝ)⁻¹ * ∑ b, C * ‖f a b‖ := by
    rw [norm_mul, norm_inv, Complex.norm_natCast]
    apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg _))
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro b _
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_left (hw b) (norm_nonneg _)).trans_eq (mul_comm _ _)
  calc
    _ ≤ (Fintype.card A : ℝ)⁻¹ *
        ∑ a, (Fintype.card B : ℝ)⁻¹ * ∑ b, C * ‖f a b‖ :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun a _ => hpoint a)
        (inv_nonneg.mpr (Nat.cast_nonneg _))
    _ = (Fintype.card B : ℝ)⁻¹ * ∑ b, C * ((Fintype.card A : ℝ)⁻¹ * ∑ a, ‖f a b‖) := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro b _
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ ≤ (Fintype.card B : ℝ)⁻¹ * ∑ _b : B, C * K := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg _))
      exact Finset.sum_le_sum fun b _ => mul_le_mul_of_nonneg_left (hf b) hC
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast Fintype.card_ne_zero), one_mul]

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
/-- The original bulk unit law gives the product of the simultaneous
quadratic-root bounds. The coefficient contains the literal data weights. -/
theorem frequencyModelBulkCore_mean_le (x y : ℤ) :
    let T := fun b => buildMovingSlotData n
      (frequencyTreeMap Subtype.val n (frequencyPairProjection S n b t))
      (small b) (bulkSlotLeaves n m slot) (a b)
    (Fintype.card (TreeLeafIndex n × Fin m → (ZMod (R ^ (n - 1 + 2)))ˣ) : ℝ)⁻¹ *
        (∑ z : TreeLeafIndex n × Fin m → (ZMod (R ^ (n - 1 + 2)))ˣ,
          ‖movingFrequencyCore (Function.extend slot (fun j => (z j).val.val) base) F E T R x y‖) ≤
      (‖movingDataWeight (F false) (E false) (T false)‖ *
        ‖movingDataWeight (F true) (E true) (T true)‖) *
      ((frequencySplitList S n t).map (pairFrequencySupportBound D)).prod := by
  intro T
  let data := frequencyModelPairData base S n R t hS hR small a x y
  let amp := ‖movingDataWeight (F false) (E false) (T false)‖ *
    ‖movingDataWeight (F true) (E true) (T true)‖
  have hs := arithmeticLeafSupport_mean_le S N n D hD (fun s hs => ⟨hS s hs, hN s hs⟩)
    hdiv t data (frequencyModelPairData_frequencies base S n R t hS hR small a x y)
  calc
    _ ≤ (Fintype.card (TreeLeafIndex n × Fin m → (ZMod (R ^ (n - 1 + 2)))ˣ) : ℝ)⁻¹ *
        ∑ z : TreeLeafIndex n × Fin m → (ZMod (R ^ (n - 1 + 2)))ˣ,
          amp * arithmeticLeafSupport n data
            ((treeLeafTupleEquiv (ZMod (R ^ (n - 1 + 2)))ˣ n).symm (bulkBlockProduct z)) := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg _))
      exact Finset.sum_le_sum fun z _ =>
        frequencyModelBulkCore_norm_support base tier S n m R t hS hR slot small a hslot hsmall ha hbase F E x y z
    _ = amp * ((Fintype.card (TreeLeafIndex n × Fin m → (ZMod (R ^ (n - 1 + 2)))ˣ) : ℝ)⁻¹ *
        ∑ z : TreeLeafIndex n × Fin m → (ZMod (R ^ (n - 1 + 2)))ˣ,
          arithmeticLeafSupport n data
            ((treeLeafTupleEquiv (ZMod (R ^ (n - 1 + 2)))ˣ n).symm (bulkBlockProduct z))) := by
      rw [← Finset.mul_sum]
      ring
    _ = amp * ((Fintype.card (TreeLeafTuple (ZMod (R ^ (n - 1 + 2)))ˣ n) : ℝ)⁻¹ *
        ∑ z : TreeLeafTuple (ZMod (R ^ (n - 1 + 2)))ˣ n, arithmeticLeafSupport n data z) := by
      rw [arithmeticLeafSupport_bulk_average n m hm data]
    _ ≤ _ := mul_le_mul_of_nonneg_left hs (mul_nonneg (norm_nonneg _) (norm_nonneg _))

include hslot hsmall ha hbase hS hR hD hN hdiv hm in
/-- Discarding the Page multiplier costs only two and preserves every
frequency split saving under the original bulk law. -/
theorem frequencyModelBulkPage_mean_le (input : PublishedProgressionInput)
    (Q : ℕ) (Y : ℝ) (hY : 0 ≤ Y) :
    let T := fun b => buildMovingSlotData n
      (frequencyTreeMap Subtype.val n (frequencyPairProjection S n b t))
      (small b) (bulkSlotLeaves n m slot) (a b)
    (Fintype.card (TreeLeafIndex n × Fin m → (ZMod (R ^ (n - 1 + 2)))ˣ) : ℝ)⁻¹ *
        (∑ z : TreeLeafIndex n × Fin m → (ZMod (R ^ (n - 1 + 2)))ˣ,
          ‖movingFrequencyCorePageAverage (Function.extend slot (fun j => (z j).val.val) base)
            F E T R (R ^ (n - 1 + 2)) input Q Y‖) ≤
      2 * ((‖movingDataWeight (F false) (E false) (T false)‖ *
        ‖movingDataWeight (F true) (E true) (T true)‖) *
      ((frequencySplitList S n t).map (pairFrequencySupportBound D)).prod) := by
  intro T
  have h := uniform_average_norm_average_mul_le
    (A := TreeLeafIndex n × Fin m → (ZMod (R ^ (n - 1 + 2)))ˣ)
    (B := ZMod (R ^ (n - 1 + 2)) × (ZMod (R ^ (n - 1 + 2)))ˣ)
    (fun z (xy : ZMod (R ^ (n - 1 + 2)) × (ZMod (R ^ (n - 1 + 2)))ˣ) =>
      movingFrequencyCore (Function.extend slot (fun j => (z j).val.val) base) F E T R
        xy.1.val xy.2.val.val)
    (fun xy => pageGiantWeight input Q (R ^ (n - 1 + 2)) xy.2.val.val Y)
    2 ((‖movingDataWeight (F false) (E false) (T false)‖ *
      ‖movingDataWeight (F true) (E true) (T true)‖) *
      ((frequencySplitList S n t).map (pairFrequencySupportBound D)).prod) (by norm_num)
    (fun xy => pageGiantWeight_norm_le_two input Q (R ^ (n - 1 + 2)) _ Y hY)
    (fun xy => frequencyModelBulkCore_mean_le base tier S n m R t hS hR slot small a
      hslot hsmall ha hbase F E N D hD hN hdiv hm xy.1.val xy.2.val.val)
  simpa only [movingFrequencyCorePageAverage] using h

end
end Ostmann

end OAI
