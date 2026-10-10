import OAI.NumberTheory.Ostmann.Arithmetic.FrequencyBulkNorm
import OAI.NumberTheory.Ostmann.Arithmetic.MovingPrimePageCRT

namespace OAI

/-! # The retained frequency norm when both top giants are primes -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def movingFrequencyCorePrimeAverage {σ : Type*} (value : σ → ℕ)
    (F : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
    (E : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℤ → ℤ → ℝ)
    {n : ℕ} (T : Bool → MovingSlotData σ n) (R : ℤ)
    (r : ℕ) [NeZero r] (input : PublishedProgressionInput) (Q : ℕ) (x y : ℝ) : ℂ :=
  (Fintype.card ((ZMod r)ˣ × (ZMod r)ˣ) : ℂ)⁻¹ *
    ∑ z : (ZMod r)ˣ × (ZMod r)ˣ,
      movingFrequencyCore value F E T R z.1.val.val z.2.val.val *
        (pageGiantWeight input Q r z.1.val.val x * pageGiantWeight input Q r z.2.val.val y)

noncomputable def movingFrequencyPrimeAverage {σ : Type*} (value : σ → ℕ)
    (outside : List ℕ)
    (F : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
    (E : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℤ → ℤ → ℝ)
    {n : ℕ} (T : Bool → MovingSlotData σ n) (nodes : Bool → List MovingFormulaNode)
    (R : ℤ) (r : ℕ) [NeZero r] (input : PublishedProgressionInput) (Q : ℕ) (x y : ℝ) : ℂ :=
  correctedPrimePairAverage input Q r
    (fun a b => movingFrequencyPairFactor value outside F E T nodes R a b) x y

theorem movingFrequencyPrimeAverage_core {σ : Type*} (value : σ → ℕ)
    (outside : List ℕ)
    (F : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℂ)
    (E : Bool → {n : ℕ} → MovingSlotData σ n → ℤ → ℤ → ℤ → ℝ)
    {n : ℕ} (T : Bool → MovingSlotData σ n) (nodes : Bool → List MovingFormulaNode)
    (R : ℤ) (r : ℕ) [NeZero r] (input : PublishedProgressionInput) (Q : ℕ) (x y : ℝ) :
    movingFrequencyPrimeAverage value outside F E T nodes R r input Q x y =
      (if ∀ b, movingRegularOutsidePairwise value outside (T b) ∧
        (∀ f ∈ nodes b, f.guard.frequencyBounds) then (1 : ℂ) else 0) *
      movingFrequencyCorePrimeAverage value F E T R r input Q x y := by
  simp only [movingFrequencyPrimeAverage, correctedPrimePairAverage,
    movingFrequencyPairFactor_core, movingFrequencyCorePrimeAverage, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z _
  ring

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
/-- Two giant Page multipliers cost four. Their residue restrictions do not
change the previously proved conditional split probabilities. -/
theorem frequencyModelBulkPrime_mean_le (input : PublishedProgressionInput)
    (Q : ℕ) (X Y : ℝ) (hX : 0 ≤ X) (hY : 0 ≤ Y) :
    let T := fun b => buildMovingSlotData n
      (frequencyTreeMap Subtype.val n (frequencyPairProjection S n b t))
      (small b) (bulkSlotLeaves n m slot) (a b)
    (Fintype.card (TreeLeafIndex n × Fin m → (ZMod (R ^ (n - 1 + 2)))ˣ) : ℝ)⁻¹ *
        (∑ z : TreeLeafIndex n × Fin m → (ZMod (R ^ (n - 1 + 2)))ˣ,
          ‖movingFrequencyCorePrimeAverage (Function.extend slot (fun j => (z j).val.val) base)
            F E T R (R ^ (n - 1 + 2)) input Q X Y‖) ≤
      4 * ((‖movingDataWeight (F false) (E false) (T false)‖ *
        ‖movingDataWeight (F true) (E true) (T true)‖) *
      ((frequencySplitList S n t).map (pairFrequencySupportBound D)).prod) := by
  intro T
  have h := uniform_average_norm_average_mul_le
    (A := TreeLeafIndex n × Fin m → (ZMod (R ^ (n - 1 + 2)))ˣ)
    (B := (ZMod (R ^ (n - 1 + 2)))ˣ × (ZMod (R ^ (n - 1 + 2)))ˣ)
    (fun z (xy : (ZMod (R ^ (n - 1 + 2)))ˣ × (ZMod (R ^ (n - 1 + 2)))ˣ) =>
      movingFrequencyCore (Function.extend slot (fun j => (z j).val.val) base) F E T R
        xy.1.val.val xy.2.val.val)
    (fun xy => pageGiantWeight input Q (R ^ (n - 1 + 2)) xy.1.val.val X *
      pageGiantWeight input Q (R ^ (n - 1 + 2)) xy.2.val.val Y)
    4 ((‖movingDataWeight (F false) (E false) (T false)‖ *
      ‖movingDataWeight (F true) (E true) (T true)‖) *
      ((frequencySplitList S n t).map (pairFrequencySupportBound D)).prod) (by norm_num)
    (fun xy => by
      rw [norm_mul]
      exact (mul_le_mul
        (pageGiantWeight_norm_le_two input Q (R ^ (n - 1 + 2)) _ X hX)
        (pageGiantWeight_norm_le_two input Q (R ^ (n - 1 + 2)) _ Y hY)
        (norm_nonneg _) (by norm_num)).trans_eq (by norm_num))
    (fun xy => frequencyModelBulkCore_mean_le base tier S n m R t hS hR slot small a
      hslot hsmall ha hbase F E N D hD hN hdiv hm xy.1.val.val xy.2.val.val)
  simpa only [movingFrequencyCorePrimeAverage] using h

end
end Ostmann

end OAI
