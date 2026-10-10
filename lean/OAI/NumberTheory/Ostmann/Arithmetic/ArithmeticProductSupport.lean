import OAI.NumberTheory.Ostmann.Arithmetic.ArithmeticSupportRate
import OAI.NumberTheory.Ostmann.Characters.TreeProductDisintegration

namespace OAI

/-! # The frequency-support estimate under the independent leaf law -/

namespace Ostmann

open scoped BigOperators Classical
open Filter

noncomputable def arithmeticProductSupportSum {Q : ℕ} [NeZero Q]
    (S : Finset ℤ) (V n : ℕ)
    (data : FrequencyTree (S × S) n → (ZMod Q)ˣ → List (ZMod Q)ˣ →
      Option (ArithmeticSplitData Q × ArithmeticSplitData Q)) : ℝ :=
  ∑ t : FrequencyTree (S × S) n,
    frequencyLeafWeight (pairedFrequencyLeaf S V) n t *
      ((Fintype.card (TreeLeafTuple (ZMod Q)ˣ n) : ℝ)⁻¹ *
        ∑ x : TreeLeafTuple (ZMod Q)ˣ n,
          sequentialSupport
            (fun past y => arithmeticPairSplitTest (data t (treeLeafProduct n x) past) y) []
            (2 ^ n - 1) (treeLeafSplitEquiv n (treeLeafProduct n x) ⟨x, rfl⟩))

theorem arithmeticProductSupportSum_eq {Q : ℕ} [NeZero Q]
    (S : Finset ℤ) (V n : ℕ)
    (data : FrequencyTree (S × S) n → (ZMod Q)ˣ → List (ZMod Q)ˣ →
      Option (ArithmeticSplitData Q × ArithmeticSplitData Q)) :
    arithmeticProductSupportSum S V n data =
      (Fintype.card (ZMod Q)ˣ : ℝ)⁻¹ * ∑ P : (ZMod Q)ˣ,
        arithmeticHistorySupportSum S V n (fun _ => P) (fun t => data t P) := by
  unfold arithmeticProductSupportSum
  calc
    _ = ∑ t : FrequencyTree (S × S) n,
        frequencyLeafWeight (pairedFrequencyLeaf S V) n t *
          ((Fintype.card (ZMod Q)ˣ : ℝ)⁻¹ * ∑ P : (ZMod Q)ˣ,
            (Fintype.card (TreeLeafFiber (ZMod Q)ˣ n P) : ℝ)⁻¹ *
              ∑ x : TreeLeafFiber (ZMod Q)ˣ n P,
                sequentialSupport (fun past y => arithmeticPairSplitTest (data t P past) y) []
                  (2 ^ n - 1) (treeLeafSplitEquiv n P x)) := by
      apply Finset.sum_congr rfl
      intro t _
      congr 1
      exact treeLeaf_average_by_product (G := (ZMod Q)ˣ) n
        (fun P x => sequentialSupport
          (fun past y => arithmeticPairSplitTest (data t P past) y) []
          (2 ^ n - 1) (treeLeafSplitEquiv n P x))
    _ = _ := by
      unfold arithmeticHistorySupportSum
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro P _
      apply Finset.sum_congr rfl
      intro t _
      ring_nf

/-- No restriction on the total leaf product appears here: this is the
original independent product measure on all bulk leaf products. -/
theorem arithmetic_product_support_rate {Q : ℕ} [NeZero Q]
    (n : ℕ) (K C ε : ℝ) (hC : 0 ≤ C) (hε : 0 < ε) :
    ∀ᶠ m : ℝ in atTop, ∀ N V : ℕ, ∀ Δ : ℝ, ∀ S : Finset ℤ,
      (N : ℝ) ≤ Real.exp (C * m) →
      (V : ℝ) ≤ Real.exp (Δ + Real.sqrt m) →
      (∀ s ∈ S, s ≠ 0 ∧ s.natAbs ≤ N) →
      ∀ data : FrequencyTree (S × S) n → (ZMod Q)ˣ → List (ZMod Q)ˣ →
        Option (ArithmeticSplitData Q × ArithmeticSplitData Q),
      (∀ t P past d e, data t P past = some (d, e) →
        d.hasFrequencies (treeNodeFrequencies S n t past.length).1 ∧
          e.hasFrequencies (treeNodeFrequencies S n t past.length).2) →
      Real.exp (-(2 ^ n : ℕ) * Δ + K) * arithmeticProductSupportSum S V n data ≤
        Real.exp ((2 ^ n : ℕ) * Δ + ε * m) := by
  filter_upwards [arithmetic_history_support_rate (Q := Q) n K C ε hC hε] with m hm
  intro N V Δ S hN hV hS data hmatch
  rw [arithmeticProductSupportSum_eq]
  calc
    _ = (Fintype.card (ZMod Q)ˣ : ℝ)⁻¹ * ∑ P : (ZMod Q)ˣ,
        Real.exp (-(2 ^ n : ℕ) * Δ + K) *
          arithmeticHistorySupportSum S V n (fun _ => P) (fun t => data t P) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro P _
      ring
    _ ≤ (Fintype.card (ZMod Q)ˣ : ℝ)⁻¹ * ∑ _P : (ZMod Q)ˣ,
        Real.exp ((2 ^ n : ℕ) * Δ + ε * m) := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg _))
      exact Finset.sum_le_sum fun P _ => hm N V Δ S hN hV hS _ _ (fun t => hmatch t P)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast Fintype.card_ne_zero), one_mul]

end Ostmann

end OAI
