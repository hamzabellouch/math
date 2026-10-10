import OAI.NumberTheory.Ostmann.Arithmetic.ArithmeticProductSupport
import OAI.NumberTheory.Ostmann.Arithmetic.ArithmeticResidueReversal

namespace OAI

/-! # The independent bulk support bound for concrete residue numerators -/

namespace Ostmann

open scoped BigOperators Classical
open Filter

theorem sequentialSupport_congr {A : Type} (test₁ test₂ : List A → A → Prop)
    (h : ∀ past x, test₁ past x ↔ test₂ past x) (past : List A)
    (n : ℕ) (x : SplitSamples A n) :
    sequentialSupport test₁ past n x = sequentialSupport test₂ past n x := by
  induction n generalizing past with
  | zero => rfl
  | succ n ih =>
      change (if test₁ past x.1 then sequentialSupport test₁ (x.1 :: past) n x.2 else 0) =
        (if test₂ past x.1 then sequentialSupport test₂ (x.1 :: past) n x.2 else 0)
      rw [propext (h past x.1)]
      split_ifs
      · exact ih _ _
      · rfl

noncomputable def residueProductSupportSum {Q : ℕ} [NeZero Q]
    (S : Finset ℤ) (V n : ℕ)
    (data : FrequencyTree (S × S) n → (ZMod Q)ˣ → List (ZMod Q)ˣ →
      ArithmeticResidueSplit Q × ArithmeticResidueSplit Q) : ℝ :=
  ∑ t : FrequencyTree (S × S) n,
    frequencyLeafWeight (pairedFrequencyLeaf S V) n t *
      ((Fintype.card (TreeLeafTuple (ZMod Q)ˣ n) : ℝ)⁻¹ *
        ∑ x : TreeLeafTuple (ZMod Q)ˣ n,
          sequentialSupport
            (fun past y => (data t (treeLeafProduct n x) past).1.support y ∧
              (data t (treeLeafProduct n x) past).2.support y) []
            (2 ^ n - 1) (treeLeafSplitEquiv n (treeLeafProduct n x) ⟨x, rfl⟩))

theorem residueProductSupportSum_eq {Q : ℕ} [NeZero Q]
    (S : Finset ℤ) (V n : ℕ)
    (data : FrequencyTree (S × S) n → (ZMod Q)ˣ → List (ZMod Q)ˣ →
      ArithmeticResidueSplit Q × ArithmeticResidueSplit Q) :
    residueProductSupportSum S V n data = arithmeticProductSupportSum S V n
      (fun t P past => arithmeticResiduePairData (data t P past).1 (data t P past).2) := by
  unfold residueProductSupportSum arithmeticProductSupportSum
  apply Finset.sum_congr rfl
  intro t _
  congr 1
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  apply sequentialSupport_congr
  intro past y
  exact (arithmeticResiduePairData_test _ _ y).symm

theorem residue_product_support_rate {Q : ℕ} [NeZero Q]
    (n : ℕ) (K C ε : ℝ) (hC : 0 ≤ C) (hε : 0 < ε) :
    ∀ᶠ m : ℝ in atTop, ∀ N V : ℕ, ∀ Δ : ℝ, ∀ S : Finset ℤ,
      (N : ℝ) ≤ Real.exp (C * m) →
      (V : ℝ) ≤ Real.exp (Δ + Real.sqrt m) →
      (∀ s ∈ S, s ≠ 0 ∧ s.natAbs ≤ N) →
      ∀ data : FrequencyTree (S × S) n → (ZMod Q)ˣ → List (ZMod Q)ˣ →
        ArithmeticResidueSplit Q × ArithmeticResidueSplit Q,
      (∀ t P past, (data t P past).1.frequencies =
          (treeNodeFrequencies S n t past.length).1 ∧
        (data t P past).2.frequencies = (treeNodeFrequencies S n t past.length).2) →
      Real.exp (-(2 ^ n : ℕ) * Δ + K) * residueProductSupportSum S V n data ≤
        Real.exp ((2 ^ n : ℕ) * Δ + ε * m) := by
  filter_upwards [arithmetic_product_support_rate (Q := Q) n K C ε hC hε] with m hm
  intro N V Δ S hN hV hS data hmatch
  rw [residueProductSupportSum_eq]
  apply hm N V Δ S hN hV hS
  intro t P past d e h
  have hd := arithmeticResiduePairData_frequencies _ _ d e h
  rw [(hmatch t P past).1] at hd
  rw [(hmatch t P past).2] at hd
  exact hd

end Ostmann

end OAI
