import OAI.NumberTheory.Ostmann.Arithmetic.WeightedArithmeticSupport
import OAI.NumberTheory.Ostmann.Construction.SpectatorSmoothNorm

namespace OAI

/-! # The norm of the idealized arithmetic history expansion

Both sets of residue variables retain their original independent Haar
laws. The smooth amplitude may depend on every coordinate.
-/

namespace Ostmann

open scoped BigOperators Classical
open Filter

noncomputable def idealHistoryNorm {Q : ℕ} [NeZero Q]
    {I : Type*} [Fintype I] (p : I → ℕ) [∀ i, Fact (p i).Prime]
    (S : Finset ℤ) (V n : ℕ) (g : ∀ i, ZMod (p i) → ℂ)
    (data : FrequencyTree (S × S) n → (ZMod Q)ˣ → List (ZMod Q)ˣ →
      Option (ArithmeticSplitData Q × ArithmeticSplitData Q))
    (d e : FrequencyTree (S × S) n → TreeLeafTuple (ZMod Q)ˣ n →
      ∀ i, SpectatorDiagram (p i) n)
    (Ξ : FrequencyTree (S × S) n → TreeLeafTuple (ZMod Q)ˣ n →
      (∀ i, TreeLeafTuple (ZMod (p i))ˣ n) → ℂ) : ℝ :=
  arithmeticWeightedSupportSum S V n data
    (fun t x => smoothSpectatorAverage p n g (d t x) (e t x) (Ξ t x))

theorem idealHistoryNorm_le {Q : ℕ} [NeZero Q]
    {I : Type*} [Fintype I] (p : I → ℕ) [∀ i, Fact (p i).Prime]
    (S : Finset ℤ) (V n : ℕ) (hp : ∀ i, 3 ≤ p i)
    (g : ∀ i, ZMod (p i) → ℂ) (hg : ∀ i, g i 0 = 0)
    (henergy : ∀ i, (∑ x : ZMod (p i), ‖g i x‖ ^ 2) ≤ (p i : ℝ))
    (data : FrequencyTree (S × S) n → (ZMod Q)ˣ → List (ZMod Q)ˣ →
      Option (ArithmeticSplitData Q × ArithmeticSplitData Q))
    (d e : FrequencyTree (S × S) n → TreeLeafTuple (ZMod Q)ˣ n →
      ∀ i, SpectatorDiagram (p i) n)
    (Ξ : FrequencyTree (S × S) n → TreeLeafTuple (ZMod Q)ˣ n →
      (∀ i, TreeLeafTuple (ZMod (p i))ˣ n) → ℂ)
    (E : ℝ) (hE : 0 ≤ E) (hΞ : ∀ t x y, ‖Ξ t x y‖ ≤ E) :
    idealHistoryNorm p S V n g data d e Ξ ≤
      (E * (3 : ℝ) ^ (2 ^ n * Fintype.card I)) * arithmeticProductSupportSum S V n data :=
  arithmeticWeightedSupportSum_le S V n data _ _ (fun t x =>
    smoothSpectatorAverage_le p n hp g hg henergy (d t x) (e t x) (Ξ t x) E hE (hΞ t x))

theorem ideal_history_norm_rate {Q : ℕ} [NeZero Q]
    {I : Type*} [Fintype I] (p : I → ℕ) [∀ i, Fact (p i).Prime]
    (n : ℕ) (hp : ∀ i, 3 ≤ p i)
    (g : ∀ i, ZMod (p i) → ℂ) (hg : ∀ i, g i 0 = 0)
    (henergy : ∀ i, (∑ x : ZMod (p i), ‖g i x‖ ^ 2) ≤ (p i : ℝ))
    (K C ε : ℝ) (hC : 0 ≤ C) (hε : 0 < ε) :
    ∀ᶠ m : ℝ in atTop, ∀ N V : ℕ, ∀ Δ : ℝ, ∀ S : Finset ℤ,
      (N : ℝ) ≤ Real.exp (C * m) →
      (V : ℝ) ≤ Real.exp (Δ + Real.sqrt m) →
      (∀ s ∈ S, s ≠ 0 ∧ s.natAbs ≤ N) →
      ∀ data : FrequencyTree (S × S) n → (ZMod Q)ˣ → List (ZMod Q)ˣ →
        Option (ArithmeticSplitData Q × ArithmeticSplitData Q),
      (∀ t P past a b, data t P past = some (a, b) →
        a.hasFrequencies (treeNodeFrequencies S n t past.length).1 ∧
          b.hasFrequencies (treeNodeFrequencies S n t past.length).2) →
      ∀ d e : FrequencyTree (S × S) n → TreeLeafTuple (ZMod Q)ˣ n →
        ∀ i, SpectatorDiagram (p i) n,
      ∀ Ξ : FrequencyTree (S × S) n → TreeLeafTuple (ZMod Q)ˣ n →
        (∀ i, TreeLeafTuple (ZMod (p i))ˣ n) → ℂ,
      (∀ t x y, ‖Ξ t x y‖ ≤ Real.exp (-(2 ^ n : ℕ) * Δ + K)) →
      idealHistoryNorm p S V n g data d e Ξ ≤
        (3 : ℝ) ^ (2 ^ n * Fintype.card I) * Real.exp ((2 ^ n : ℕ) * Δ + ε * m) := by
  filter_upwards [arithmetic_product_support_rate (Q := Q) n K C ε hC hε] with m hm
  intro N V Δ S hN hV hS data hmatch d e Ξ hΞ
  calc
    _ ≤ (Real.exp (-(2 ^ n : ℕ) * Δ + K) * (3 : ℝ) ^ (2 ^ n * Fintype.card I)) *
        arithmeticProductSupportSum S V n data :=
      idealHistoryNorm_le p S V n hp g hg henergy data d e Ξ _ (Real.exp_pos _).le hΞ
    _ = (3 : ℝ) ^ (2 ^ n * Fintype.card I) *
        (Real.exp (-(2 ^ n : ℕ) * Δ + K) * arithmeticProductSupportSum S V n data) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (hm N V Δ S hN hV hS data hmatch) (by positivity)

end Ostmann

end OAI
