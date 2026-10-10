import OAI.NumberTheory.Ostmann.Arithmetic.SampledHistoryEnergy
import OAI.NumberTheory.Ostmann.Arithmetic.HarmonicHistoryRates

namespace OAI

/-! # Original-prior squared-history rate from integer reversals -/

namespace Ostmann

open Filter
open scoped BigOperators Classical

theorem adaptivePivotData_history_frequencies (S : Finset ℤ) (n R k : ℕ)
    (t : FrequencyTree S n) (D : PivotDependencyScheme (2 ^ n - 1))
    (hs : ∀ i, (D.frequencies i).root ≠ 0)
    (hsR : ∀ i, (D.frequencies i).root.natAbs ∣ R)
    (hfreq : ∀ i, D.frequencies i = singleTreeNodeFrequencies S n t i.val)
    (total : (ZMod (R ^ (k + 2)))ˣ) (past : List (ZMod (R ^ (k + 2)))ˣ)
    (d : ArithmeticSplitData (R ^ (k + 2)))
    (hd : adaptivePivotData n R k D hs hsR total past = some d) :
    d.hasFrequencies (singleTreeNodeFrequencies S n t past.length) := by
  by_cases hj : past.length < 2 ^ n - 1
  · have h := adaptivePivotData_frequencies n R k D hs hsR total past hj d hd
    rwa [hfreq] at h
  · simp only [adaptivePivotData, hj, dite_false] at hd
    cases hd

/-- This is the squared-history estimate with actual prime sampling and
actual integer integrality/unit conditions. The adaptive-support event is
constructed, and is not an additional hypothesis. -/
theorem sampled_history_square_rate (n k : ℕ) (K C ε : ℝ) (hC : 0 ≤ C) (hε : 0 < ε) :
    ∀ᶠ m : ℝ in atTop, ∀ N V : ℕ, ∀ Δ : ℝ, ∀ P : Finset ℕ, ∀ S : Finset ℤ,
      (N : ℝ) ≤ Real.exp (C * m) →
      (V : ℝ) ≤ Real.exp (Δ + Real.sqrt m) →
      (∀ s ∈ S, s ≠ 0 ∧ s.natAbs ≤ N) →
      ∀ R : FrequencyTree S n → ℕ, ∀ [_hQ : ∀ t, NeZero (R t ^ (k + 2))],
      ∀ D : FrequencyTree S n → PivotDependencyScheme (2 ^ n - 1),
      (∀ t i, (D t).depth i ≤ k) →
      ∀ _hs : ∀ t i, ((D t).frequencies i).root ≠ 0,
      ∀ _hsR : ∀ t i, ((D t).frequencies i).root.natAbs ∣ R t,
      (∀ t i, (D t).frequencies i = singleTreeNodeFrequencies S n t i.val) →
      ∀ T : TreeLeafIndex n → Finset ℕ, ∀ h J : TreeLeafIndex n → ℕ,
      ∀ hunit : ∀ t, ∀ p : P, (p : ℕ).Coprime (R t ^ (k + 2)),
      (∀ t i, R t ^ (k + 2) ≤ 2 ^ h i) →
      (∀ i p, p ∈ T i → 2 ^ h i ≤ p ∧ p < 2 ^ (h i + J i)) →
      ∀ a C₁ L : ℝ, 0 < a → 1 ≤ L →
      (∀ i, a ≤ ∑ p ∈ T i, (p : ℝ)⁻¹) →
      (∀ i, (J i : ℝ) ≤ Real.exp (C₁ * L)) →
      ∀ pivots : FrequencyTree S n → (TreeLeafIndex n → P) → Fin (2 ^ n - 1) → ℤ,
      ∀ W : FrequencyTree S n → (TreeLeafIndex n → P) → ℂ,
      (∀ t x, ‖W t x‖ ^ 2 ≤ Real.exp (-(2 ^ n : ℕ) * Δ + K) *
        frequencyLeafWeight (singleFrequencyLeaf S V) n t) →
      (∀ t x, W t x ≠ 0 →
        (sampledPrimeHistory P (R t ^ (k + 2)) n (hunit t) x (pivots t x)).valid (D t)) →
      (∑ t, ∑ x, (∏ i, primeSubsetPrior P (T i) (x i)) * ‖W t x‖ ^ 2) ≤
        Real.exp ((C₁ + max (Real.log (3 / a)) 0) * (2 ^ n : ℕ) * L + ε * m) := by
  filter_upwards [harmonic_history_support_rate n K C ε hC hε] with m hm
  intro N V Δ P S hN hV hS R _hQ D hdepth hs hsR hfreq T h J hunit hsmall hrange
    a C₁ L ha hL hmass hJ pivots W hsize hvalid
  have hb := sampled_history_square_sum_le P S V n k R D hdepth hs hsR T hunit pivots W
    (Real.exp (-(2 ^ n : ℕ) * Δ + K)) (Real.exp_pos _).le hsize hvalid
  exact hb.trans (hm N V Δ P S hN hV hS (fun t => R t ^ (k + 2)) T h J hunit hsmall hrange
    a C₁ L ha hL hmass hJ (fun t => adaptivePivotData n (R t) k (D t) (hs t) (hsR t))
    (fun t => adaptivePivotData_history_frequencies S n (R t) k t (D t) (hs t) (hsR t) (hfreq t)))

end Ostmann

end OAI
