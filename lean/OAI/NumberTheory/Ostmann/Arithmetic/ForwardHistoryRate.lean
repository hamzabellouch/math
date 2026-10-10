import OAI.NumberTheory.Ostmann.Arithmetic.ForwardHistorySupport

namespace OAI

/-! # Squared forward-history weights under their original prime priors -/

namespace Ostmann

open Filter
open scoped BigOperators Classical

theorem forward_history_square_rate (n : ℕ) (K C ε : ℝ) (hC : 0 ≤ C) (hε : 0 < ε) :
    ∀ᶠ m : ℝ in atTop, ∀ N V : ℕ, ∀ Δ : ℝ, ∀ P : Finset ℕ, ∀ S : Finset ℤ,
      (N : ℝ) ≤ Real.exp (C * m) →
      (V : ℝ) ≤ Real.exp (Δ + Real.sqrt m) →
      (∀ s ∈ S, s ≠ 0 ∧ s.natAbs ≤ N) →
      ∀ XL XR : ℤ, ∀ CL CR : List Bool → ℤ,
      ∀ T : TreeLeafIndex n → Finset ℕ, ∀ h J : TreeLeafIndex n → ℕ,
      ∀ hunit : ∀ t : FrequencyTree S n, ∀ p : P,
        (p : ℕ).Coprime (historyFrequencyModulus S n n t),
      (∀ t i, historyFrequencyModulus S n n t ≤ 2 ^ h i) →
      (∀ i p, p ∈ T i → 2 ^ h i ≤ p ∧ p < 2 ^ (h i + J i)) →
      ∀ a C₁ L : ℝ, 0 < a → 1 ≤ L →
      (∀ i, a ≤ ∑ p ∈ T i, (p : ℝ)⁻¹) →
      (∀ i, (J i : ℝ) ≤ Real.exp (C₁ * L)) →
      ∀ pivots : FrequencyTree S n → (TreeLeafIndex n → P) → Fin (2 ^ n - 1) → ℤ,
      ∀ W : FrequencyTree S n → (TreeLeafIndex n → P) → ℂ,
      (∀ t x, ‖W t x‖ ^ 2 ≤ Real.exp (-(2 ^ n : ℕ) * Δ + K) *
        frequencyLeafWeight (singleFrequencyLeaf S V) n t) →
      (∀ t x, W t x ≠ 0 → forwardIntegerHistory S n (historyFrequencyModulus S n n t)
        t XL XR CL CR
        (sampledPrimeHistory P (historyFrequencyModulus S n n t) n (hunit t) x (pivots t x))) →
      (∑ t, ∑ x, (∏ i, primeSubsetPrior P (T i) (x i)) * ‖W t x‖ ^ 2) ≤
        Real.exp ((C₁ + max (Real.log (3 / a)) 0) * (2 ^ n : ℕ) * L + ε * m) := by
  filter_upwards [sampled_history_square_rate n n K C ε hC hε] with m hm
  intro N V Δ P S hN hV hS XL XR CL CR T h J hunit hsmall hrange
    a C₁ L ha hL hmass hJ pivots W hsize hnode
  let R := historyFrequencyProduct S n
  let D := fun t => forwardTreeAncestorScheme S n t XL XR CL CR
  let : ∀ t, NeZero (R t ^ (n + 2)) := fun t =>
    ⟨Nat.ne_of_gt (historyFrequencyModulus_pos S (fun s hs => (hS s hs).1) n n t)⟩
  exact hm N V Δ P S hN hV hS R D
    (fun t => forwardTreeAncestorScheme_depth S n t XL XR CL CR)
    (fun t => forwardTreeAncestorScheme_root_ne_zero S n t XL XR CL CR (fun s hs => (hS s hs).1))
    (fun t => forwardTreeAncestorScheme_frequency_dvd S n t XL XR CL CR)
    (fun _ _ => rfl) T h J hunit hsmall hrange a C₁ L ha hL hmass hJ pivots W hsize
    (fun t x hx => forwardIntegerHistory_valid S n (R t ^ (n + 2)) t XL XR CL CR
      (sampledPrimeHistory P _ n (hunit t) x (pivots t x)) (hnode t x hx))

end Ostmann

end OAI
