import OAI.NumberTheory.Ostmann.Construction.ScheduledSampledValidity
import OAI.NumberTheory.Ostmann.Construction.ScheduledFourierEnergy
import OAI.NumberTheory.Ostmann.Arithmetic.SampledHistoryRate

namespace OAI

/-! # The sharp squared-history estimate for the actual scheduled Fourier weight -/

namespace Ostmann
open Filter
open scoped BigOperators Classical SchwartzMap FourierTransform

/-- The original prime law is retained. Both the integer equations and the
coefficient units come from the full weight; only published analytic estimates
and the explicit prime-cell size conditions remain for the final application. -/
theorem uniform_scheduled_clipped_square_rate (n : ℕ)
    (ψ : 𝓢(ℝ, ℂ)) (C₀ K C ε : ℝ) (hC : 0 ≤ C) (hε : 0 < ε)
    (hψ : SchwartzMap.seminorm ℝ 0 0 (𝓕 ψ : 𝓢(ℝ, ℂ)) ≤ Real.exp K) :
    ∀ᶠ m : ℝ in atTop,
      ∀ {I : Type*} [Fintype I],
      ∀ (role : I → CopyScheduleRole) (childBound pivotBound : ℕ → ℕ)
        (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
        (i : I) (hi : role i = .word)
        (_hu : ∀ k < n, ∀ a b, role a = .pivot k → role b = .pivot k → a = b),
      ∀ N V : ℕ, ∀ Δ X lo upper : ℝ,
      ∀ P : Finset ℕ, ∀ S : Finset ℤ,
      (N : ℝ) ≤ Real.exp (C * m) →
      (V : ℝ) ≤ Real.exp (Δ + Real.sqrt m) →
      (∀ s ∈ S, s ≠ 0 ∧ s.natAbs ≤ N) →
      (∀ p ∈ P, p.Prime ∧ N < p) →
      0 < X → Real.exp (Δ - C₀) ≤ lo →
      ∀ T : Finset ℕ, ∀ h J : ℕ,
      (∀ t : FrequencyTree S n, historyFrequencyModulus S n n t ≤ 2 ^ h) →
      (∀ p ∈ T, 2 ^ h ≤ p ∧ p < 2 ^ (h + J)) →
      ∀ a C₁ L : ℝ, 0 < a → 1 ≤ L →
      a ≤ ∑ p ∈ T, (p : ℝ)⁻¹ → (J : ℝ) ≤ Real.exp (C₁ * L) →
      ∀ base : CopyScheduleAtoms role n → ℕ,
      (∑ t : FrequencyTree S n, ∑ x : TreeLeafIndex n → P,
        (∏ j, primeSubsetPrior P T (x j)) *
          ‖clippedFullAtomFourierWeight role childBound pivotBound ranges ψ X lo upper S V n
            (wordLeafScale role i hi n base (fun j => (x j : ℕ))) t‖ ^ 2) ≤
        Real.exp ((C₁ + max (Real.log (3 / a)) 0) * (2 ^ n : ℕ) * L + ε * m) := by
  filter_upwards [sampled_history_square_rate n n ((2 ^ n : ℕ) * (C₀ + 2 * K)) C ε hC hε]
    with m hm
  intro I instI role childBound pivotBound ranges i hi hu N V Δ X lo upper P S hN hV hS hP hX hlo T h J hsmall hrange a C₁ L ha hL hmass hJ base
  let R := historyFrequencyProduct S n
  let D := fun t : FrequencyTree S n =>
    scheduledActualSourceScheme role S n t (fun v => (base v : ℤ))
  let hunit : ∀ t : FrequencyTree S n, ∀ p : P, (p : ℕ).Coprime (R t ^ (n + 2)) :=
    fun t p => prime_coprime_historyFrequencyModulus S N p (hP p p.property).1
      (hP p p.property).2 hS n n t
  have : ∀ t : FrequencyTree S n, NeZero (R t ^ (n + 2)) := fun t =>
    ⟨Nat.ne_of_gt (historyFrequencyModulus_pos S (fun s hs => (hS s hs).1) n n t)⟩
  let pivots := fun (t : FrequencyTree S n) (x : TreeLeafIndex n → P) (j : Fin (2 ^ n - 1)) =>
    ((transferPivotArray (scheduleAtomSystem role childBound pivotBound) n
      ⟨n, wordLeafScale role i hi n base (fun j => (x j : ℕ))⟩
      (frequencyTreeMap Subtype.val n t) j : ℕ) : ℤ)
  let W := fun (t : FrequencyTree S n) (x : TreeLeafIndex n → P) =>
    clippedFullAtomFourierWeight role childBound pivotBound ranges ψ X lo upper S V n
      (wordLeafScale role i hi n base (fun j => (x j : ℕ))) t
  apply hm N V Δ P S hN hV hS R D
    (fun t j => scheduledSourceScheme_depth role S n t _ _ _ j)
    (fun t j => scheduledSourceScheme_root_ne_zero role S n t _ _ _
      (fun s hs => (hS s hs).1) j)
    (fun t j => scheduledSourceScheme_frequency_dvd role S n t _ _ _ j)
    (fun _ _ => rfl) (fun _ => T) (fun _ => h) (fun _ => J) hunit
    (fun t _ => hsmall t) (fun _ p hp => hrange p hp)
    a C₁ L ha hL (fun _ => hmass) (fun _ => hJ) pivots W
  · intro t x
    exact clippedFullAtomFourierWeight_square_le role childBound pivotBound ranges ψ X lo upper
      Δ C₀ K hX hlo hψ S V n _ t
  · intro t x hx
    have hfull : fullAtomTransferWeight role childBound pivotBound ranges
        (scheduleFourierLeaf role ψ X lo upper) n
        (wordLeafScale role i hi n base (fun j => (x j : ℕ)))
        (frequencyTreeMap Subtype.val n t) ≠ 0 := by
      unfold W clippedFullAtomFourierWeight at hx
      split_ifs at hx
      · exact hx
      · exact False.elim (hx rfl)
    exact fullAtomTransferWeight_sampled_valid role childBound pivotBound ranges
      (scheduleFourierLeaf role ψ X lo upper) i hi S n base P (R t ^ (n + 2))
      (hunit t) x t hu hfull

theorem scheduled_clipped_square_rate {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (childBound pivotBound : ℕ → ℕ)
    (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (i : I) (hi : role i = .word) (n : ℕ)
    (hu : ∀ k < n, ∀ a b, role a = .pivot k → role b = .pivot k → a = b)
    (ψ : 𝓢(ℝ, ℂ)) (C₀ K C ε : ℝ) (hC : 0 ≤ C) (hε : 0 < ε)
    (hψ : SchwartzMap.seminorm ℝ 0 0 (𝓕 ψ : 𝓢(ℝ, ℂ)) ≤ Real.exp K) :
    ∀ᶠ m : ℝ in atTop, ∀ N V : ℕ, ∀ Δ X lo upper : ℝ,
      ∀ P : Finset ℕ, ∀ S : Finset ℤ,
      (N : ℝ) ≤ Real.exp (C * m) →
      (V : ℝ) ≤ Real.exp (Δ + Real.sqrt m) →
      (∀ s ∈ S, s ≠ 0 ∧ s.natAbs ≤ N) →
      (∀ p ∈ P, p.Prime ∧ N < p) →
      0 < X → Real.exp (Δ - C₀) ≤ lo →
      ∀ T : Finset ℕ, ∀ h J : ℕ,
      (∀ t : FrequencyTree S n, historyFrequencyModulus S n n t ≤ 2 ^ h) →
      (∀ p ∈ T, 2 ^ h ≤ p ∧ p < 2 ^ (h + J)) →
      ∀ a C₁ L : ℝ, 0 < a → 1 ≤ L →
      a ≤ ∑ p ∈ T, (p : ℝ)⁻¹ → (J : ℝ) ≤ Real.exp (C₁ * L) →
      ∀ base : CopyScheduleAtoms role n → ℕ,
      (∑ t : FrequencyTree S n, ∑ x : TreeLeafIndex n → P,
        (∏ j, primeSubsetPrior P T (x j)) *
          ‖clippedFullAtomFourierWeight role childBound pivotBound ranges ψ X lo upper S V n
            (wordLeafScale role i hi n base (fun j => (x j : ℕ))) t‖ ^ 2) ≤
        Real.exp ((C₁ + max (Real.log (3 / a)) 0) * (2 ^ n : ℕ) * L + ε * m) := by
  filter_upwards [uniform_scheduled_clipped_square_rate n ψ C₀ K C ε hC hε hψ] with m hm
  exact hm role childBound pivotBound ranges i hi hu

end Ostmann

end OAI
