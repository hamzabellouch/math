import OAI.NumberTheory.TwoPoint.Fourier.MinorArcSquareLogError

namespace OAI

/-! The minor-arc part of corrected MRT, Section 3: the literal typical-set
short integral has the required log-log over log saving. -/

namespace TwoPointCorrelations

open Finset

theorem minor_arc_typical_short_bound :
    ∃ C : ℝ, 0 < C ∧ ∃ R₀ : ℕ,
      ∀ {ι : Type*} (I : Finset ι) (P : ι → Finset ℕ),
      (∀ i ∈ I, ∀ p ∈ P i, p.Prime) → Set.PairwiseDisjoint (I : Set ι) P →
      ∀ i ∈ I, ∀ (X H : ℕ), 2 ≤ H → H ≤ X →
      1 ≤ Real.log (H : ℝ) → 1 ≤ Real.log (Real.log (H : ℝ)) →
      (∀ p ∈ P i, p ≠ 2 ∧ 2 * R₀ ≤ p ∧
        2 * (Real.log (H : ℝ)) ^ 5 ≤ (p : ℝ) ∧
        (p : ℝ) ≤ (H : ℝ) / (Real.log (H : ℝ)) ^ 5) →
      ∀ (F : ℕ → ℂ), Multiplicative F → OneBounded F →
      ∀ (r : ℤ) (q : ℕ), 2 ≤ q →
      (Real.log (H : ℝ)) ^ 5 ≤ (q : ℝ) →
      (q : ℝ) ≤ (H : ℝ) / (Real.log (H : ℝ)) ^ 5 →
      ∀ α : ℝ, IsCoprime (q : ℤ) r →
      |α - (r : ℝ) / (q : ℝ)| ≤ 1 / (q : ℝ) ^ 2 →
      shortExponentialIntegral (mrtTypicalCoefficient I P F) X H α ≤
        C * (X : ℝ) * H * Real.log (Real.log (H : ℝ)) / Real.log (H : ℝ) := by
  obtain ⟨C, hC, R₀, hbound⟩ := minor_arc_typical_prime_range_saving
  refine ⟨C + 12, by positivity, R₀, ?_⟩
  intro ι I P hP hdis i hi X H hH hHX hlogH hloglog hrange F hF hFb
    r q hq hWq hqH α hcop happ
  have ht := hbound I P hP hdis i hi X H hH hHX hlogH hloglog hrange
    F hF hFb r q hq hWq hqH α hcop happ
  have hW : 1 ≤ (Real.log (H : ℝ)) ^ 5 := one_le_pow₀ hlogH
  have hr : ∀ p ∈ P i, (Real.log (H : ℝ)) ^ 5 ≤ (p : ℝ) ∧ p ≤ H := by
    intro p hp
    have hlow := (hrange p hp).2.2.1
    have hhigh := (hrange p hp).2.2.2
    refine ⟨by linarith, ?_⟩
    have hh : (p : ℝ) ≤ H := hhigh.trans (div_le_self (Nat.cast_nonneg H) hW)
    exact_mod_cast hh
  have he := minor_arc_square_log_error (P i) X H hHX hlogH hloglog hr
  apply ht.trans
  convert add_le_add (le_refl (C * (X : ℝ) * H * Real.log (Real.log (H : ℝ)) /
    Real.log (H : ℝ))) he using 1
  ring

end TwoPointCorrelations

end OAI
