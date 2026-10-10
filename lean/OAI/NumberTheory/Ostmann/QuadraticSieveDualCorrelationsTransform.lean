import OAI.NumberTheory.Ostmann.QuadraticSieveDualCorrelationsPairError

namespace OAI

namespace Ostmann.QuadraticSieve
open MeasureTheory Set
open scoped SchwartzMap

theorem dualCorrelation_full_transform (W : 𝓢(ℝ, ℂ)) (hc : HasCompactSupport W)
    (hs : tsupport W ⊆ Ioi (0 : ℝ)) (M : ℝ) (hM : 0 < M) (Δ K N : ℕ)
    (hΔ0 : Δ ≠ 0) (hΔ : Odd Δ) (S : Finset ℕ) (a : ℕ → ℂ)
    (X₁ X₂ L : ℕ → ℕ → ℝ) (hS : S ⊆ oddSquarefreeUpTo N) (hS1 : ∀ n ∈ S, 1 < n) :
    dualCorrelation W M Δ S a =
      dualLeadingCorrelation M (∫ x : ℝ in Ioi 0, W (x^2)) K Δ S a +
        dualCorrelationZeroCorrection W M Δ K S a X₂ +
        dualCorrelationLargeCorrection W M Δ K S a X₂ +
        dualCorrelationFourierCorrection W M Δ K S a X₁ X₂ L +
        dualCorrelationRemainder W M Δ K S a X₁ X₂ L + dualCorrelationTail W M Δ K S a := by
  rw [dualCorrelation_eq W M hM Δ K N hΔ0 S a X₁ X₂ L hS hS1,
    dualCorrelationMain_eq_leading W hc hs M hM Δ K N hΔ S a X₁ X₂ L hS]

end Ostmann.QuadraticSieve

end OAI
