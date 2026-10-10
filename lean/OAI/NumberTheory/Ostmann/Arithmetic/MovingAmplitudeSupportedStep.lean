import OAI.NumberTheory.Ostmann.Arithmetic.MovingAmplitudeSupportedTransfer
import OAI.NumberTheory.Ostmann.Arithmetic.MovingAmplitudeNext

namespace OAI

/-! # Consecutive original amplitudes with their supported product windows -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

/-- The next term is the actual doubled-prior amplitude. The transfer
inequality is derived rather than imposed as a recurrence hypothesis. -/
theorem movingTemplatePrimeAmplitude_step_on_support {σ : Type} [Fintype σ]
    (value : σ → ℕ) (hvalue : ∀ a, (value a).Prime)
    (outside : List ℕ) (μ : ℕ → σ → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (hV : Monotone V)
    (F : MovingSlotState σ → ℤ → ℂ) (hF : ∀ x, F x 0 = 0)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (n r m : ℕ)
    (Pg I : Finset ℕ) (hPg : ∀ p ∈ Pg, p.Prime) (hPI : Pg ⊆ I)
    (hI : ∀ p ∈ I, 0 < p) (hφ : ∀ x, 0 ≤ φ x)
    (hpos : 0 < smoothGiantMass Pg φ (G (n + 1)))
    (hμ : ∀ a, 0 ≤ μ n a) (hμmass : ∑ a, μ n a = 1)
    (ν : MovingRegularSlot n r m → σ → ℝ)
    (sets : ∀ q : ℕ, Finset (ZMod q))
    (hsets : ∀ a, (sets (value a)).Nonempty)
    (hcard : ∀ a, (sets (value a)).card < value a)
    (ggiant : ∀ q : ℕ, ZMod q → ℂ) (favorable : ℕ → Bool)
    (hgiant : ∀ q : Pg, ∀ x, ggiant q (-x) = conj (ggiant q x))
    (H : ℕ)
    (hH : ∀ (u : TreeLeafIndex n × Fin 4 → σ), (∏ i, μ n (u i)) ≠ 0 →
      ∀ (p : ℕ), p ∈ I →
      ∀ (q : Pg) (y : MovingRegularSlot n r m → σ) (s : transferFrequencyRange (V n)),
      movingTemplateCoefficient value outside μ childBound pivotBound V F φ G
        n (4 + r) m s.val (movingRestoreSample n r m u y) p q ≠ 0 →
        (q : ℕ) * (∏ i, value (y i)) ≤ H)
    (hscale : ∀ (u : TreeLeafIndex n × Fin 4 → σ), (∏ i, μ n (u i)) ≠ 0 → ∀ p ∈ I,
      2 * V n * H ≤ V (n + 1) * (p * ∏ i, value (u i)))
    (hlarge : ∀ (q : Pg) (y : MovingRegularSlot n r m → σ) ℓ,
      ℓ.Prime → ℓ ∣ (q : ℕ) * (∏ i, value (y i)) → V (n + 1) < ℓ)
    (hvg : ∀ q : Pg, V (n + 1) < (q : ℕ))
    (hφsupport : ∀ p : ℕ, 0 < p → φ (Real.log p - G (n + 1)) ≠ 0 → p ∈ I)
    (hchild : V n ≤ childBound (n + 1))
    (hgap : ∀ XR : Pg, ∀ right : MovingRegularSlot n r m → σ, (∏ i, ν i (right i)) ≠ 0 →
      2 * pivotBound (n + 1) * childBound (n + 1) < (XR : ℕ) * ∏ i, value (right i))
    (hcomp : ∀ u : TreeLeafIndex n × Fin 4 → σ, (∏ i, μ n (u i)) ≠ 0 →
      (∀ p ∈ I, p * (∏ i, value (u i)) ≤ pivotBound (n + 1)) ∧
      (∀ q, q.Prime → q ∣ ∏ i, value (u i) → childBound (n + 1) < q)) :
    let ρ := smoothGiantPrior Pg φ (G (n + 1))
    let greg := normalizedResidueFamily sets
    Real.exp (-smoothGiantLogNormalizer Pg φ (G (n + 1))) *
      ‖movingTemplatePrimeAmplitude value outside μ childBound pivotBound V F φ G n (4 + r) m
        Pg ρ (movingTemplateRestoredPrior n r m (μ n) ν) greg ggiant favorable‖ ^ 2 ≤
      movingAmplitudeDiagonal value outside μ childBound pivotBound V F φ G n r m Pg I
        ρ ν greg ggiant favorable +
      ‖movingTemplatePrimeAmplitude value outside μ childBound pivotBound V F φ G (n + 1) r m
        Pg ρ (movingTemplateDoubledPrior n r m ν) greg ggiant favorable‖ := by
  intro ρ greg
  have he := movingAmplitudeOffDiagonal_eq_next value hvalue outside μ childBound pivotBound V
    hV F hF φ G n r m Pg hPg ρ ν hvg I hI hφsupport hchild hgap
    (fun XR right _ => hlarge XR right) hcomp greg ggiant favorable
  rw [← he]
  exact movingTemplatePrimeAmplitude_transfer_on_support value hvalue outside μ childBound pivotBound V F
    φ G n r m Pg I hPg hPI hI hφ hpos hμ hμmass ν sets hsets hcard ggiant favorable
    hgiant H hH hscale hlarge

end Ostmann

end OAI
