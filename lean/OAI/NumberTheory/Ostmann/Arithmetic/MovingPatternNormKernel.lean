import OAI.NumberTheory.Ostmann.Arithmetic.MovingPatternIntegrand
import OAI.NumberTheory.Ostmann.Characters.FourierWindowDecay

namespace OAI

/-! # The window decay for the literal prime-cell integrand -/

namespace Ostmann
open MeasureTheory
open scoped Classical BigOperators SchwartzMap

section
variable {B C : Type*} {N n m : ℕ}
    (e : Fin (N + 1) ≃ B ⊕ C) (tierB : B → ℕ) (tierC : C → ℕ)
    (t : Bool → FrequencyTree ℤ n) (small : Bool → TreeLeafTuple (List B) n)
    (slot : (TreeLeafIndex n × Fin m) ↪ B) (perm : Equiv.Perm (TreeLeafIndex n × Fin m))
    (pattern : Bool × MovingSampleIndex n → C)
    (hB : ∀ i, n ≤ tierB i) (htier : ∀ i, tierC (pattern i) = movingSampleTier i.2)
    (base : Fin (N + 1) → ℝ) (childBound pivotBound : ℕ → ℕ)
    (j₀ : TreeLeafIndex n × Fin m)
    (ψ : 𝓢(ℝ, ℂ)) (X lo hi V : ℝ) (hlo : 1 ≤ lo) (hhi : lo ≤ hi)
    (hfreq : ∀ b, ∀ s ∈ allFrequencyList n (t b), |(s : ℝ)| ≤ V)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (Bφ Dφ : ℝ) (hBφ : 0 ≤ Bφ) (hDφ : 0 ≤ Dφ)
    (hφ : ∀ x, |φ x| ≤ Bφ) (hlip : ∀ x y, |φ x - φ y| ≤ Dφ * |x - y|)
    (hout : ∀ x, 1 ≤ |x| → φ x = 0) (L U : ℝ)

theorem movingPatternBulkIntegrand_norm_window (z : (TreeLeafIndex n × Fin m) → ℝ) :
    ‖movingPatternBulkIntegrand e tierB tierC t small slot perm pattern hB htier base
      childBound pivotBound j₀ ψ X lo hi V hlo hhi hfreq φ G Bφ Dφ hBφ hDφ hφ hlip hout L U z‖ ≤
      ((SchwartzMap.seminorm ℝ 0 0 ψ / Real.sqrt lo) ^ (2 ^ n) * Bφ ^ (2 ^ n - 1)) ^ 2 :=
  realValueKernelPair_norm_window
    (bulkLogValues base (selectedBulkSet (movingPatternBulkEmbedding e slot))
      (bulkCoordinateInsert base (movingPatternBulkEmbedding e slot) z))
    childBound pivotBound (movingPatternFinBulkData e n m t small slot perm pattern)
    ψ X lo hi hlo hhi φ G Bφ hBφ hφ L U

end
end Ostmann

end OAI
