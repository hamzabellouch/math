import OAI.Probability.MatroidProphet.Main

namespace OAI

/-! Independent specification of source `lem:transfer` / `eq:rank-transfer`.
The fixed filter mask is arbitrary. Every remaining product coordinate and parity
is averaged, and the actual nominal rank statistic is zero when unlisted. -/

namespace MatroidProphet

open Finset MainAlgorithm

/-- Full sample-to-rank contract for the actual rounded greedy survivor groups. -/
def TransferClaim : Prop :=
  ∀ (n : ℕ) (M : Matroid (Fin n)) (hE : M.E = Set.univ)
    (w : Weights n), (∀ e, 0 ≤ w e) →
    ∀ (H : Finset (Fin n)) (i : ℤ),
    let s : Fin n → Option ℤ := fun e => roundedLevel weightBase (w e)
    let d : MainMasks n := ⟨H, ∅, ∅, ∅, false⟩
    let U := trueGroup M d s i
    let Y := (positiveGreedy M s \ H).filter (fun e => s e = some i)
    densityThreshold ≤ (U.card : ℝ) →
      ((((2 : ℝ)^16)⁻¹ * Y.card - ((2 : ℝ)^23)⁻¹ * U.card) / (2 : ℝ)^100) ≤
        mainMean d (fun d' => (trueZ M hE d' s i : ℝ))

end MatroidProphet

end OAI
