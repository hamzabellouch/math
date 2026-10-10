import OAI.NumberTheory.Ostmann.Arithmetic.MovingNormalizedSymmetrizedEnergy
import OAI.NumberTheory.Ostmann.Characters.MixedExternalPartition

namespace OAI

/-! # The full smooth cell for the original symmetrized coefficient -/

namespace Ostmann
open scoped Classical BigOperators

theorem movingTemplateMaskedSymmetrizedEnergy_full_cell_bound
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (outside : List ℕ) (μ : ℕ → P → ℝ)
    (childBound pivotBound V : ℕ → ℕ) (F : MovingSlotState P → ℤ → ℂ)
    (φ : ℝ → ℝ) (G : ℕ → ℝ) (n r m : ℕ)
    (ν : MovingRegularSlot n r m → P → ℝ) (active : MovingRegularSlot n r m → Bool)
    (greg : ∀ q : ℕ, ZMod q → ℂ) (Jleft Jright : ℝ) (diagonal : Bool)
    (H K center E : ℝ)
    (h : ∀ i j : Bool, ‖movingTemplateMaskedSymmetrizedEnergy P hP outside μ childBound pivotBound V F φ G
      n r m ν active greg Jleft Jright diagonal
      (if i then H else H - 1) ((if i then H else H - 1) + 1)
      (if j then K else K - 1) ((if j then K else K - 1) + 1) center‖ ≤ E) :
    ‖movingTemplateMaskedSymmetrizedEnergy P hP outside μ childBound pivotBound V F φ G
      n r m ν active greg Jleft Jright diagonal (H - 1) (H + 1) (K - 1) (K + 1) center‖ ≤ 4 * E := by
  exact mixedExternalAverage_full_cell_bound ν (V n) H K center E _ h

end Ostmann

end OAI
