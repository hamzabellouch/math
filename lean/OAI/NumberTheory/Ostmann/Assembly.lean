import OAI.NumberTheory.Ostmann.FiniteFactor
import OAI.NumberTheory.Ostmann.Setup

namespace OAI

namespace Ostmann

theorem assemble_from_infinite_case (hinfinite : ∀ _ : Decomposition, False) :
    AsymptoticallyIndecomposable := by
  apply assemble_indecomposability
  · intro A B hfinite hA _
    exact finite_factor_impossible A B hfinite hA
  · intro A B hA hB h
    obtain ⟨N, hN⟩ := h
    exact hinfinite ⟨A, B, hA, hB, N, hN⟩

end Ostmann

end OAI
