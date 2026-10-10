import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint

namespace OAI

namespace Laughlin
open scoped InnerProductSpace

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [FiniteDimensional ℂ E] [FiniteDimensional ℂ F]

theorem complex_compression_positive_iff (W : E →ₗ[ℂ] F) (C : E →ₗ[ℂ] E) :
    (∀ x : E, 0 ≤ (⟪x, W.adjoint (W (C (W.adjoint (W x))))⟫_ℂ).re) ↔
      (∀ y : F, 0 ≤ (⟪y, W (C (W.adjoint y))⟫_ℂ).re) := by
  simp only [W.adjoint_inner_right, ← W.adjoint_inner_left]
  constructor
  · intro h y
    have hy : W.adjoint y ∈ (W.adjoint ∘ₗ W).range := by
      rw [W.range_adjoint_comp_self]
      exact ⟨y, rfl⟩
    obtain ⟨x, hx⟩ := hy
    change W.adjoint (W x) = W.adjoint y at hx
    simpa only [hx] using h x
  · intro h x
    exact h (W x)

end Laughlin

end OAI
