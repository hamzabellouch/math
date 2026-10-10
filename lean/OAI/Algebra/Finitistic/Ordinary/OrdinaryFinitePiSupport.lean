import Mathlib.LinearAlgebra.Pi

namespace OAI
noncomputable section
namespace LittleFinitistic.FinitePiSupport
universe u v w
variable {R : Type u} [Ring R] {ι : Type v} [DecidableEq ι]
variable (V : ι → Type w) [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]
variable (i₀ : ι) (hV : ∀ i, i ≠ i₀ → Subsingleton (V i))

/-- A product with all but one coordinate zero is exactly its remaining coordinate. -/
def equivalence : (∀ i, V i) ≃ₗ[R] V i₀ :=
  LinearEquiv.ofBijective (LinearMap.proj i₀) ⟨by
    intro x y h
    funext i
    by_cases hi : i = i₀
    · subst i
      exact h
    · exact (hV i hi).elim _ _, by
    intro x
    refine ⟨fun i => if h : i = i₀ then h.symm ▸ x else 0, ?_⟩
    simp⟩

@[simp] theorem equivalence_apply (x : ∀ i, V i) : equivalence (R := R) V i₀ hV x = x i₀ := rfl
end LittleFinitistic.FinitePiSupport

end

end OAI
