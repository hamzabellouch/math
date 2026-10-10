import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumHistoryEnumeration

namespace OAI

/-! Exact transport of finite quadratic forms and masses under a basis equivalence. -/

noncomputable section
namespace ContinuumCoulomb
open Matrix
open scoped BigOperators Classical

theorem qmaQuadratic_reindex_equiv {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (M : Matrix β β ℂ) (u : α → ℂ) :
    qmaQuadratic (M.submatrix e e) u = qmaQuadratic M (u ∘ e.symm) := by
  have hm := Matrix.submatrix_mulVec_equiv M u e e
  unfold qmaQuadratic
  rw [hm]
  have he := e.sum_comp (fun j => star (u (e.symm j))*M.mulVec (u ∘ e.symm) j)
  simp only [Equiv.symm_apply_apply] at he
  exact congrArg Complex.re he

theorem qmaMass_reindex {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (u : α → ℂ) :
    (∑ i, Complex.normSq (u (e.symm i))) = ∑ i, Complex.normSq (u i) :=
  e.symm.sum_comp (fun i => Complex.normSq (u i))

end ContinuumCoulomb

end

end OAI
