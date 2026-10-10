import Mathlib.Basic.Real.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

namespace OAI

namespace Yau.Analysis
noncomputable section

theorem subspace_nonzero_linear_constraints {S : Type*} [AddCommGroup S] [Module ℝ S]
    {N : ℕ} (V : Submodule ℝ S) [FiniteDimensional ℝ V]
    (hV : N < Module.finrank ℝ V) (ell : Fin N → S →ₗ[ℝ] ℝ) :
    ∃ x : S, x ∈ V ∧ x ≠ 0 ∧ ∀ i, ell i x = 0 := by
  let L : V →ₗ[ℝ] (Fin N → ℝ) := LinearMap.pi (fun i ↦ (ell i).comp V.subtype)
  have hk : LinearMap.ker L ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt (by simpa using hV)
  obtain ⟨x,hx,hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hk
  exact ⟨x,x.property,fun h ↦ hx0 (Subtype.ext h),fun i ↦ congrFun (LinearMap.mem_ker.mp hx) i⟩

end
end Yau.Analysis

end OAI
