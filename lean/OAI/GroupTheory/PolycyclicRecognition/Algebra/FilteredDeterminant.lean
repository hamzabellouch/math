import Mathlib.LinearAlgebra.Eigenspace.Zero
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Basic.Real.Basic

namespace OAI

/-! # Determinant of an endomorphism that raises a finite filtration -/

noncomputable section
namespace PolycyclicRecognition

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

theorem nilpotent_of_raises_filtration (F : ℕ → Submodule ℝ V)
    (hF0 : F 0 = ⊤) {c : ℕ} (hFc : F c = ⊥)
    (N : V →ₗ[ℝ] V) (hN : ∀ k v, v ∈ F k → N v ∈ F (k + 1)) : IsNilpotent N := by
  have hp : ∀ k v, (N ^ k) v ∈ F k := by
    intro k
    induction k with
    | zero => intro v; simp [hF0]
    | succ k ih =>
      intro v
      rw [pow_succ', Module.End.mul_apply]
      exact hN k _ (ih v)
  refine ⟨c, LinearMap.ext fun v => ?_⟩
  have hv := hp c v
  simpa only [hFc, Submodule.mem_bot, LinearMap.zero_apply] using hv

theorem det_one_add_of_nilpotent [FiniteDimensional ℝ V]
    (N : V →ₗ[ℝ] V) (hN : IsNilpotent N) : LinearMap.det (1 + N) = 1 := by
  have hneg : IsNilpotent (-N) := hN.neg
  have he := LinearMap.eval_charpoly (-N) (1 : ℝ)
  rw [hneg.charpoly_eq_X_pow_finrank] at he
  simpa using he.symm

theorem det_eq_one_of_raises_filtration [FiniteDimensional ℝ V]
    (F : ℕ → Submodule ℝ V) (hF0 : F 0 = ⊤) {c : ℕ} (hFc : F c = ⊥)
    (A : V →ₗ[ℝ] V) (hA : ∀ k v, v ∈ F k → (A - 1) v ∈ F (k + 1)) :
    LinearMap.det A = 1 := by
  have hn := nilpotent_of_raises_filtration F hF0 hFc (A - 1) hA
  have hd := det_one_add_of_nilpotent (A - 1) hn
  simpa only [add_sub_cancel] using hd

end PolycyclicRecognition

end

end OAI
