import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Basic.Real.Basic
import Lean.Elab.Tactic.Omega

namespace OAI

noncomputable section
namespace Zarankiewicz
open Module
open scoped BigOperators
variable {κ ρ : Type*} [Fintype κ] [Fintype ρ] [DecidableEq ρ]

theorem matrix_rank_eq_zero_iff
    {κ ρ : Type*} [Fintype κ] [Fintype ρ] [DecidableEq ρ]
    (A : Matrix κ ρ ℝ) : A.rank = 0 ↔ A = 0 := by
  constructor
  · intro ha
    have hf : A.mulVecLin = 0 :=
      LinearMap.range_eq_bot.mp (Submodule.finrank_eq_zero.mp ha)
    funext i j
    have hh := congrArg (fun f : (ρ → ℝ) →ₗ[ℝ] (κ → ℝ) => f (Pi.single j 1) i) hf
    simpa [Matrix.mulVec_single] using hh
  · rintro rfl
    exact Matrix.rank_zero

theorem matrix_rank_add_le
    {κ ρ : Type*} [Fintype κ] [Fintype ρ] [DecidableEq ρ]
    (A B : Matrix κ ρ ℝ) : (A+B).rank ≤ A.rank+B.rank := by
  change finrank ℝ (LinearMap.range (A+B).mulVecLin) ≤ _
  rw [Matrix.mulVecLin_add]
  exact (Submodule.finrank_mono (LinearMap.range_add_le A.mulVecLin B.mulVecLin)).trans
    (Submodule.finrank_add_le_finrank_add_finrank _ _)

theorem matrix_rank_smul_le
    {κ ρ : Type*} [Fintype κ] [Fintype ρ] [DecidableEq ρ]
    (c : ℝ) (A : Matrix κ ρ ℝ) : (c • A).rank ≤ A.rank := by
  by_cases hc : c = 0
  · simp [hc, Matrix.rank_zero]
  · rw [Matrix.rank_smul_of_mem_nonZeroDivisors A (mem_nonZeroDivisors_of_ne_zero hc)]

theorem matrix_rank_sum_le {α : Type*} (S : Finset α) (A : α → Matrix κ ρ ℝ) :
    (∑ a ∈ S, A a).rank ≤ ∑ a ∈ S, (A a).rank := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [Matrix.rank_zero]
  | @insert a S ha ih =>
    simp only [Finset.sum_insert ha]
    exact (matrix_rank_add_le _ _).trans (Nat.add_le_add_left ih _)

end Zarankiewicz

end

end OAI
