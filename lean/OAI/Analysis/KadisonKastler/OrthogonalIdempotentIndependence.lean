import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.Analysis.Complex.Basic

namespace OAI

/-! # Independence of nonzero orthogonal idempotents -/

namespace KadisonKastler

open scoped BigOperators

theorem linearIndependent_of_orthogonal_idempotents
    {A ι : Type*} [Ring A] [Algebra ℂ A] [Fintype ι] [DecidableEq ι]
    (p : ι → A) (hp : ∀ i, p i ≠ 0)
    (hmul : ∀ i j, p i * p j = if i = j then p i else 0) :
    LinearIndependent ℂ p := by
  apply Fintype.linearIndependent_iff.mpr
  intro c hc i
  have h := congrArg (fun a : A => a * p i) hc
  simp only [Finset.sum_mul, smul_mul_assoc, hmul, smul_ite, smul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, zero_mul] at h
  exact (smul_eq_zero.mp h).resolve_right (hp i)

end KadisonKastler

end OAI
