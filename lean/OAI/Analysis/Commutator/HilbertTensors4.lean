import Mathlib

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion
open scoped InnerProductSpace
open scoped TensorProduct

namespace Kadison

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem constant_right_orthonormal_coefficient_zero (v : ℕ → E)
    (hv : Orthonormal ℂ v) (x : E) (c : ℂ)
    (hc : ∀ n, inner ℂ x (v n) = c) : c = 0 := by
  have hs : Summable (fun n => ‖inner ℂ x (v n)‖ ^ 2) :=
    (hv.inner_products_summable x).congr (fun n => by rw [norm_inner_symm])
  simp_rw [hc] at hs
  have h0 : ‖c‖ ^ 2 = 0 := (summable_const_iff _).mp hs
  have hn : ‖c‖ = 0 := by nlinarith [norm_nonneg c]
  exact norm_eq_zero.mp hn

end Kadison
end

end OAI
