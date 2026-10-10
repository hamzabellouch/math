import Mathlib

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion
open scoped InnerProductSpace
open scoped TensorProduct

namespace Kadison

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

theorem constant_orthonormal_coefficient_zero (v : ℕ → E) (hv : Orthonormal ℂ v)
    (x : E) (c : ℂ) (hc : ∀ n, inner ℂ (v n) x = c) : c = 0 := by
  have hs := hv.inner_products_summable x
  simp_rw [hc] at hs
  have h0 : ‖c‖ ^ 2 = 0 := (summable_const_iff _).mp hs
  have hn : ‖c‖ = 0 := by nlinarith [norm_nonneg c]
  exact norm_eq_zero.mp hn

theorem constant_operator_coefficient_zero [CompleteSpace E] [CompleteSpace F]
    (T : E →L[ℂ] F) (v : ℕ → E) (hv : Orthonormal ℂ v)
    (x : F) (c : ℂ) (hc : ∀ n, inner ℂ (T (v n)) x = c) : c = 0 := by
  apply constant_orthonormal_coefficient_zero v hv (T.adjoint x) c
  intro n
  rw [ContinuousLinearMap.adjoint_inner_right, hc]

end Kadison
end

end OAI
