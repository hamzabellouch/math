import OAI.NumberTheory.Ostmann.Construction.ResidueBlockEnergy

namespace OAI

/-! # Tensoring finite kernel energy bounds without a dimension factor -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def tensorKernel {α β γ δ : Type*}
    (M : α → β → ℂ) (N : γ → δ → ℂ) (x : α × γ) (y : β × δ) : ℂ :=
  M x.1 y.1 * N x.2 y.2

/-- Slice first in one coordinate and then in the other. The two operator
bounds multiply; the cardinalities of the coordinate spaces never enter. -/
theorem tensorKernel_energy_le {α β γ δ : Type*}
    [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    (M : α → β → ℂ) (N : γ → δ → ℂ) (A B : ℝ)
    (hM : ∀ f : β → ℂ, (∑ x, ‖∑ y, M x y * f y‖ ^ 2) ≤ A ^ 2 * ∑ y, ‖f y‖ ^ 2)
    (hN : ∀ f : δ → ℂ, (∑ x, ‖∑ y, N x y * f y‖ ^ 2) ≤ B ^ 2 * ∑ y, ‖f y‖ ^ 2)
    (f : β × δ → ℂ) :
    (∑ x, ‖∑ y, tensorKernel M N x y * f y‖ ^ 2) ≤
      (A * B) ^ 2 * ∑ y, ‖f y‖ ^ 2 := by
  have he (x : α) (z : γ) : (∑ y, tensorKernel M N (x, z) y * f y) =
      ∑ y, M x y * ∑ w, N z w * f (y, w) := by
    rw [Fintype.sum_prod_type]
    simp only [tensorKernel, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y _
    apply Finset.sum_congr rfl
    intro w _
    ring
  rw [Fintype.sum_prod_type]
  simp_rw [he]
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑ z, A ^ 2 * ∑ y, ‖∑ w, N z w * f (y, w)‖ ^ 2 :=
      Finset.sum_le_sum fun z _ => hM (fun y => ∑ w, N z w * f (y, w))
    _ = A ^ 2 * ∑ y, ∑ z, ‖∑ w, N z w * f (y, w)‖ ^ 2 := by
      rw [← Finset.mul_sum, Finset.sum_comm]
    _ ≤ A ^ 2 * ∑ y, B ^ 2 * ∑ w, ‖f (y, w)‖ ^ 2 :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun y _ => hN (fun w => f (y, w))) (sq_nonneg _)
    _ = _ := by rw [← Finset.mul_sum, Fintype.sum_prod_type, mul_pow]; ring

end Ostmann

end OAI
