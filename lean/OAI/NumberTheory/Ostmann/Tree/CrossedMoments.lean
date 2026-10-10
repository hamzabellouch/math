import Mathlib

namespace OAI

namespace Ostmann.FiniteField
noncomputable section
open scoped BigOperators
variable {C A : Type*} [CommGroup C] [Fintype C] [Fintype A]

theorem crossed_moment_bound (F H : C → C → A → ℝ) (ν : C) (e : A ≃ A) :
    2*(∑ χ : C,∑ ψ : C,∑ a : A, F χ (ν*ψ⁻¹) a*H ψ (ν⁻¹*χ⁻¹) (e a)) ≤
      (∑ χ : C,∑ α : C,∑ a : A,F χ α a^2)+
      (∑ ψ : C,∑ β : C,∑ a : A,H ψ β a^2) := by
  have hL (χ : C) : (∑ ψ : C,∑ a : A,F χ (ν*ψ⁻¹) a^2)=
      ∑ α : C,∑ a : A,F χ α a^2 := by
    exact ((Equiv.mulLeft ν).bijective.comp inv_involutive.bijective).sum_comp
      (fun α => ∑ a : A,F χ α a^2)
  have hR (ψ : C) : (∑ χ : C,∑ a : A,H ψ (ν⁻¹*χ⁻¹) (e a)^2)=
      ∑ β : C,∑ a : A,H ψ β a^2 := by
    have he (β : C) : (∑ a : A,H ψ β (e a)^2)=∑ a : A,H ψ β a^2 := e.sum_comp (fun a => H ψ β a^2)
    simp_rw [he]
    exact ((Equiv.mulLeft ν⁻¹).bijective.comp inv_involutive.bijective).sum_comp
      (fun β => ∑ a : A,H ψ β a^2)
  calc
    _ = ∑ χ : C,∑ ψ : C,∑ a : A,2*(F χ (ν*ψ⁻¹) a*H ψ (ν⁻¹*χ⁻¹) (e a)) := by
      simp only [Finset.mul_sum]
    _ ≤ ∑ χ : C,∑ ψ : C,∑ a : A,
        (F χ (ν*ψ⁻¹) a^2+H ψ (ν⁻¹*χ⁻¹) (e a)^2) := by
      apply Finset.sum_le_sum
      intro χ _
      apply Finset.sum_le_sum
      intro ψ _
      apply Finset.sum_le_sum
      intro a _
      nlinarith only [sq_nonneg (F χ (ν*ψ⁻¹) a-H ψ (ν⁻¹*χ⁻¹) (e a))]
    _ = _ := by
      simp only [Finset.sum_add_distrib]
      congr 1
      · simp_rw [hL]
      · rw [Finset.sum_comm]
        simp_rw [hR]

end
end Ostmann.FiniteField

end OAI
