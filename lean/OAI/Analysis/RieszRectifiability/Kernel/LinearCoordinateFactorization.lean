import Mathlib

namespace OAI

namespace RieszRectifiability

noncomputable section

theorem linear_functional_finite_coordinate_representation
    {E ι : Type*} [AddCommGroup E] [Module ℂ E] [Fintype ι]
    (J : E →ₗ[ℂ] (ι → ℂ)) (T : E →ₗ[ℂ] ℂ)
    (hker : ∀ x, J x = 0 → T x = 0) :
    ∃ c : ι → ℂ, ∀ x, T x = ∑ i, c i * J x i := by
  classical
  have hk : LinearMap.ker J ≤ LinearMap.ker T := fun x hx => hker x hx
  let qT : (E ⧸ LinearMap.ker J) →ₗ[ℂ] ℂ := (LinearMap.ker J).liftQ T hk
  let a : LinearMap.range J →ₗ[ℂ] ℂ := qT.comp J.quotKerEquivRange.symm.toLinearMap
  obtain ⟨A, hA⟩ := a.exists_extend
  have hfactor : ∀ x, A (J x) = T x := by
    intro x
    calc
      A (J x) = a ⟨J x, ⟨x, rfl⟩⟩ := LinearMap.congr_fun hA ⟨J x, ⟨x, rfl⟩⟩
      _ = T x := by
        exact congrArg qT (J.quotKerEquivRange_symm_apply_image x ⟨x, rfl⟩)
  refine ⟨fun i => A (Pi.single i 1), fun x => ?_⟩
  rw [← hfactor x]
  have hx : J x = ∑ i, (J x i) • (Pi.single i (1 : ℂ) : ι → ℂ) := by
    ext i
    simp [Pi.single_apply]
  conv_lhs => rw [hx, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul, smul_eq_mul, mul_comm]

end

end RieszRectifiability

end OAI
