import OAI.MeasureTheory.Falconer.Slicing.GaussianRowStability

namespace OAI

/-! # The dimension of kernel slices in the controlled row chart -/

namespace Falconer
variable {d h : ℕ}

theorem adjoint_injective_of_lower (L : Space d →L[ℝ] Space h)
    {K : ℝ} (hL : ∀ a : Space h, ‖a‖ ≤ K*‖L.adjoint a‖) :
    Function.Injective L.adjoint := by
  apply LinearMap.ker_eq_bot.mp
  apply (LinearMap.ker_eq_bot').mpr
  intro a ha
  change L.adjoint a = 0 at ha
  have hn := hL a
  rw [ha,norm_zero,mul_zero] at hn
  exact norm_eq_zero.mp (le_antisymm hn (norm_nonneg _))

theorem kernel_finrank_of_adjoint_lower (L : Space d →L[ℝ] Space h)
    {K : ℝ} (hL : ∀ a : Space h, ‖a‖ ≤ K*‖L.adjoint a‖) :
    Module.finrank ℝ L.ker = d-h := by
  have hr := LinearMap.finrank_range_of_inj (adjoint_injective_of_lower L hL)
  have ha := LinearMap.finrank_range_adjoint L.toLinearMap
  rw [ContinuousLinearMap.adjoint_toLinearMap] at ha
  have hn := L.toLinearMap.finrank_range_add_finrank_ker
  simp only [finrank_euclideanSpace, Fintype.card_fin] at hr hn
  omega

theorem row_kernel_finrank (A : Fin h → Space d)
    (e : Space h →ₗᵢ[ℝ] Space d) {ε : ℝ}
    (hA : ∀ i, ‖A i-e (EuclideanSpace.basisFun (Fin h) ℝ i)‖ ≤ ε)
    (hε : (h:ℝ)*ε ≤ 1/2) :
    Module.finrank ℝ (gaussianRowMap A).ker = d-h :=
  kernel_finrank_of_adjoint_lower _ (row_adjoint_lower_near_isometry A e hA hε)

end Falconer

end OAI
