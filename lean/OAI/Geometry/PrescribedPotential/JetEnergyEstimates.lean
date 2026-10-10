import Mathlib
import OAI.Geometry.PrescribedPotential.JetEnergyUniform

namespace OAI

/-! Jet Energy Estimates. -/

section

 

noncomputable section
open Set Filter Topology Finset Module
open scoped ContDiff
namespace HigherJet
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  {ι : Type*} [Fintype ι]

lemma energy_first_of_residual {U : Set E} (hU : IsOpen U) {u : E → F}
    (hu : ContDiffOn ℝ ∞ u U) (e : ι → E) {x : E} (hx : x ∈ U) (v : ι → E)
    {A R : ℝ} (hA : 1 ≤ A) (hR : 0 ≤ R)
    (hS : Real.sqrt (jetEnergy e 1 u x) ≤ A)
    (hN : ‖iteratedFDeriv ℝ 2 u x‖ ≤ A*Real.sqrt (familyDissipation v (jetFamily e 1 u) x))
    (hr : ∀ σ, ‖frameLaplace v (jetFamily e 1 u σ) x‖ ≤ R*(1+‖iteratedFDeriv ℝ 2 u x‖)) :
    familyDissipation v (jetFamily e 1 u) x -
      (2*(A+(Fintype.card (Fin 1 → ι)+1)*R*A)^2+(A+(Fintype.card (Fin 1 → ι)+1)*R*A)^4) ≤
      frameLaplace v (jetEnergy e 1 u) x := by
  apply BernsteinEstimate.first_energy_scaled (W := Real.sqrt (∑ σ, ‖frameLaplace v (jetFamily e 1 u σ) x‖^2)) (jetEnergy_nonneg _ _ _ _)
    (familyDissipation_nonneg _ _ _) hA (show 0 ≤ (Fintype.card (Fin 1 → ι)+1)*R by positivity) hS
  · exact (family_laplace_norm_bound (show 0 ≤ R*(1+‖iteratedFDeriv ℝ 2 u x‖) by positivity) hr).trans
      (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
        (add_le_add (le_refl 1) hN) hR) (show 0 ≤ (Fintype.card (Fin 1 → ι)+1 : ℝ) by positivity))
  · exact familyEnergy_laplace_lower hU (jetFamily_smoothOn hU hu e 1) hx v

lemma energy_second_of_residual {U : Set E} (hU : IsOpen U) {u : E → F}
    (hu : ContDiffOn ℝ ∞ u U) (e : ι → E) {x : E} (hx : x ∈ U) (v : ι → E)
    {A R : ℝ} (hA : 1 ≤ A) (hR : 0 ≤ R)
    (hN : ‖iteratedFDeriv ℝ 2 u x‖ ≤ A*Real.sqrt (jetEnergy e 2 u x))
    (hD : ‖iteratedFDeriv ℝ 3 u x‖ ≤ A*Real.sqrt (familyDissipation v (jetFamily e 2 u) x))
    (hr : ∀ σ, ‖frameLaplace v (jetFamily e 2 u σ) x‖ ≤
      R*(1+‖iteratedFDeriv ℝ 2 u x‖^2+‖iteratedFDeriv ℝ 3 u x‖)) :
    familyDissipation v (jetFamily e 2 u) x -
      (4*((Fintype.card (Fin 2 → ι)+1)*R*A^2)+2*((Fintype.card (Fin 2 → ι)+1)*R*A^2)^2)*
        (1+jetEnergy e 2 u x*Real.sqrt (jetEnergy e 2 u x)) ≤
      frameLaplace v (jetEnergy e 2 u) x := by
  apply BernsteinEstimate.cubic_energy_scaled (W := Real.sqrt (∑ σ, ‖frameLaplace v (jetFamily e 2 u σ) x‖^2)) (jetEnergy_nonneg _ _ _ _)
    (familyDissipation_nonneg _ _ _) hA (show 0 ≤ (Fintype.card (Fin 2 → ι)+1)*R by positivity)
  · have hn2 := pow_le_pow_left₀ (norm_nonneg _) hN 2
    rw [mul_pow,Real.sq_sqrt (jetEnergy_nonneg _ _ _ _)] at hn2
    exact (family_laplace_norm_bound (show 0 ≤ R*(1+‖iteratedFDeriv ℝ 2 u x‖^2+‖iteratedFDeriv ℝ 3 u x‖) by positivity) hr).trans
      (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
        (add_le_add (add_le_add (le_refl 1) hn2) hD) hR) (show 0 ≤ (Fintype.card (Fin 2 → ι)+1 : ℝ) by positivity))
  · exact familyEnergy_laplace_lower hU (jetFamily_smoothOn hU hu e 2) hx v

lemma energy_high_of_residual {U : Set E} (hU : IsOpen U) {u : E → F}
    (hu : ContDiffOn ℝ ∞ u U) (e : ι → E) (m : ℕ) {x : E} (hx : x ∈ U) (v : ι → E)
    {A R : ℝ} (hA : 1 ≤ A) (hR : 0 ≤ R)
    (hN : ‖iteratedFDeriv ℝ m u x‖ ≤ A*Real.sqrt (jetEnergy e m u x))
    (hD : ‖iteratedFDeriv ℝ (m+1) u x‖ ≤ A*Real.sqrt (familyDissipation v (jetFamily e m u) x))
    (hr : ∀ σ, ‖frameLaplace v (jetFamily e m u σ) x‖ ≤
      R*(1+‖iteratedFDeriv ℝ m u x‖+‖iteratedFDeriv ℝ (m+1) u x‖)) :
    familyDissipation v (jetFamily e m u) x -
      (4*((Fintype.card (Fin m → ι)+1)*R*A)+((Fintype.card (Fin m → ι)+1)*R*A)^2)*
        (1+jetEnergy e m u x) ≤ frameLaplace v (jetEnergy e m u) x := by
  apply BernsteinEstimate.linear_energy_scaled (W := Real.sqrt (∑ σ, ‖frameLaplace v (jetFamily e m u σ) x‖^2)) (jetEnergy_nonneg _ _ _ _)
    (familyDissipation_nonneg _ _ _) hA (show 0 ≤ (Fintype.card (Fin m → ι)+1)*R by positivity)
  · exact (family_laplace_norm_bound (show 0 ≤ R*(1+‖iteratedFDeriv ℝ m u x‖+‖iteratedFDeriv ℝ (m+1) u x‖) by positivity) hr).trans
      (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
        (add_le_add (add_le_add (le_refl 1) hN) hD) hR) (show 0 ≤ (Fintype.card (Fin m → ι)+1 : ℝ) by positivity))
  · exact familyEnergy_laplace_lower hU (jetFamily_smoothOn hU hu e m) hx v
end HigherJet

end
end

end OAI
