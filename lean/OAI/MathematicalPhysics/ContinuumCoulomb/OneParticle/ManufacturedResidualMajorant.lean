import OAI.MathematicalPhysics.ContinuumCoulomb.Programs.PolynomialResidualBudget

namespace OAI

/-! A four-term majorant for the actual manufactured differential residual.
The denominator powers are the ones used by the fixed physical schedule. -/

noncomputable section
open scoped BigOperators
namespace ContinuumCoulomb

theorem manufacturedResidual_four_power_majorant {freq : ℝ} (hf : 0 < freq)
    {rho : ℝ} (hrho : 0 ≤ rho) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ R L H S D a d δ M : ℝ,
      2 ≤ R → 1 ≤ L → R^50 ≤ H → H ≤ 2*R^50 → R^5 ≤ S → S ≤ 2*R^5 →
      0 < a → 0 ≤ d → 0 ≤ δ → δ ≤ 1 → δ ≤ d*M/(a*R^30) →
      Real.exp (-(19/10:ℝ)*D) ≤ (R^40)⁻¹ →
      ∀ (m : ℕ) (u : Fin m → PlanarPosition), (m:ℝ) ≤ M → (∀ j, ‖u j‖ ≤ L) →
      4*(m:ℝ)^2*(∑ j, manufacturedOrbitalSquaredError rho H S freq δ D (R^5) u j) ≤
        12*(PlanarSobolev.wellBound*planarWellMatrixConstant)*M^5/R^40+
        768*C*M^3*L^72/R^70+
        (12*PlanarSobolev.wellBound^2*d^2/a^2)*M^7/R^60+
        12288*PlanarSobolev.wellBound^2*C*M^5*L^8/R^40 := by
  obtain ⟨C,hC,hbound⟩ := manufacturedResidual_polynomial_geometry hf hrho
  refine ⟨C,hC,fun R L H S D a d δ M hR hL hHlo hHhi hSlo hShi ha hd hδ hδ1 hδa he m u hm hu => ?_⟩
  have hR0 : 0 < R := by linarith
  have hM : 0 ≤ M := (Nat.cast_nonneg m).trans hm
  have hW := PlanarSobolev.wellBound_nonnegative
  have hP := planarWellMatrixConstant_nonnegative
  have hr5 : 2 ≤ R^5 := hR.trans (le_self_pow₀ (by linarith) (by decide))
  have hb := hbound (R^5) L H S δ D hr5 hL
    (by simpa only [← pow_mul] using hHlo) (by simpa only [← pow_mul] using hHhi)
    hSlo hShi m u hu
  have h1 : (m:ℝ)^2*(PlanarSobolev.wellBound*planarWellMatrixConstant)*
      Real.exp (-(19/10:ℝ)*D) ≤ M^2*(PlanarSobolev.wellBound*planarWellMatrixConstant)/R^40 := by
    calc
      _ ≤ M^2*(PlanarSobolev.wellBound*planarWellMatrixConstant)*(R^40)⁻¹ := by gcongr
      _ = _ := by rw [div_eq_mul_inv]
  have h3 : ((m:ℝ)*δ*PlanarSobolev.wellBound)^2 ≤
      (M*(d*M/(a*R^30))*PlanarSobolev.wellBound)^2 := by gcongr
  have h4 : 256*((m:ℝ)*(δ+1)*PlanarSobolev.wellBound)^2*C*L^8/(R^5)^8 ≤
      1024*M^2*PlanarSobolev.wellBound^2*C*L^8/R^40 := by
    calc
      _ ≤ 256*(M*2*PlanarSobolev.wellBound)^2*C*L^8/(R^5)^8 := by gcongr; linarith
      _ = _ := by rw [← pow_mul]; ring
  have h2 : 64*C*L^72/(R^5)^14 = 64*C*L^72/R^70 := by rw [← pow_mul]
  have hp := add_le_add (add_le_add (add_le_add h1 (le_of_eq h2)) h3) h4
  have hscaled := mul_le_mul_of_nonneg_left hb (show 0 ≤ 4*(m:ℝ)^2 by positivity)
  calc
    _ ≤ 12*(m:ℝ)^3*((m:ℝ)^2*(PlanarSobolev.wellBound*planarWellMatrixConstant)*
        Real.exp (-(19/10:ℝ)*D)+64*C*L^72/(R^5)^14+
        ((m:ℝ)*δ*PlanarSobolev.wellBound)^2+
        256*((m:ℝ)*(δ+1)*PlanarSobolev.wellBound)^2*C*L^8/(R^5)^8) := by
      convert hscaled using 1
      ring
    _ ≤ 12*M^3*(M^2*(PlanarSobolev.wellBound*planarWellMatrixConstant)/R^40+
        64*C*L^72/R^70+(M*(d*M/(a*R^30))*PlanarSobolev.wellBound)^2+
        1024*M^2*PlanarSobolev.wellBound^2*C*L^8/R^40) := by
      exact mul_le_mul (by gcongr) hp (by positivity) (by positivity)
    _ = _ := by
      field_simp [ne_of_gt ha,ne_of_gt hR0]
      ring

end ContinuumCoulomb

end

end OAI
