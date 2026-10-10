import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousPolynomialLaplacian
import Mathlib.Tactic.Positivity

namespace OAI

/-! # Algebraic harmonic decomposition

A homogeneous polynomial is a homogeneous harmonic polynomial plus the
squared radius times a polynomial of two lower degrees. The preimage is
constructed by induction, using the positive radius-power coefficient.
-/

open MvPolynomial

namespace DefocusingNLS

theorem physicalPolynomialLaplacian_radius_preimage (p : PhysicalRealPolynomial)
    (n : ℕ) (hp : p.IsHomogeneous n) (j : ℕ) :
    ∃ q : PhysicalRealPolynomial, q.IsHomogeneous n ∧
      physicalPolynomialLaplacian (physicalRadiusPolynomial ^ (j + 1) * q) =
        physicalRadiusPolynomial ^ j * p := by
  induction n using Nat.strong_induction_on generalizing p j with
  | h n ih =>
    let c : ℝ := (4 * (j + 1) * (n + j + 6) : ℕ)
    have hc : c ≠ 0 := by dsimp only [c]; positivity
    by_cases hn : n ≤ 1
    · refine ⟨c⁻¹ • p, (homogeneousSubmodule (Fin 12) ℝ n).smul_mem _ hp, ?_⟩
      rw [mul_smul_comm, map_smul, physicalPolynomialLaplacian_radius_pow_mul p n j hp,
        physicalPolynomialLaplacian_low_degree p n hp hn, mul_zero, zero_add]
      rw [← Nat.cast_smul_eq_nsmul ℝ]
      change c⁻¹ • (c • (physicalRadiusPolynomial ^ j * p)) = _
      rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
    · obtain ⟨q₁, hq₁, hDq₁⟩ := ih (n - 2) (by omega)
        (physicalPolynomialLaplacian p) (physicalPolynomialLaplacian_homogeneous p n hp)
        (j + 1)
      have hRq₁ : (physicalRadiusPolynomial * q₁).IsHomogeneous n := by
        convert physicalRadiusPolynomial_homogeneous.mul hq₁ using 1
        omega
      let q := c⁻¹ • (p - physicalRadiusPolynomial * q₁)
      refine ⟨q, (homogeneousSubmodule (Fin 12) ℝ n).smul_mem _ (hp.sub hRq₁), ?_⟩
      have hqeq : physicalRadiusPolynomial ^ (j + 1) * q = c⁻¹ •
          (physicalRadiusPolynomial ^ (j + 1) * p -
            physicalRadiusPolynomial ^ (j + 2) * q₁) := by
        dsimp only [q]
        rw [mul_smul_comm, mul_sub]
        congr 2
        rw [show j + 2 = (j + 1) + 1 by omega, pow_succ]
        ring
      rw [hqeq, map_smul, map_sub, physicalPolynomialLaplacian_radius_pow_mul p n j hp,
        hDq₁]
      rw [← Nat.cast_smul_eq_nsmul ℝ]
      change c⁻¹ • (physicalRadiusPolynomial ^ (j + 1) * physicalPolynomialLaplacian p +
        c • (physicalRadiusPolynomial ^ j * p) -
        physicalRadiusPolynomial ^ (j + 1) * physicalPolynomialLaplacian p) = _
      rw [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hc, one_smul]

theorem physicalPolynomial_harmonic_decomposition (p : PhysicalRealPolynomial)
    (n : ℕ) (hp : p.IsHomogeneous n) :
    ∃ h q : PhysicalRealPolynomial, h.IsHomogeneous n ∧
      physicalPolynomialLaplacian h = 0 ∧ q.IsHomogeneous (n - 2) ∧
      p = h + physicalRadiusPolynomial * q := by
  by_cases hn : n ≤ 1
  · exact ⟨p, 0, hp, physicalPolynomialLaplacian_low_degree p n hp hn,
      isHomogeneous_zero (Fin 12) ℝ (n - 2), by simp⟩
  obtain ⟨q, hq, hDq⟩ := physicalPolynomialLaplacian_radius_preimage
    (physicalPolynomialLaplacian p) (n - 2) (physicalPolynomialLaplacian_homogeneous p n hp) 0
  simp only [zero_add, pow_one, pow_zero, one_mul] at hDq
  have hRq : (physicalRadiusPolynomial * q).IsHomogeneous n := by
    convert physicalRadiusPolynomial_homogeneous.mul hq using 1
    omega
  refine ⟨p - physicalRadiusPolynomial * q, q, hp.sub hRq, ?_, hq, ?_⟩
  · rw [map_sub, hDq, sub_self]
  · ring

end DefocusingNLS

end OAI
