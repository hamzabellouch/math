import OAI.Combinatorics.Progressions.Polynomial.PolynomialResidueDescentSize

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem exists_uniform_residue_descent_parameters (A B C : ℕ) :
    ∃ K : ℕ, 2 ≤ K ∧ ∀ p : ℝ, 0 ≤ p → ∀ Δ : ℝ,
      0 < Δ → Δ ≤ 1 → Δ⁻¹ ≤ Real.exp p →
      ∃ rho q ε δ : ℝ,
        p + 16 ≤ q ∧ verticalDecompositionBudget (p + 16) ≤ q ∧ q ≤ (p + 2) ^ K ∧
        0 < rho ∧ rho⁻¹ ≤ Real.exp (p + 16) ∧
        0 < ε ∧ ε < 1 / 2 ∧ 0 < δ ∧ δ ≤ 1 ∧
        ε⁻¹ ≤ Real.exp ((p + 2) ^ K) ∧ δ⁻¹ ≤ Real.exp ((p + 2) ^ K) ∧
        2 * (2 * rho + Real.exp (verticalDecompositionBudget (p + 16) - q)) ≤ Δ / 2 ∧
        8 * ε + 2 * (Real.exp (((p + 16) + 2) ^ C) * δ) = Δ / 4 ∧
        ∀ {σ : Type*} [Fintype σ] (N : σ → ℕ) (M P : ℕ) (J : σ → ℕ),
          (M : ℝ) ≤ Real.exp ((p + 2) ^ A) → (P : ℝ) ≤ Real.exp ((p + 2) ^ A) →
          (∀ i, (J i : ℝ) ≤ Real.exp ((p + 2) ^ A)) →
          (Fintype.card σ : ℝ) ≤ Real.exp ((p + 2) ^ A) →
          (∀ i, Real.exp ((p + 2) ^ K) ≤ (N i : ℝ)) →
          (∀ i, ((M * J i : ℕ) : ℝ) * (Real.exp ((q + B) ^ B) + 1) ≤ (N i : ℝ)) ∧
          (∀ i, 8 ≤ δ * (N i : ℝ)) ∧
          (∑ i, ((Nat.lcm M (M * P) * J i : ℕ) : ℝ) / (N i : ℝ)) ≤ δ * ε / 8 := by
  obtain ⟨D, _, hprecision⟩ := exists_residue_event_descent_precision C
  let R := max A D
  obtain ⟨K₀, hK₀, hsize⟩ := exists_polynomial_residue_descent_size R B
  let K := max R K₀
  refine ⟨K, hK₀.trans (le_max_right _ _), ?_⟩
  intro p hp Δ hΔ hΔone hΔinv
  obtain ⟨rho, q, ε, δ, hpq, hfreq, hq, hrho, hrhop, hε, hεhalf, hδ, hδone,
    hεbound, hδbound, hprojection, hfreezing⟩ := hprecision p hp Δ hΔ hΔone hΔinv
  have hpbase : 1 ≤ p + 2 := by linarith
  have hAR : (p + 2) ^ A ≤ (p + 2) ^ R := pow_le_pow_right₀ hpbase (le_max_left _ _)
  have hDR : (p + 2) ^ D ≤ (p + 2) ^ R := pow_le_pow_right₀ hpbase (le_max_right _ _)
  have hRK : (p + 2) ^ R ≤ (p + 2) ^ K := pow_le_pow_right₀ hpbase (le_max_left _ _)
  have hK₀K : (p + 2) ^ K₀ ≤ (p + 2) ^ K := pow_le_pow_right₀ hpbase (le_max_right _ _)
  have hDK : Real.exp ((p + 2) ^ D) ≤ Real.exp ((p + 2) ^ K) :=
    Real.exp_le_exp.mpr (hDR.trans hRK)
  refine ⟨rho, q, ε, δ, hpq, hfreq, hq.trans (hDR.trans hRK), hrho, hrhop,
    hε, hεhalf, hδ, hδone, hεbound.trans hDK, hδbound.trans hDK, hprojection, hfreezing, ?_⟩
  intro σ _ N M P J hM hP hJ hcard hN
  have hExpAR := Real.exp_le_exp.mpr hAR
  have hExpDR := Real.exp_le_exp.mpr hDR
  exact hsize p q hp (by linarith) (hq.trans hDR) N M P J ε δ
    (hM.trans hExpAR) (hP.trans hExpAR) (fun i => (hJ i).trans hExpAR)
    (hcard.trans hExpAR) hε hδ (hεbound.trans hExpDR) (hδbound.trans hExpDR)
    (fun i => (Real.exp_le_exp.mpr hK₀K).trans (hN i))

end Erdos3

end

end OAI
