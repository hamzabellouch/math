import OAI.NumberTheory.Ostmann.Quadratic.QuadraticSmallGcdPowerSaving
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticGcdMainGrowth

namespace OAI

/-! # The small-gcd moment with only its literal correction sum left -/

namespace Ostmann

open scoped Classical BigOperators

theorem quadratic_small_gcd_comparison {ξ δ ε : ℝ}
    (h : QuadraticSieveGrowth ξ) (hδ : 0 < δ) (hε : 0 < ε) (P : ℕ) :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧
      ∀ M R K D : ℕ, 1 ≤ M → 1 ≤ R → Squarefree D → Odd D → D < R → 0 < K →
      ∀ J : ℝ, ((M : ℝ) * R) ^ δ ≤ J →
      2 * (2 * (R : ℝ)) ^ 2 * J ≤ (M : ℝ) * ((K : ℝ) + 1) →
      (K : ℝ) ≤ ((M : ℝ) * R) ^ 3 →
      ∀ v : ℕ → ℂ, (∀ n ∈ oddSquarefreeRange (2 * R), n < R → v n = 0) →
      ‖quadraticRoughGcdMoment M (2 * R) K D v‖ ≤
        (C₁ * (((K * D ^ 2 : ℕ) : ℝ) * (2 * R)) ^ (2 * ε) * (D : ℝ) ^ ε *
          (Real.sqrt M / Real.sqrt K) * (((K * D ^ 2 : ℕ) : ℝ) ^ ξ + 2 * R) +
          C₂ / (((M : ℝ) * R) ^ P)) * quadraticSieveEnergy (2 * R) v +
          ‖quadraticGcdMomentCorrections M R K D J v‖ := by
  obtain ⟨C₁, hC₁, hc₁⟩ := quadratic_gcd_main_growth h hε
  obtain ⟨C₂, hC₂, hc₂⟩ := quadratic_small_gcd_error_arbitrary_power hδ P
  refine ⟨C₁, C₂, hC₁, hC₂, ?_⟩
  intro M R K D hM hR hD ho hDR hK J hJ hcut hKB v hsupp
  have hm := hc₁ M (2 * R) D K (by omega) (by omega) hD ho hK v
  have he := hc₂ M R K D hM hR (Nat.pos_of_ne_zero hD.ne_zero) hDR J hJ hcut hKB v hsupp
  have hn := norm_add_le
    ((quadraticTransformedFirstMain M (2 * R) D K quadraticSieveWeight v -
      quadraticSmallTransformedMain M (2 * R) D K quadraticSieveWeight v) +
      quadraticGcdMomentCorrections M R K D J v) (quadraticGcdMomentError M R K D J v)
  have hn₂ := norm_add_le
    (quadraticTransformedFirstMain M (2 * R) D K quadraticSieveWeight v -
      quadraticSmallTransformedMain M (2 * R) D K quadraticSieveWeight v)
    (quadraticGcdMomentCorrections M R K D J v)
  rw [quadratic_small_gcd_moment_decomposition (by omega) R K D J v]
  simp only [Nat.cast_mul, Nat.cast_ofNat] at hm ⊢
  nlinarith

end Ostmann

end OAI
