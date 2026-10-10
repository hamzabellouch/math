import OAI.NumberTheory.Ostmann.Quadratic.QuadraticSmallGcdError

namespace OAI

/-! # Uniform arbitrary power saving at every retained small gcd -/

namespace Ostmann

open scoped Classical BigOperators

theorem quadratic_small_gcd_error_arbitrary_power {δ : ℝ} (hδ : 0 < δ) (P : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ M R K D : ℕ, 1 ≤ M → 1 ≤ R → 0 < D → D < R →
      ∀ J : ℝ, ((M : ℝ) * R) ^ δ ≤ J →
      2 * (2 * (R : ℝ)) ^ 2 * J ≤ (M : ℝ) * ((K : ℝ) + 1) →
      (K : ℝ) ≤ ((M : ℝ) * R) ^ 3 →
      ∀ v : ℕ → ℂ, (∀ n ∈ oddSquarefreeRange (2 * R), n < R → v n = 0) →
      ‖quadraticGcdMomentError M R K D J v‖ ≤
        C / (((M : ℝ) * R) ^ P) * quadraticSieveEnergy (2 * R) v := by
  obtain ⟨A, hA⟩ := quadratic_polynomial_error_power_choice hδ P 6
  obtain ⟨C, hC, hc⟩ := quadratic_small_gcd_error A
  refine ⟨C, hC, ?_⟩
  intro M R K D hM hR hD hDR J hJ hcut hK v hsupp
  have hprod : 1 ≤ (M : ℝ) * R := one_le_mul_of_one_le_of_one_le
    (by exact_mod_cast hM) (by exact_mod_cast hR)
  have hJone : 1 ≤ J := (Real.one_le_rpow hprod hδ.le).trans hJ
  have hp := hA ((M : ℝ) * R) hprod
  have he : 0 ≤ quadraticSieveEnergy (2 * R) v := Finset.sum_nonneg fun _ _ => sq_nonneg _
  apply (hc M R K D hM hR hD hDR J hJone hcut hK v hsupp).trans
  calc
    _ ≤ C * (((M : ℝ) * R) ^ 6 / (((M : ℝ) * R) ^ δ) ^ A) *
        quadraticSieveEnergy (2 * R) v := by gcongr
    _ ≤ C * (1 / (((M : ℝ) * R) ^ P)) * quadraticSieveEnergy (2 * R) v := by gcongr
    _ = _ := by ring

/-- The large-gcd loss in the descent is only an arbitrary small power. -/
theorem quadratic_rough_gcd_descent_epsilon (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ M N K D₀ : ℕ, 0 < D₀ → ∀ T : ℝ, 0 ≤ T →
      QuadraticRoughBound M (N / D₀) K T → ∀ v : ℕ → ℂ,
      quadraticRoughEnergy M N K v ≤
        (∑ D ∈ (Finset.Icc 1 N).filter (fun D => D ≤ D₀),
          ‖quadraticRoughGcdMoment M N K D v‖) +
        C * (N : ℝ) ^ ε * T * quadraticSieveEnergy N v := by
  obtain ⟨C, hC, hc⟩ := quadratic_divisor_moment_bound ε hε
  refine ⟨C, hC, ?_⟩
  intro M N K D₀ hD₀ T hT h v
  apply (quadratic_rough_gcd_descent hD₀ hT h v).trans
  apply add_le_add le_rfl
  have hh := mul_le_mul_of_nonneg_left (hc N v) hT
  convert hh using 1; ring

end Ostmann

end OAI
