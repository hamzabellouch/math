import OAI.NumberTheory.Ostmann.Preliminaries.CardinalKernelNorm

namespace OAI

/-! # The exact coefficient energy of the normalized squarefree array -/

namespace Ostmann

open scoped BigOperators

noncomputable def rootNormalizedCoefficient (F : ℕ → ℂ) (s : ℕ) : ℂ :=
  ((Real.sqrt (s : ℝ))⁻¹ : ℂ) * F s

theorem rootNormalizedCoefficient_norm_sq (F : ℕ → ℂ) (s : ℕ) :
    ‖rootNormalizedCoefficient F s‖ ^ 2 = (s : ℝ)⁻¹ * ‖F s‖ ^ 2 := by
  rw [rootNormalizedCoefficient, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, inv_pow,
    Real.sq_sqrt (Nat.cast_nonneg s)]

theorem rootNormalizedCoefficient_energy (S : Finset ℕ) (u : ℝ) (F : ℕ → ℂ) :
    (∑ s : S, u ^ s.val.primeFactors.card * ‖rootNormalizedCoefficient F s‖ ^ 2) =
      ∑ s ∈ S, (u ^ s.primeFactors.card / (s : ℝ)) * ‖F s‖ ^ 2 := by
  rw [show (∑ s : S, u ^ s.val.primeFactors.card * ‖rootNormalizedCoefficient F s‖ ^ 2) =
    ∑ s ∈ S, u ^ s.primeFactors.card * ‖rootNormalizedCoefficient F s‖ ^ 2 from
      Finset.sum_coe_sort S (fun s : ℕ => u ^ s.primeFactors.card * ‖rootNormalizedCoefficient F s‖ ^ 2)]
  apply Finset.sum_congr rfl
  intro s _
  rw [rootNormalizedCoefficient_norm_sq]
  ring

end Ostmann

end OAI
