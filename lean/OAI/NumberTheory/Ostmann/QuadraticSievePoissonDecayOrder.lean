import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace OAI

namespace Ostmann.QuadraticSieve

theorem exists_poisson_decay_order (η p : ℝ) (hη : 0 < η) :
    ∃ A : ℕ, ∀ P : ℝ, 1 ≤ P → P^p/(P^η)^A ≤ 1 := by
  obtain ⟨A,hA⟩ := exists_nat_gt (p/η)
  refine ⟨A,?_⟩
  intro P hP
  have hPp : 0 < P := by linarith
  have hexp : p ≤ η*A := by
    have h := (div_lt_iff₀ hη).mp hA
    nlinarith
  apply (div_le_one (by positivity : 0 < (P^η)^A)).mpr
  rw [←Real.rpow_mul_natCast hPp.le]
  exact Real.rpow_le_rpow_of_exponent_le hP hexp

theorem poisson_decay_absorbs_polynomial (η p : ℝ) (hη : 0 < η) :
    ∃ A : ℕ, ∀ P F : ℝ, 1 ≤ P → F ≤ P^p → F/(P^η)^A ≤ 1 := by
  obtain ⟨A,hA⟩ := exists_poisson_decay_order η p hη
  refine ⟨A,?_⟩
  intro P F hP hF
  have hPp : 0 < P := by linarith
  exact (div_le_div_of_nonneg_right hF (by positivity)).trans (hA P hP)

end Ostmann.QuadraticSieve

end OAI
