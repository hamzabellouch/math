import OAI.NumberTheory.Ostmann.ZeroDensity.DensityMollifierProduct

namespace OAI

/-! # The actual divisor coefficients of the squared character L-function -/

namespace Ostmann

open scoped BigOperators Classical

 theorem density_character_self_convolution {q : ℕ} (χ : DirichletCharacter ℂ q) :
    LSeries.convolution (fun n : ℕ => χ (n : ZMod q)) (fun n : ℕ => χ (n : ZMod q)) =
      fun n : ℕ => χ (n : ZMod q) * (n.divisors.card : ℂ) := by
  funext n
  rw [LSeries.convolution_def]
  calc
    _ = ∑ _p ∈ n.divisorsAntidiagonal, χ (n : ZMod q) := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [← map_mul, ← Nat.cast_mul, (Nat.mem_divisorsAntidiagonal.mp hp).1]
    _ = _ := by
      rw [Nat.sum_divisorsAntidiagonal' (fun _ _ => χ (n : ZMod q))]
      simp only [Finset.sum_const, nsmul_eq_mul]
      ring

 theorem density_square_LSeries {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (s : ℂ) (hs : 1 < s.re) :
    LSeries (fun n : ℕ => χ (n : ZMod q) * (n.divisors.card : ℂ)) s =
      DirichletCharacter.LFunction χ s ^ 2 := by
  rw [← density_character_self_convolution χ,
    LSeries_convolution' (χ.LSeriesSummable_of_one_lt_re hs)
      (χ.LSeriesSummable_of_one_lt_re hs), ← DirichletCharacter.LFunction_eq_LSeries χ hs]
  ring

end Ostmann

end OAI
