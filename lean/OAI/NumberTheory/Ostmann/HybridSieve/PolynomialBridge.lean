import OAI.NumberTheory.Ostmann.HybridSieve.OrdinateDefs
import OAI.NumberTheory.Ostmann.ZeroDensity.BetaDerivative

namespace OAI

open scoped Classical
namespace Ostmann.HybridSieve

noncomputable def realPartCoefficients (a : ℕ → ℂ) (σ : ℝ) (n : ℕ) : ℂ :=
  a n * ((n:ℝ)^(-σ):ℝ)

lemma physicalDyadicSum_eq_finiteCharacterPolynomial (N : ℕ) (a : ℕ → ℂ)
    {Q : ℕ} (i : PrimitiveFamily Q) (σ γ : ℝ) :
    physicalDyadicSum N (realPartCoefficients a σ) i γ =
      Ostmann.ZeroDensity.finiteCharacterPolynomial i.2.val a (Finset.Ioc N (2*N))
        ((σ:ℂ)+(γ:ℂ)*Complex.I) := by
  apply Finset.sum_congr rfl
  intro n hn
  have hnpos : 0 < n := lt_of_le_of_lt (Nat.zero_le N) (Finset.mem_Ioc.mp hn).1
  have hn0 : (n:ℂ) ≠ 0 := by exact_mod_cast hnpos.ne'
  have hre : (((n:ℝ)^(-σ):ℝ):ℂ) = (n:ℂ)^(-(σ:ℂ)) := by
    simpa using Complex.ofReal_cpow (Nat.cast_nonneg n) (-σ)
  have him : (n:ℂ)^(-((γ:ℂ)*Complex.I)) =
      Complex.exp (-Complex.I*(γ:ℂ)*(Real.log n:ℂ)) := by
    rw [Complex.cpow_def_of_ne_zero hn0, ← Complex.natCast_log]
    congr 1
    ring
  dsimp [realPartCoefficients, familyValue]
  rw [show -((σ:ℂ)+(γ:ℂ)*Complex.I) = (-(σ:ℂ))+(-((γ:ℂ)*Complex.I)) by ring,
    Complex.cpow_add _ _ hn0, ← hre, him]
  ring

lemma norm_realPartCoefficients_sq (a : ℕ → ℂ) (σ : ℝ) {n : ℕ} (_hn : 0 < n) :
    ‖realPartCoefficients a σ n‖^2 = ‖a n‖^2*(n:ℝ)^(-2*σ) := by
  rw [realPartCoefficients, norm_mul, mul_pow, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)]
  congr 1
  rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg n)]
  congr 1
  ring

end Ostmann.HybridSieve

end OAI
