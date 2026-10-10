import OAI.NumberTheory.Ostmann.HybridSieve.SamplingLog
import OAI.NumberTheory.Ostmann.ZeroDensity.CoefficientEnergy

namespace OAI

noncomputable section
open scoped BigOperators
open Set
namespace Ostmann.ZeroDensity

theorem exists_mollifier_varying_sampling_constant :
    ∃ C : ℝ, 0 < C ∧ ∀ {ι : Type} [Fintype ι],
      ∀ (U Q X N : ℕ) (σ H : ℝ) (character : ι → Ostmann.HybridSieve.PrimitiveFamily Q)
        (β γ : ι → ℝ),
      0 < U → 0 < Q → 1 ≤ H → 0 ≤ σ → σ ≤ 1 →
      (∀ j, β j ∈ Icc σ 1) → (∀ j, |γ j| ≤ H) →
      (∀ j k, j ≠ k → character j = character k → 1 ≤ |γ j - γ k|) →
      (∑ j, ‖finiteCharacterPolynomial (character j).2.val (mollifierCoefficient X N)
        (Finset.Ioc U (2 * U)) ((β j : ℂ) + (γ j : ℂ) * Complex.I)‖ ^ 2) ≤
        C * ((U : ℝ) + (Q : ℝ) ^ 2 * H) * (1 + Real.log Q) *
          (1 + Real.log (2 * U : ℝ)) ^ 7 * U * (U : ℝ) ^ (-2 * σ) := by
  obtain ⟨C, hC, hsampling⟩ :=
    Ostmann.HybridSieve.exists_unweighted_character_polynomial_sampling_log_constant
  refine ⟨6 * C, by positivity, ?_⟩
  intro ι _ U Q X N σ H character β γ hU hQ hH hσ hσ1 hβ hγ hsep
  have hU1 : 1 ≤ U := hU
  have hUR : (1 : ℝ) ≤ U := by exact_mod_cast hU
  have hQl : 0 ≤ Real.log Q := Real.log_nonneg (by exact_mod_cast hQ)
  have hl : 0 ≤ Real.log (2 * U : ℝ) := Real.log_nonneg (by linarith)
  let A : ℝ := C * ((U : ℝ) + (Q : ℝ) ^ 2 * H) * (1 + Real.log Q) *
    (1 + Real.log (2 * U : ℝ)) ^ 2
  let E : ℝ := 2 * U * (1 + Real.log (2 * U : ℝ)) ^ 3 * (U : ℝ) ^ (-2 * σ)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have horder (k : ℕ) (u : ℝ) (hu : u ∈ Icc σ 1) :
      (∑ j, ‖finiteCharacterPolynomial (character j).2.val
        (logPowerCoefficients k (mollifierCoefficient X N))
        (Finset.Ioc U (2 * U)) ((u : ℂ) + (γ j : ℂ) * Complex.I)‖ ^ 2) ≤
          A * ((Real.log (2 * U : ℝ)) ^ (2 * k) * E) := by
    have he := mollifier_logPower_dyadic_energy_le X N k (hσ.trans hu.1) hU1
    have hp : (U : ℝ) ^ (-2 * u) ≤ (U : ℝ) ^ (-2 * σ) :=
      Real.rpow_le_rpow_of_exponent_le hUR (by linarith [hu.1])
    have he' : (∑ n ∈ Finset.Ioc U (2 * U),
        ‖logPowerCoefficients k (mollifierCoefficient X N) n‖ ^ 2 *
          (n : ℝ) ^ (-2 * u)) ≤ (Real.log (2 * U : ℝ)) ^ (2 * k) * E := by
      apply he.trans
      dsimp [E]
      gcongr
    exact (hsampling U Q _ u H character γ hU hQ hH hγ hsep).trans
      (mul_le_mul_of_nonneg_left he' hA)
  let f : ι → ℝ → ℂ := fun j u =>
    finiteCharacterPolynomial (character j).2.val (mollifierCoefficient X N)
      (Finset.Ioc U (2 * U)) ((u : ℂ) + (γ j : ℂ) * Complex.I)
  let g : ι → ℝ → ℂ := fun j u =>
    finiteCharacterPolynomial (character j).2.val
      (logDerivativeCoefficients (mollifierCoefficient X N))
      (Finset.Ioc U (2 * U)) ((u : ℂ) + (γ j : ℂ) * Complex.I)
  have hpos : ∀ n ∈ Finset.Ioc U (2 * U), 0 < n := by
    intro n hn
    exact hU.trans (Finset.mem_Ioc.mp hn).1
  have hcoeff : logPowerCoefficients 1 (mollifierCoefficient X N) =
      logDerivativeCoefficients (mollifierCoefficient X N) := by
    funext n
    simp only [logPowerCoefficients, logDerivativeCoefficients, pow_one]
  have hv := sum_norm_sq_varying_parameter_le_of_uniform Finset.univ f g β hσ1
    (by linarith : 1 - σ ≤ 1) (mul_nonneg hA hE)
    (mul_nonneg hA (mul_nonneg (sq_nonneg (Real.log (2 * U : ℝ))) hE)) (by simpa using hβ)
    (fun j _ => finite_polynomial_beta_continuous _ _ _ hpos _)
    (fun j _ => finite_polynomial_beta_continuous _ _ _ hpos _)
    (fun j _ u => finite_polynomial_beta_derivative _ _ _ hpos _ u)
    (fun u hu => by simpa [f] using horder 0 u hu)
    (fun u hu => by simpa only [g, hcoeff, Nat.mul_one] using horder 1 u hu)
  change (∑ j, ‖f j (β j)‖ ^ 2) ≤ _
  calc
    _ ≤ 2 * (A * E) + A * ((Real.log (2 * U : ℝ)) ^ 2 * E) := hv
    _ ≤ 3 * (1 + Real.log (2 * U : ℝ)) ^ 2 * (A * E) := by
      have hf : 2 + (Real.log (2 * U : ℝ)) ^ 2 ≤
          3 * (1 + Real.log (2 * U : ℝ)) ^ 2 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_right hf (mul_nonneg hA hE)]
    _ = _ := by dsimp [A, E]; ring

end Ostmann.ZeroDensity

end

end OAI
