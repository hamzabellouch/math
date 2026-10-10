import OAI.NumberTheory.Ostmann.QuadraticSieveGaussMellin
import OAI.NumberTheory.Ostmann.QuadraticSieveMellinSeparationScale

namespace OAI

namespace Ostmann.QuadraticSieve

noncomputable def sqrtCoefficients (a : ℕ → ℂ) (n : ℕ) : ℂ := a n*(Real.sqrt (n : ℝ) : ℂ)

theorem coefficientEnergy_sqrtCoefficients_le (S : Finset ℕ) (a : ℕ → ℂ)
    (N : ℕ) (hS : ∀ n ∈ S, n ≤ N) :
    coefficientEnergy S (sqrtCoefficients a) ≤ (N : ℝ)*coefficientEnergy S a := by
  unfold coefficientEnergy
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n hn
  rw [sqrtCoefficients,norm_mul,mul_pow,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _),Real.sq_sqrt (Nat.cast_nonneg n)]
  have h := mul_le_mul_of_nonneg_left (show (n : ℝ) ≤ N by exact_mod_cast hS n hn) (sq_nonneg ‖a n‖)
  simpa only [mul_comm] using h

noncomputable def rootGaussMellinKernel (a b : ℕ → ℂ) (c : ℤ) (d v n t : ℕ) : ℂ :=
  if Nat.Coprime n t ∧ d ∣ n*t then a n*b t*
    ((Real.sqrt ((n : ℝ)*t) : ℂ)*jacobiGaussRatio (n*t)*(jacobiSym (c*(v : ℤ)) (n*t) : ℂ)) else 0

theorem rootGaussMellinKernel_eq (a b : ℕ → ℂ) (c : ℤ) (d v n t : ℕ) :
    rootGaussMellinKernel a b c d v n t =
      gaussMellinKernel (sqrtCoefficients a) (sqrtCoefficients b) c d v n t := by
  unfold rootGaussMellinKernel gaussMellinKernel sqrtCoefficients
  by_cases h : Nat.Coprime n t ∧ d ∣ n*t
  · rw [ite_eq_left h,ite_eq_left h,Real.sqrt_mul (Nat.cast_nonneg n),Complex.ofReal_mul]
    ring
  · rw [ite_eq_right h,ite_eq_right h]

theorem mellinWeightedEnergy_sqrtCoefficients_le (S : Finset ℕ) (a : ℕ → ℂ)
    (N : ℕ) (σ : ℝ) (hσ : 0 ≤ σ) (hS : ∀ n ∈ S, 0 < n ∧ n ≤ N) :
    mellinWeightedEnergy S (sqrtCoefficients a) (fun n => Real.sqrt n) σ ≤
      (N : ℝ)*coefficientEnergy S a :=
  (mellinWeightedEnergy_sqrt_le S (sqrtCoefficients a) σ hσ (fun n hn => (hS n hn).1)).trans
    (coefficientEnergy_sqrtCoefficients_le S a N (fun n hn => (hS n hn).2))

end Ostmann.QuadraticSieve

end OAI
