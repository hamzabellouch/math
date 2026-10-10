import OAI.NumberTheory.Ostmann.Characters.OneSidedBounds

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate
namespace Ostmann.Characters
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

def oneSidedMean (μ : ι → ℝ) (ν : κ → ℝ) (U : ι → ℂ) (V : κ → ℂ)
    (F : ι → κ → ℂ) : ℂ :=
  ∑ n, (μ n : ℂ) * U n * ∑ q, (ν q : ℂ) * V q * F n q

theorem oneSided_cauchy_extension (μ b : ι → ℝ) (U G : ι → ℂ)
    (hμ : ∀ n, 0 ≤ μ n) (hmass : ∑ n, μ n ≤ 1)
    (hb : ∀ n, μ n ≤ b n) (hU : ∀ n, ‖U n‖ ≤ 1) :
    ‖∑ n, (μ n : ℂ) * U n * G n‖^2 ≤ ∑ n, b n * ‖G n‖^2 := by
  have hnorm : ‖∑ n, (μ n : ℂ) * U n * G n‖ ≤ ∑ n, μ n * ‖G n‖ := by
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro n hn
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hμ n)]
    calc
      _ ≤ μ n * 1 * ‖G n‖ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hU n) (hμ n)) (norm_nonneg _)
      _ = _ := by ring
  have hCS : (∑ n, μ n * ‖G n‖)^2 ≤ (∑ n, μ n) * (∑ n, μ n * ‖G n‖^2) := by
    apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
      (fun n _ => hμ n) (fun n _ => mul_nonneg (hμ n) (sq_nonneg _))
    intro n hn
    exact le_of_eq (by ring)
  calc
    _ ≤ (∑ n, μ n * ‖G n‖)^2 := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    _ ≤ (∑ n, μ n) * (∑ n, μ n * ‖G n‖^2) := hCS
    _ ≤ 1 * (∑ n, μ n * ‖G n‖^2) :=
      mul_le_mul_of_nonneg_right hmass (Finset.sum_nonneg (fun n _ => mul_nonneg (hμ n) (sq_nonneg _)))
    _ ≤ _ := by
      rw [one_mul]
      exact Finset.sum_le_sum (fun n _ => mul_le_mul_of_nonneg_right (hb n) (sq_nonneg _))

def oneSidedGram (b : ι → ℝ) (F : ι → κ → ℂ) (q q' : κ) : ℂ :=
  ∑ n, (b n : ℂ) * F n q * conj (F n q')

theorem norm_sq_eq_re_mul_conj (z : ℂ) : ‖z‖^2 = (z * conj z).re := by
  rw [Complex.mul_conj, Complex.ofReal_re, Complex.sq_norm]

theorem oneSided_energy_expansion (b : ι → ℝ) (a : κ → ℂ) (F : ι → κ → ℂ) :
    (∑ n, b n * ‖∑ q, a q * F n q‖^2) =
      ∑ q, ∑ q', (a q * conj (a q') * oneSidedGram b F q q').re := by
  simp only [norm_sq_eq_re_mul_conj, map_sum, Complex.re_sum, Finset.sum_mul, Finset.mul_sum, map_mul]
  simp only [oneSidedGram, Finset.mul_sum, Complex.re_sum]
  conv_rhs => rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q hq
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q' hq'
  apply Finset.sum_congr rfl
  intro n hn
  rw [← Complex.re_ofReal_mul]
  congr 1
  ring

end Ostmann.Characters

end

end OAI
