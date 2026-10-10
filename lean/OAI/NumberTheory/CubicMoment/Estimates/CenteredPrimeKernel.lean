import OAI.NumberTheory.CubicMoment.Estimates.BilinearKernelIdentity
import OAI.NumberTheory.CubicMoment.Estimates.PrimeMellinTransfer

namespace OAI

/-! Identification of the decomposition kernel with the paper's prime
comparison, including the actual common-height Mellin polynomial. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma centeredGauss_primaryPrime {p : Eisenstein} (hp : primaryPrime p) :
    centeredGauss p = gaussAtPrime p-((cStar*norm p^(-1/6:ℝ):ℝ):ℂ) := by
  rw [centeredGauss,gauss_prime hp,idealMoebius_primaryPrime hp]
  push_cast
  ring

lemma theta_centeredGauss_primaryPrime (ℓ : ℤ) {p : Eisenstein} (hp : primaryPrime p) :
    theta ℓ p*centeredGauss p = primeComparisonCoefficient ℓ p := by
  rw [centeredGauss_primaryPrime hp]
  rfl

lemma prime_comparison_polynomial_eq_centered (ℓ : ℤ) (u X : ℝ) :
    (∑ p ∈ primeCutoff X, primeComparisonCoefficient ℓ p*normTwist u p) =
      ∑ p ∈ primeCutoff X, theta ℓ p*centeredGauss p*normTwist u p := by
  apply Finset.sum_congr rfl
  intro p hp
  rw [theta_centeredGauss_primaryPrime ℓ (mem_primeCutoff.mp hp).1]

lemma centeredGauss_vanishes {n : Eisenstein} (hn : primary n) (hs : ¬Squarefree n) :
    centeredGauss n = 0 := by
  have hg : gauss n = 0 := norm_eq_zero.mp (by rw [norm_gauss hn,ite_eq_right hs])
  rw [centeredGauss,hg,idealMoebius_sq_complex,ite_eq_right hs]
  simp

lemma norm_centeredGauss_le {n : Eisenstein} (hn : primary n) :
    ‖centeredGauss n‖ ≤ 1+cStar := by
  have hn1 : 1 ≤ norm n := one_le_norm (primary_ne_zero hn)
  have hp : norm n^(-1/6:ℝ) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hn1 (by norm_num)
  have hμ : ‖(idealMoebius n:ℂ)^2‖ ≤ 1 := by
    rw [norm_pow]
    simpa using pow_le_pow_left₀ (_root_.norm_nonneg _) (norm_idealMoebius_le_one n) 2
  have hcs := cStar_pos
  have hm : ‖(cStar:ℂ)*(idealMoebius n:ℂ)^2*((norm n^(-1/6:ℝ):ℝ):ℂ)‖ ≤ cStar := by
    rw [norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos cStar_pos,
      Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg (norm_nonneg n) _)]
    calc
      _ ≤ cStar*1*1 := by gcongr
      _ = _ := by ring
  exact (norm_sub_le _ _).trans ((add_le_add (norm_gauss_le_one hn) hm))

end CubicFirstMoment

end

end OAI
