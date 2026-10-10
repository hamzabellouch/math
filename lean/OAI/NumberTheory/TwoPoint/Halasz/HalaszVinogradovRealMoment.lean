import OAI.NumberTheory.TwoPoint.Halasz.HalaszVinogradovMoment
import OAI.NumberTheory.TwoPoint.Halasz.HalaszVinogradovFibers

namespace OAI

/-! Real nonnegative moments, in the form used by the mean-value
inequalities in the complete-system iteration. -/
namespace TwoPointCorrelations

open Finset MeasureTheory
open scoped ComplexConjugate

lemma halasz_vinogradov_character_norm {k : ℕ} (m : Fin k → ℤ)
    (α : Fin k → AddCircle (1:ℝ)) : ‖halaszVinogradovCharacter m α‖=1 := by
  simp [halaszVinogradovCharacter,norm_prod,fourier_apply]

lemma halasz_vinogradov_polynomial_norm (k N : ℕ)
    (α : Fin k → AddCircle (1:ℝ)) : ‖halaszVinogradovPolynomial k N α‖ ≤ N := by
  unfold halaszVinogradovPolynomial
  calc
    _ ≤ ∑ n : Fin N, ‖halaszVinogradovCharacter
        (fun j => (((n.val+1)^(j.val+1):ℕ):ℤ)) α‖ := norm_sum_le _ _
    _ = _ := by simp only [halasz_vinogradov_character_norm,sum_const,card_univ,
      Fintype.card_fin,nsmul_eq_mul,mul_one]

theorem halasz_vinogradov_real_moment (s k N : ℕ) :
    (∫ α, ‖halaszVinogradovPolynomial k N α‖^(2*s) ∂halaszVinogradovHaar k) =
      (halaszVinogradovCount s k N:ℝ) := by
  have hp (α : Fin k → AddCircle (1:ℝ)) :
      ((‖halaszVinogradovPolynomial k N α‖^(2*s):ℝ):ℂ) =
      (halaszVinogradovPolynomial k N α)^s *
        conj ((halaszVinogradovPolynomial k N α)^s) := by
    simpa only [norm_pow,← Complex.ofReal_pow,← pow_mul,Nat.mul_comm] using
      (Complex.mul_conj' ((halaszVinogradovPolynomial k N α)^s)).symm
  have hc : Complex.ofReal (∫ α, ‖halaszVinogradovPolynomial k N α‖^(2*s)
      ∂halaszVinogradovHaar k) = (halaszVinogradovCount s k N:ℂ) := by
    rw [← integral_complex_ofReal]
    simp_rw [hp]
    exact halasz_vinogradov_moment s k N
  exact_mod_cast hc

theorem halasz_vinogradov_diagonal_moment {s k : ℕ} (hsk : s≤k) (N : ℕ) :
    (∫ α, ‖halaszVinogradovPolynomial k N α‖^(2*s) ∂halaszVinogradovHaar k) ≤
      (N:ℝ)^s*s.factorial := by
  rw [halasz_vinogradov_real_moment]
  exact_mod_cast halasz_vinogradov_diagonal_bound (N := N) hsk

theorem halasz_vinogradov_initial_moment (k r N : ℕ) :
    (∫ α, ‖halaszVinogradovPolynomial k N α‖^(2*(k+r)) ∂halaszVinogradovHaar k) ≤
      (N:ℝ)^(k+2*r)*k.factorial := by
  rw [halasz_vinogradov_real_moment]
  exact_mod_cast halasz_vinogradov_initial_bound k r N

end TwoPointCorrelations

end OAI
