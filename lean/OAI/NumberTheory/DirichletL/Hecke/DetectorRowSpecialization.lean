import OAI.NumberTheory.DirichletL.Hecke.RowClosure
import OAI.NumberTheory.DirichletL.Hecke.Dyadic

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.HeckeDetectorRowSpecialization
open HeckeFamily HeckeDyadic HeckeRowClosure

theorem inverse_polynomial_original_row (η χ : Character) (m f z : O)
    (heq : ∀ n : O, elementCoeff χ n =
      CanonicalRowCompletion.rowTwist (elementHom η) m f z n)
    (W : ℝ→ℂ) (D σ freq : ℝ) :
    polynomial χ true W D σ freq =
      (D : ℂ)^(-(1/2 : ℂ))*∑' J : NonzeroIdeal,
        (UniqueFactorizationMonoid.moebius J.val : ℂ)*idealCoeff η J.val*
          CanonicalRowCompletion.idealRowHom (m^6*f^4*z) J.val*
          W (norm J/D)*((norm J/D : ℝ) : ℂ)^(-shift σ freq) := by
  unfold polynomial
  congr 1
  apply tsum_congr
  intro J
  unfold summand coefficient
  simp only [ite_true,idealCoeff_eq_row η χ m f z heq]
  ring

theorem plain_polynomial_original_row (η χ : Character) (m f z : O)
    (heq : ∀ n : O, elementCoeff χ n =
      CanonicalRowCompletion.rowTwist (elementHom η) m f z n)
    (W : ℝ→ℂ) (D σ freq : ℝ) :
    polynomial χ false W D σ freq =
      (D : ℂ)^(-(1/2 : ℂ))*∑' J : NonzeroIdeal,
        idealCoeff η J.val*CanonicalRowCompletion.idealRowHom (m^6*f^4*z) J.val*
          W (norm J/D)*((norm J/D : ℝ) : ℂ)^(-shift σ freq) := by
  unfold polynomial
  congr 1
  apply tsum_congr
  intro J
  unfold summand coefficient
  simp only [Bool.false_eq_true,ite_false,idealCoeff_eq_row η χ m f z heq]

end SevenEighths.HeckeDetectorRowSpecialization

end

end OAI
