import OAI.LinearAlgebra.MatrixMultiplication.Tensor.ComplexWitness
import OAI.LinearAlgebra.MatrixMultiplication.Numerical.ComplexCertificates

namespace OAI

/-! Explicit complex square and rectangular matrix multiplication bounds. -/

open Filter

namespace MatrixMultiplication.SquareWitness

open MatrixMultiplication.Foundation

def leafCount : ℕ := 2995461856366867388223311649574852466276480577

theorem leafCount_pos : 0 < leafCount := by decide

theorem exponent_upper {c l : ℝ}
    (hc : c < (10987 : ℝ) / 10000)
    (hl : (523471 : ℝ) / 5000 < l) :
    216 * c / l < (1186596 : ℝ) / 523471 := by
  have hl₀ : 0 < l := by linarith
  apply (div_lt_iff₀ hl₀).2
  nlinarith

theorem exponent_lt_target {c l : ℝ}
    (hc : c < (10987 : ℝ) / 10000)
    (hl : (523471 : ℝ) / 5000 < l) :
    216 * c / l < (2267 : ℝ) / 1000 := by
  exact (exponent_upper hc hl).trans
    (by norm_num : (1186596 : ℝ) / 523471 < 2267 / 1000)

theorem strict_log_gap
    (hthree : Real.log 3 < (10987 : ℝ) / 10000)
    (hleaves : (523471 : ℝ) / 5000 < Real.log leafCount) :
    Real.log 3 < ((2267 : ℝ) / 1000) / 216 * Real.log leafCount := by
  have h := exponent_lt_target hthree hleaves
  have hl₀ : 0 < Real.log leafCount := by linarith
  have hm := (div_lt_iff₀ hl₀).1 h
  nlinarith

theorem omega_lt_of_uniform_square_family
    (W : ℕ → FiniteMMRealization)
    (hlimit : Tendsto
      (fun n => (W n).rates.score ((2267 : ℝ) / 1000)) atTop
      (nhds (((2267 : ℝ) / 1000) / 216 * Real.log leafCount)))
    (hthree : Real.log 3 < (10987 : ℝ) / 10000)
    (hleaves : (523471 : ℝ) / 5000 < Real.log leafCount) :
    Arithmetic.omega < (2267 : ℝ) / 1000 :=
  ComplexWitness.omega_lt_of_score_limit W hlimit (strict_log_gap hthree hleaves)

theorem omega_lt_of_certified_uniform_square_family
    (W : ℕ → FiniteMMRealization)
    (hlimit : Tendsto
      (fun n => (W n).rates.score ((2267 : ℝ) / 1000)) atTop
      (nhds (((2267 : ℝ) / 1000) / 216 * Real.log leafCount))) :
    Arithmetic.omega < (2267 : ℝ) / 1000 := by
  apply omega_lt_of_uniform_square_family W hlimit
    ComplexCertificates.log_three_upper
  exact ComplexCertificates.square_log_lower

end MatrixMultiplication.SquareWitness

end OAI
