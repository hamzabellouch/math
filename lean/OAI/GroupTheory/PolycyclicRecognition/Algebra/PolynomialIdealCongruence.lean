import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolynomialSubalgebraFiltration

namespace OAI

/-! # Congruence of the polynomial group law modulo a Lie ideal -/

noncomputable section
namespace PolycyclicRecognition
variable {V : Type*} [LieRing V] [LieAlgebra ℝ V]

theorem finiteDynkinPolynomial_sub_mem_of_sub_mem {c n : ℕ}
    (coeff : DynkinCoefficients c n) (J : LieIdeal ℝ V) (X Y : Fin n → V)
    (hXY : ∀ i, X i - Y i ∈ J) :
    finiteDynkinPolynomial coeff X - finiteDynkinPolynomial coeff Y ∈ J := by
  simp only [finiteDynkinPolynomial, ← Finset.sum_sub_distrib, ← smul_sub]
  apply J.sum_mem
  intro d _
  apply J.sum_mem
  intro w _
  exact J.smul_mem _ (evalBracketWord_sub_mem X Y J hXY (rightNestedWord d.val w))

variable {L : Type} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [P : PolynomialExponentialCoordinates L]
attribute [local instance] polynomialSubalgebraGroup

theorem polynomialSubalgebra_mul_congr (K : LieSubalgebra ℝ L) (J : LieIdeal ℝ K)
    (a b c d : K) (hac : a - c ∈ J) (hbd : b - d ∈ J) : a * b - c * d ∈ J := by
  rw [polynomialSubalgebra_mul_eq, polynomialSubalgebra_mul_eq]
  apply finiteDynkinPolynomial_sub_mem_of_sub_mem P.coefficients J
  intro i
  fin_cases i
  · exact hac
  · exact hbd

theorem polynomialSubalgebra_mul_inv_mem_of_sub_mem (K : LieSubalgebra ℝ L)
    (J : LieIdeal ℝ K) (a b : K) (hab : a - b ∈ J) : a * b⁻¹ ∈ J := by
  have h := polynomialSubalgebra_mul_congr K J a b⁻¹ b b⁻¹ hab (by simp)
  have hone : (1 : K) = 0 := Subtype.ext P.one_eq_zero
  simpa only [mul_inv_cancel, hone, sub_zero] using h

theorem polynomialSubalgebra_conjugate_mem (K : LieSubalgebra ℝ L)
    (J : LieIdeal ℝ K) (x : K) (hx : x ∈ J) (v : K) : v * x * v⁻¹ ∈ J := by
  have hone : (1 : K) = 0 := Subtype.ext P.one_eq_zero
  have hv0 : v * (0 : K) = v := by rw [← hone, mul_one]
  have hh : v * x - v ∈ J := by
    have hh := polynomialSubalgebra_mul_congr K J v x v 0 (by simp) (by simpa using hx)
    rwa [hv0] at hh
  exact polynomialSubalgebra_mul_inv_mem_of_sub_mem K J (v * x) v hh

end PolycyclicRecognition

end

end OAI
