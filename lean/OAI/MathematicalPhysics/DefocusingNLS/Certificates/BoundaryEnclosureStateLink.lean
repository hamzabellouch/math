import OAI.MathematicalPhysics.DefocusingNLS.Certificates.BoundaryEnclosureState
import OAI.MathematicalPhysics.DefocusingNLS.Certificates.BoundaryPolynomialParity

namespace OAI

/-! # The coherent enclosure state is the polynomial forward matrix -/

open Polynomial Matrix

namespace DefocusingNLS.BoundaryCertificate

attribute [local irreducible] polynomialState

noncomputable def stateMatrix (pq : PolynomialState) : Matrix (Fin 2) (Fin 2) (Polynomial ℂ) :=
  !![pq.1.1, pq.1.2; pq.2.1, pq.2.2]

noncomputable def scaledConstant (ell n : ℕ) (b : ℝ) : ℂ :=
  (inputReal ell n : ℂ) - Complex.I * (100000000 * b : ℝ)

noncomputable def scaledMass (ell : ℕ) : ℝ := (100000000 * (ell + 5) : ℤ)

noncomputable def scaledShift (Z : ℝ) : ℂ := Complex.I * (100000000 * Z : ℝ)

noncomputable def variableScale : Polynomial ℂ := C (100000000 : ℂ) * X

theorem polynomialStep_matrix (M s t : Polynomial ℂ) (pq : PolynomialState) :
    stateMatrix (polynomialStep M s t pq) =
      (!![t, s; -t, t - M - s] : Matrix (Fin 2) (Fin 2) (Polynomial ℂ)) * stateMatrix pq := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [stateMatrix, polynomialStep, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem inputT_eq_comp (ell n : ℕ) (b : ℝ) :
    inputT ell n b = (boundaryLinear (scaledConstant ell n b)).comp variableScale := by
  have hc : C (Complex.I * (100000000 : ℝ)) =
      C Complex.I * C (100000000 : ℂ) := by norm_num [map_mul]
  simp only [inputT, boundaryLinear, scaledConstant, variableScale, add_comp,
    mul_comp, C_comp, X_comp, hc]
  ring

theorem boundaryForwardStep_scaled_comp (ell n : ℕ) (b Z : ℝ) (i j : Fin 2) :
    ((boundaryForwardStep (scaledMass ell) (scaledShift Z) (scaledConstant ell n b) i j).comp
      variableScale) =
      (!![inputT ell n b, inputS Z; -inputT ell n b,
        inputT ell n b - C ((100000000 * (ell + 5) : ℤ) : ℂ) - inputS Z] :
        Matrix (Fin 2) (Fin 2) (Polynomial ℂ)) i j := by
  fin_cases i <;> fin_cases j <;>
    simp [boundaryForwardStep, ← inputT_eq_comp, inputS, scaledShift, scaledMass]

/-- This identity connects the exact uncertain-coefficient recursion to the
parameter-uniform polynomial degree and parity theorems. -/
theorem polynomialState_matrix (ell : ℕ) (b Z : ℝ) (K : ℕ) (i j : Fin 2) :
    stateMatrix (polynomialState ell b Z K) i j =
      (boundaryForwardProduct (scaledMass ell) (scaledShift Z)
        (fun n => scaledConstant ell n b) K i j).comp variableScale := by
  induction K generalizing i j with
  | zero => fin_cases i <;> fin_cases j <;> simp [polynomialState, stateMatrix, boundaryForwardProduct]
  | succ K ih =>
    rw [polynomialState, polynomialStep_matrix]
    simp only [Matrix.mul_apply, Fin.sum_univ_two, ih, boundaryForwardProduct,
      add_comp, mul_comp]
    rw [boundaryForwardStep_scaled_comp, boundaryForwardStep_scaled_comp]

end DefocusingNLS.BoundaryCertificate

end OAI
