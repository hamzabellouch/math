import OAI.MathematicalPhysics.DefocusingNLS.Profile.ProfileMatrixProduct

namespace OAI

/-! Entrywise majorants for the finite free-profile Taylor remainder. -/

open Matrix
namespace DefocusingNLS.ProfileCertificate

/-- Entrywise complex modulus bounds, retaining the two-term matrix product. -/
def Dominates (E : Matrix (Fin 2) (Fin 2) ℝ)
    (A : Matrix (Fin 2) (Fin 2) ℂ) : Prop := ∀ i j, ‖A i j‖ ≤ E i j

namespace Dominates

theorem nonneg {E : Matrix (Fin 2) (Fin 2) ℝ} {A : Matrix (Fin 2) (Fin 2) ℂ}
    (h : Dominates E A) (i j : Fin 2) : 0 ≤ E i j := (norm_nonneg _).trans (h i j)

theorem add {E F : Matrix (Fin 2) (Fin 2) ℝ} {A B : Matrix (Fin 2) (Fin 2) ℂ}
    (hA : Dominates E A) (hB : Dominates F B) : Dominates (E+F) (A+B) := by
  intro i j
  exact (norm_add_le _ _).trans (add_le_add (hA i j) (hB i j))

theorem mul {E F : Matrix (Fin 2) (Fin 2) ℝ} {A B : Matrix (Fin 2) (Fin 2) ℂ}
    (hA : Dominates E A) (hB : Dominates F B) : Dominates (E*F) (A*B) := by
  intro i j
  simp only [Matrix.mul_apply, Fin.sum_univ_two]
  apply (norm_add_le _ _).trans
  rw [norm_mul, norm_mul]
  exact add_le_add
    (mul_le_mul (hA i 0) (hB 0 j) (norm_nonneg _) (hA.nonneg i 0))
    (mul_le_mul (hA i 1) (hB 1 j) (norm_nonneg _) (hA.nonneg i 1))

theorem smul {E : Matrix (Fin 2) (Fin 2) ℝ} {A : Matrix (Fin 2) (Fin 2) ℂ}
    (hA : Dominates E A) (r : ℝ) : Dominates (|r| • E) (r • A) := by
  intro i j
  simp only [Matrix.smul_apply, norm_smul, Real.norm_eq_abs, smul_eq_mul]
  exact mul_le_mul_of_nonneg_left (hA i j) (abs_nonneg r)

theorem mono {E F : Matrix (Fin 2) (Fin 2) ℝ} {A : Matrix (Fin 2) (Fin 2) ℂ}
    (hA : Dominates E A) (hEF : ∀ i j, E i j ≤ F i j) : Dominates F A := by
  intro i j
  exact (hA i j).trans (hEF i j)

theorem smul_le {E : Matrix (Fin 2) (Fin 2) ℝ} {A : Matrix (Fin 2) (Fin 2) ℂ}
    (hA : Dominates E A) (r δ : ℝ) (hr : |r| ≤ δ) : Dominates (δ • E) (r • A) := by
  apply (hA.smul r).mono
  intro i j
  exact mul_le_mul_of_nonneg_right hr (hA.nonneg i j)

end Dominates

noncomputable def rationalMatrix (E : RMatrix) : Matrix (Fin 2) (Fin 2) ℝ :=
  (Matrix2.toMatrix E).map (Rat.castHom ℝ)

noncomputable def absoluteMatrix (A : QMatrix) : Matrix (Fin 2) (Fin 2) ℝ :=
  rationalMatrix (Matrix2.map RationalComplex.absOne A)

theorem absoluteMatrix_dominates (A : QMatrix) : Dominates (absoluteMatrix A) (complexMatrix A) := by
  intro i j
  fin_cases i <;> fin_cases j <;> exact RationalComplex.norm_toComplex_le_absOne _

/-- The exact algebraic remainder identity. -/
theorem product_remainder (F P U V R : Matrix (Fin 2) (Fin 2) ℂ) :
    (F+P)*(U+V+R)-(F*U+F*V+P*U) = (F+P)*R+P*V := by
  noncomm_ring

/-- Propagate one Taylor remainder without losing the entrywise product structure. -/
theorem product_remainder_dominates
    (F P U V R : Matrix (Fin 2) (Fin 2) ℂ)
    (Fbound N Vbound E : Matrix (Fin 2) (Fin 2) ℝ) (δ : ℝ)
    (hF : Dominates Fbound F) (hP : Dominates (δ • N) P)
    (hV : Dominates (δ • Vbound) V) (hR : Dominates (δ^2 • E) R) :
    Dominates (δ^2 • ((Fbound+δ • N)*E+N*Vbound))
      ((F+P)*(U+V+R)-(F*U+F*V+P*U)) := by
  rw [product_remainder]
  have h := ((hF.add hP).mul hR).add (hP.mul hV)
  convert! h using 1
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.mul_apply,
    Fin.sum_univ_two, smul_eq_mul]
  ring

end DefocusingNLS.ProfileCertificate

end OAI
