import Mathlib
import OAI.Analysis.FreeWords.MatrixConditionalExpectation
import OAI.Analysis.FreeWords.RelativeConjugationDefinitions

namespace OAI

noncomputable section

namespace KKControlledConjugation

open KKRelativeMatrix KKMatrixExpectation KKTraceTransfer KKFreeLiftFrontier

noncomputable section

variable {A : Type*} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]

def amplifyConj (n : ℕ) (u : unitary A) :
    Matrix (Fin n) (Fin n) A →⋆ₐ[ℂ] Matrix (Fin n) (Fin n) A :=
  { (Unitary.conjStarAlgAut ℂ A u).toStarAlgHom.toAlgHom.mapMatrix with
    map_star' := by
      intro X
      ext i j
      exact map_star (Unitary.conjStarAlgAut ℂ A u) (X j i) }

omit [StarModule ℂ A] in
@[simp] theorem amplifyConj_apply (n : ℕ) (u : unitary A)
    (X : Matrix (Fin n) (Fin n) A) (i j : Fin n) :
    amplifyConj n u X i j=u.val*X i j*star u.val := rfl

omit [StarModule ℂ A] in
theorem conj_trace (τ : A →ₗ[ℂ] ℂ) (htr : ∀a b,τ (a*b)=τ (b*a))
    (u : unitary A) (a : A) : τ (u.val*a*star u.val)=τ a := by
  rw [htr,← mul_assoc]
  rw [show star u.val*u.val=1 from u.property.1,one_mul]

omit [StarModule ℂ A] in
theorem amplifyConj_trace (τ : A →ₗ[ℂ] ℂ) (htr : ∀a b,τ (a*b)=τ (b*a))
    (n : ℕ) (u : unitary A) (X : Matrix (Fin n) (Fin n) A) :
    matrixTraceMap τ n (amplifyConj n u X)=matrixTraceMap τ n X := by
  simp only [matrixTraceMap_apply,amplifyConj_apply,conj_trace τ htr]

theorem amplifyConj_expectation (τ : A →ₗ[ℂ] ℂ) (htr : ∀a b,τ (a*b)=τ (b*a))
    (n : ℕ) (u : unitary A) (X : Matrix (Fin n) (Fin n) A) :
    matrixExpectation τ n (amplifyConj n u X)=matrixExpectation τ n X := by
  ext i j
  simp only [matrixExpectation_apply,amplifyConj_apply,conj_trace τ htr]

theorem amplifyConj_numerical (n : ℕ) (u : unitary A) (b : Matrix (Fin n) (Fin n) ℂ) :
    amplifyConj n u (numericalHom (A := A) n b)=numericalHom (A := A) n b := by
  ext i j
  change (Unitary.conjStarAlgAut ℂ A u) (algebraMap ℂ A (b i j))=algebraMap ℂ A (b i j)
  exact (Unitary.conjStarAlgAut ℂ A u).toStarAlgHom.commutes (b i j)

theorem amplifyConj_entry_range {n d : ℕ} (u : unitary A)
    (ρ : Matrix (Fin d) (Fin d) ℂ →⋆ₐ[ℂ] A)
    (X : Matrix (Fin n) (Fin n) A) (hX : ∀i j,X i j∈ρ.range) (i j : Fin n) :
    amplifyConj n u X i j∈((Unitary.conjStarAlgAut ℂ A u).toStarAlgHom.comp ρ).range := by
  obtain ⟨a,ha⟩ := hX i j
  refine ⟨a,?_⟩
  change (Unitary.conjStarAlgAut ℂ A u) (ρ a)= (Unitary.conjStarAlgAut ℂ A u) (X i j)
  exact congrArg (Unitary.conjStarAlgAut ℂ A u) ha

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem amplifyConj_eq_scalarConjugate {M : VonNeumannAlgebra H} {n : ℕ}
    (u : unitary (ConcreteAlgebra M)) (X : Matrix (Fin n) (Fin n) (ConcreteAlgebra M)) :
    amplifyConj n u X=scalarConjugate u X := by
  ext i j
  simp only [amplifyConj_apply,scalarConjugate,Matrix.diagonal_mul,Matrix.mul_diagonal]
  rfl

end

end KKControlledConjugation
end

end OAI
