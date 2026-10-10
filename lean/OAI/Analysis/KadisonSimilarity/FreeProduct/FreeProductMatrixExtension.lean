import OAI.Analysis.KadisonSimilarity.Tracial.TracialBaseGeometry
import Mathlib.LinearAlgebra.UnitaryGroup

namespace OAI

/-! The precise two-factor matrix-automorphism extension input. -/

noncomputable section
namespace KadisonSimilarity
namespace TracialCornerGeometry

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (G : TracialCornerGeometry P H) (D : StarSubalgebra ℂ P)
  {α : Type*} [Fintype α] [DecidableEq α]
  (ι : Matrix α α ℂ →⋆ₐ[ℂ] D) (u : Matrix.unitaryGroup α ℂ)

/-- Algebraic conjugation of a letter in the other factor. -/
def matrixConjugateLetter (c : D) : D :=
  ι (u : Matrix α α ℂ) * c * star (ι (u : Matrix α α ℂ))

@[simp] theorem matrixConjugateLetter_one (c : D) :
    matrixConjugateLetter D ι 1 c = c := by
  simp [matrixConjugateLetter]

theorem matrixConjugateLetter_mul (v : Matrix.unitaryGroup α ℂ) (c : D) :
    matrixConjugateLetter D ι (u * v) c =
      matrixConjugateLetter D ι u (matrixConjugateLetter D ι v c) := by
  simp only [matrixConjugateLetter, Submonoid.coe_mul, map_mul, star_mul, mul_assoc]

@[simp] theorem matrixConjugateLetter_inv (c : D) :
    matrixConjugateLetter D ι u⁻¹ (matrixConjugateLetter D ι u c) = c := by
  rw [← matrixConjugateLetter_mul, inv_mul_cancel, matrixConjugateLetter_one]

@[simp] theorem trace_matrixConjugateLetter (c : D) :
    G.trace (matrixConjugateLetter D ι u c : P) = G.trace (c : P) := by
  have huD : star (ι (u : Matrix α α ℂ)) * ι (u : Matrix α α ℂ) = 1 := by
    rw [← map_star, ← map_mul, u.property.1, map_one]
  have huP : star (ι (u : Matrix α α ℂ) : P) * (ι (u : Matrix α α ℂ) : P) = 1 :=
    congrArg (fun x : D => (x : P)) huD
  change G.trace (((ι (u : Matrix α α ℂ) : P) * (c : P)) *
    star (ι (u : Matrix α α ℂ) : P)) = G.trace (c : P)
  rw [G.tracial, ← mul_assoc, huP, one_mul]

/-- The two-factor specialization of Blanchard--Dykema, *Embeddings of reduced
free products of operator algebras*, Pacific J. Math. 199 (2001), 1--19,
Theorem 3.7 (arXiv:math/9911012, p. 13). Applied to a tracial reduced free
product, the identity embedding on the base factor and matrix conjugation on
the other factor extend to a trace-preserving normal star homomorphism.

Only the algebraic extension and trace preservation are recorded here; no
unitary implementation, completed-word covariance, or operator estimate is
included. Normality is not needed for the L² construction. -/
def MatrixConjugationExtensionInput (A : StarSubalgebra ℂ P) : Prop :=
  ∀ v : Matrix.unitaryGroup α ℂ, ∃ Φ : P →⋆ₐ[ℂ] P,
    (∀ x, G.trace (Φ x) = G.trace x) ∧
    (∀ a : A, Φ (a : P) = (a : P)) ∧
    (∀ d : D, Φ (d : P) = (matrixConjugateLetter D ι v d : P))

end TracialCornerGeometry
end KadisonSimilarity

end

end OAI
