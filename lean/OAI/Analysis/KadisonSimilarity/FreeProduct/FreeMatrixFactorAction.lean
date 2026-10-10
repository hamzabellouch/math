import OAI.Analysis.KadisonSimilarity.FreeProduct.FreeMatrixConjugation
import OAI.Analysis.KadisonSimilarity.Tracial.MatrixConjugateAutomorphism

namespace OAI

/-! The free-word isometry fixes the base algebra and intertwines left
multiplication by the matrix factor. -/

noncomputable section
namespace KadisonSimilarity.TracialCornerGeometry

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (G : TracialCornerGeometry P H) (A D : StarSubalgebra ℂ P)
  [IsClosed (A : Set P)] [IsClosed (D : Set P)]
  {α : Type*} [Fintype α] [DecidableEq α]
  (ι : Matrix α α ℂ →⋆ₐ[ℂ] D) (u : Matrix.unitaryGroup α ℂ)
  (hτ : G.trace 1 = 1) (hf : ScalarFree G.trace D A)
  (hgen : ReducedWordGenerated G A D)

local notation "W" => G.freeMatrixConjugationIsometry A D ι u hτ hf hgen

@[simp] theorem freeMatrixConjugationIsometry_base (a : A) :
    W (G.vector (a : P)) = G.vector (a : P) := by
  simpa only [alternatingProduct_zero, matrixConjugateLetter_one_letter,
    OneMemClass.coe_one, one_mul, mul_one] using
    G.freeMatrixConjugationIsometry_word A D ι u hτ hf hgen 0 1 a
      Fin.elim0 Fin.elim0 (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)

@[simp] theorem freeMatrixConjugationIsometry_one : W (G.vector 1) = G.vector 1 :=
  G.freeMatrixConjugationIsometry_base A D ι u hτ hf hgen 1

theorem freeMatrixConjugationIsometry_other_word (x : D)
    (n : ℕ) (d : D) (b : A) (a : Fin n → A) (c : Fin n → D)
    (ha : ∀ i, G.trace (a i : P) = 0) (hc : ∀ i, G.trace (c i : P) = 0) :
    W (G.left (x : P) (G.vector ((d : P) *
      alternatingProduct (fun i => (a i : P)) (fun i => (c i : P)) * (b : P)))) =
    G.left (matrixConjugateLetter D ι u x : P)
      (W (G.vector ((d : P) *
        alternatingProduct (fun i => (a i : P)) (fun i => (c i : P)) * (b : P)))) := by
  rw [G.left_vector, G.freeMatrixConjugationIsometry_word A D ι u hτ hf hgen n d b a c ha hc,
    G.left_vector]
  have h := G.freeMatrixConjugationIsometry_word A D ι u hτ hf hgen
    n (x * d) b a c ha hc
  simpa only [MulMemClass.coe_mul, matrixConjugateLetter_product, mul_assoc] using h

theorem freeMatrixConjugationIsometry_other (x : D) :
    (W).toContinuousLinearMap.comp (G.left (x : P)) =
      (G.left (matrixConjugateLetter D ι u x : P)).comp (W).toContinuousLinearMap := by
  apply sub_eq_zero.mp
  apply continuousLinearMap_eq_zero_of_total (G.freeWordFamily A D)
    (G.freeWordFamily_total A D hgen)
  rintro ⟨n, p⟩
  change W (G.left (x : P) (G.freeWordFamily A D ⟨n, p⟩)) -
    G.left (matrixConjugateLetter D ι u x : P) (W (G.freeWordFamily A D ⟨n, p⟩)) = 0
  exact sub_eq_zero.mpr (G.freeMatrixConjugationIsometry_other_word A D ι u hτ hf hgen
    x n p.2.1 p.1.2 (fun i => (p.1.1 i).1) (fun i => (p.2.2 i).1)
    (fun i => (p.1.1 i).2) (fun i => (p.2.2 i).2))

end KadisonSimilarity.TracialCornerGeometry

end

end OAI
