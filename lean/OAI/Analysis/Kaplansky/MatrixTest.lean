import OAI.Analysis.Kaplansky.BundlePolynomials
import OAI.Analysis.Kaplansky.Operators
import OAI.Analysis.Kaplansky.TestAlgebra
import OAI.Analysis.Quasitrace.Infiniteness

namespace OAI

noncomputable section

/-! Polynomial evaluation and actual matrix test operators. -/

open scoped BigOperators
namespace Kaplansky

/-- Algebraic words in the constructed bounded-product generators evaluate
as the actual Hilbert-shift words, on arbitrary Hilbert vectors. -/
theorem actualAlgebraWord_eval (z : ActualTestIndex) (w : List (Bool × Fin 24)) (v : ActualHilbert z) :
    algebraStarWord actualBoundedGenerator w z v =
      applyWord (shiftLetter (fun i j => actualTestOperator i z j)
        (fun i j => actualTestOperator_norm i z j)) w v := by
  induction w with
  | nil => rfl
  | cons l w ih =>
    obtain ⟨b,i⟩ := l
    cases b with
    | false =>
      change forwardShift (actualTestOperator i z) (actualTestOperator_norm i z)
        (algebraStarWord actualBoundedGenerator w z v) = _
      rw [ih]
      rfl
    | true =>
      change (forwardShift (actualTestOperator i z) (actualTestOperator_norm i z)).adjoint
        (algebraStarWord actualBoundedGenerator w z v) = _
      rw [ih]
      rfl

/-- Exact representation of the finitely supported polynomial supplied by
density, before restriction to the bottom-level bundle. -/
theorem actualAlgebraPolynomial_eval (z : ActualTestIndex) (p : StarWordPolynomial 24)
    (v : ActualHilbert z) :
    actualRepresentation z (generatedWordPolynomial actualBoundedGenerator p) v =
      ∑ w ∈ p.support, p w • applyWord (shiftLetter (fun i j => actualTestOperator i z j)
        (fun i j => actualTestOperator_norm i z j)) w v := by
  change (∑ w ∈ p.support, p w • algebraStarWord actualBoundedGenerator w) z v = _
  rw [show ((∑ w ∈ p.support, p w • algebraStarWord actualBoundedGenerator w) z) =
      ∑ w ∈ p.support, p w • algebraStarWord actualBoundedGenerator w z from by
    exact map_sum (boundedProductEval z) _ _]
  simp only [sum_apply,smul_apply]
  exact Finset.sum_congr rfl (fun w _ => congrArg (fun u => p w • u) (actualAlgebraWord_eval z w v))

attribute [local instance 2000] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing

theorem actualRepresentation_matrix_column {m n : ℕ}
    (W : CStarMatrix (Fin m) (Fin n) ActualAlgebra)
    (h : ∀ i j, (∑ row, star (W row i)*W row j)=if i=j then 1 else 0)
    (z : ActualTestIndex) (i j : Fin n) :
    (∑ row, (actualRepresentation z (W row i)).adjoint.comp (actualRepresentation z (W row j))) =
      if i=j then ContinuousLinearMap.id ℂ (ActualHilbert z) else 0 := by
  have he := congrArg (actualRepresentation z) (h i j)
  have hstar (b : ActualAlgebra) : actualRepresentation z (star b) = (actualRepresentation z b).adjoint := rfl
  simp only [map_sum,map_mul,hstar] at he
  have hone : actualRepresentation z 1 = ContinuousLinearMap.id ℂ (ActualHilbert z) := rfl
  have hzero : actualRepresentation z 0 = 0 := rfl
  change (∑ row, (actualRepresentation z (W row i)).adjoint * (actualRepresentation z (W row j))) = _
  by_cases hij : i=j
  · simpa only [hij,ite_true,hone] using he
  · simpa only [hij,ite_false,hzero] using he

theorem actualRepresentation_matrix_entry_close {m n : ℕ}
    (P W : CStarMatrix (Fin m) (Fin n) ActualAlgebra) {δ : ℝ} (h : ‖P-W‖ < δ)
    (z : ActualTestIndex) (i : Fin m) (j : Fin n) :
    ‖actualRepresentation z (P i j)-actualRepresentation z (W i j)‖ ≤ δ := by
  have hentry := CStarMatrix.norm_entry_le_norm (M := P-W) (i := i) (j := j)
  have he := NonUnitalStarAlgHom.norm_apply_le (actualRepresentation z) ((P-W) i j)
  have hsub := map_sub (actualRepresentation z) (P i j) (W i j)
  exact (congrArg norm hsub).symm.le.trans (he.trans (hentry.trans h.le))

/-- The matrix entries supplied by density and their extracted term list
have precisely the same action on the matching actual test Hilbert space. -/
theorem actualPolynomialMatrix_action {m n : ℕ} (hm : 0<m)
    (p : Fin m → Fin n → StarWordPolynomial 24)
    (y : SmoothTestBase m (matrixPolynomialDegree p))
    (v : MatrixTowerHilbert (testSequenceStage m (matrixPolynomialDegree p)) n y) :
    operatorMatrixAction (fun row col => actualRepresentation
      ⟨⟨m,hm⟩,⟨matrixPolynomialDegree p,matrixPolynomialDegree_pos p⟩,y⟩
      (generatedWordPolynomial actualBoundedGenerator (p row col))) v =
    matrixPolynomialAction (testSequenceStep (R := matrixPolynomialDegree p) hm)
      Finset.univ (matrixPolynomialTerm p) y v := by
  apply (PiLp.continuousLinearEquiv 2 ℂ
    (fun _ : Fin m => ActualHilbert ⟨⟨m,hm⟩,⟨matrixPolynomialDegree p,matrixPolynomialDegree_pos p⟩,y⟩)).injective
  funext row
  change operatorMatrixAction (fun r c => actualRepresentation
    (⟨⟨m,hm⟩,⟨matrixPolynomialDegree p,matrixPolynomialDegree_pos p⟩,y⟩ : ActualTestIndex)
    (generatedWordPolynomial actualBoundedGenerator (p r c))) v row =
    (matrixPolynomialAction (testSequenceStep (R := matrixPolynomialDegree p) hm)
      Finset.univ (matrixPolynomialTerm p) y v) row
  have hleft := operatorMatrixAction_apply (fun r c => actualRepresentation
    (⟨⟨m,hm⟩,⟨matrixPolynomialDegree p,matrixPolynomialDegree_pos p⟩,y⟩ : ActualTestIndex)
    (generatedWordPolynomial actualBoundedGenerator (p r c))) v row
  have hsum := Finset.sum_congr (s₁ := Finset.univ) rfl (fun col _ => actualAlgebraPolynomial_eval
    (⟨⟨m,hm⟩,⟨matrixPolynomialDegree p,matrixPolynomialDegree_pos p⟩,y⟩ : ActualTestIndex)
    (p row col) (v col))
  exact hleft.trans (hsum.trans (matrixPolynomialTerm_sum p _ (fun col => v col) row).symm)

end Kaplansky

end

end OAI
