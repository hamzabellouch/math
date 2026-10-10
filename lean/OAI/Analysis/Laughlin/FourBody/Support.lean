import OAI.Analysis.Laughlin.FourBody.PhysicalTrace

namespace OAI

namespace Laughlin.Spin
open Rotation MeasureTheory
open scoped BigOperators Matrix

theorem realOuter_mulVec_row {I : Type*} [Fintype I] (u v w : I → ℝ) (i : I) :
    (realOuter u v *ᵥ w) i = u i * dotProduct w v := by
  simp only [Matrix.mulVec,dotProduct,realOuter,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem fourBodyTermMatrix_high_copy (Q r D t : ℕ) (hr : r ≤ Q) (hrD : r ≤ D)
    (hA : D-r ≤ 2*Q-2) (hB : D-r ≤ genericCoupledWeight Q Q r)
    (e f : ℕ × ℕ × ℤ) (he : t ≤ e.1+e.2.1) (hf : t ≤ f.1+f.2.1)
    (hT : e.1+e.2.1+(f.1+f.2.1-t) < D) :
    fourBodyTermMatrix Q t e f * fourBodyInclusion Q r D hr hA hB = 0 := by
  ext i n
  change (fourBodyTermMatrix Q t e f *ᵥ fourBodyCopy Q r D hr hA hB n.val) i=0
  rw [fourBodyTermMatrix,Matrix.smul_mulVec]
  simp only [Pi.smul_apply,smul_eq_mul]
  rw [realOuter_mulVec_row,fourBodyCopy_signed_off Q r D n.val f.1 f.2.1
    (e.1+e.2.1-t) hr hrD hA hB (by omega),mul_zero,mul_zero]

theorem list_sum_mul_zero {I J K : Type*} [Fintype J]
    (l : List (Matrix I J ℝ)) (W : Matrix J K ℝ) (h : ∀ M ∈ l, M*W=0) : l.sum*W=0 := by
  induction l with
  | nil => simp
  | cons M l ih =>
    rw [List.sum_cons,Matrix.add_mul,h M (by simp),ih (fun A hA => h A (by simp [hA])),zero_add]

theorem physicalFourBodyMatrix_high_copy (Q r D : ℕ) (hr : r ≤ Q) (hrD : r ≤ D)
    (hA : D-r ≤ 2*Q-2) (hB : D-r ≤ genericCoupledWeight Q Q r) (hD : 23 < D) :
    physicalFourBodyMatrix Q * fourBodyInclusion Q r D hr hA hB = 0 := by
  unfold physicalFourBodyMatrix
  apply list_sum_mul_zero
  intro M hM
  rcases List.mem_map.mp hM with ⟨row,hrow,rfl⟩
  apply list_sum_mul_zero
  intro A hA'
  rcases List.mem_map.mp hA' with ⟨e,he,rfl⟩
  apply list_sum_mul_zero
  intro B hB'
  rcases List.mem_map.mp hB' with ⟨f,hf,rfl⟩
  exact fourBodyTermMatrix_high_copy Q r D row.1 hr hrD hA hB e f
    (source_rows_admissible row hrow e he) (source_rows_admissible row hrow f hf)
    (by have := source_fourBody_rows_support row hrow e he f hf; omega)

theorem real_matrix_mul_zero_complex {I J K : Type*} [Fintype J]
    (A : Matrix I J ℝ) (B : Matrix J K ℝ) (h : A*B=0) :
    A.map Complex.ofReal * B.map Complex.ofReal=0 := by
  ext i k
  have he := congrArg Complex.ofReal (congrFun (congrFun h i) k)
  simpa only [Matrix.mul_apply,Matrix.map_apply,Complex.ofReal_sum,Complex.ofReal_mul,
    Matrix.zero_apply,Complex.ofReal_zero] using he

theorem physicalFourBodyMatrix_high_wedge_copy (Q r D : ℕ) (hr : r ≤ Q) (hrD : r ≤ D)
    (hA : D-r ≤ 2*Q-2) (hB : D-r ≤ genericCoupledWeight Q Q r) (hD : 23 < D) :
    (physicalFourBodyMatrix Q).map Complex.ofReal * fourWedgeInclusion Q r D hr hA hB = 0 :=
  real_matrix_mul_zero_complex _ _ (physicalFourBodyMatrix_high_copy Q r D hr hrD hA hB hD)

theorem physicalFourBodyHaar_high_copy (Q r D : ℕ) (hr : r ≤ Q) (hor : Odd r) (hrD : r ≤ D)
    (hA : D-r ≤ 2*Q-2) (hB : D-r ≤ genericCoupledWeight Q Q r) (hD : 23 < D) :
    matrixIntegral sourceHaar
      (conjugateOrbit (fourBodySpinRepresentation Q) ((physicalFourBodyMatrix Q).map Complex.ofReal)) *
      fourWedgeInclusion Q r D hr hA hB = 0 := by
  have hz (g : SourceSU2) :
      conjugateOrbit (fourBodySpinRepresentation Q) ((physicalFourBodyMatrix Q).map Complex.ofReal) g *
        fourWedgeInclusion Q r D hr hA hB = 0 := by
    unfold conjugateOrbit
    rw [Matrix.mul_assoc, fourWedgeInclusion_SU2 Q r D hr hor hA hB, Matrix.mul_assoc,
      ← Matrix.mul_assoc ((physicalFourBodyMatrix Q).map Complex.ofReal),
      physicalFourBodyMatrix_high_wedge_copy Q r D hr hrD hA hB hD,Matrix.zero_mul,Matrix.mul_zero]
  have hi := integral_matrix_sandwich sourceHaar
    (conjugateOrbit (fourBodySpinRepresentation Q) ((physicalFourBodyMatrix Q).map Complex.ofReal))
    (compact_conjugateOrbit_integrable sourceHaar _ (fourBodySpinRepresentation_continuous Q) _)
    (1 : Matrix (FourWedgeIndex Q) (FourWedgeIndex Q) ℂ) (fourWedgeInclusion Q r D hr hA hB)
  simp only [Matrix.one_mul,hz,Matrix.zero_apply,integral_zero] at hi
  exact hi.symm

end Laughlin.Spin

end OAI
