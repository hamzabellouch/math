import Mathlib
import OAI.Analysis.Commutator.MatrixVectorTrace
import OAI.Analysis.Commutator.RowOperator

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators InnerProductSpace ComplexOrder

namespace Kadison.MatrixGNS

variable {A ι : Type*} [CStarAlgebra A] [Fintype ι]

local instance matrixRowCornerDecidableEq : DecidableEq ι := Classical.decEq ι

def rowMatrix (i : ι) (a : A) : CStarMatrix ι ι A :=
  CStarMatrix.ofMatrix (fun j k => if j=i ∧ k=i then a else 0)

omit [Fintype ι] in
@[simp] lemma rowMatrix_apply (i : ι) (a : A) (j k : ι) :
    rowMatrix i a j k=if j=i ∧ k=i then a else 0 := rfl

lemma rowMatrix_corner (i : ι) (X : CStarMatrix ι ι A) :
    rowMatrix i (1:A)*X*rowMatrix i (1:A)=rowMatrix i (X i i) := by
  ext j k
  simp only [CStarMatrix.mul_apply,rowMatrix_apply]
  by_cases hj : j=i <;> by_cases hk : k=i <;> simp [hj,hk]

lemma rowMatrix_mul (i : ι) (a b : A) : rowMatrix i a*rowMatrix i b=rowMatrix i (a*b) := by
  ext j k
  simp only [CStarMatrix.mul_apply,rowMatrix_apply]
  by_cases hj : j=i <;> by_cases hk : k=i <;> simp [hj,hk]

omit [Fintype ι] in
lemma rowMatrix_star (i : ι) (a : A) : star (rowMatrix i a)=rowMatrix i (star a) := by
  ext j k
  simp only [CStarMatrix.star_apply,rowMatrix_apply]
  by_cases hj : j=i <;> by_cases hk : k=i <;> simp [hj,hk]

lemma rowMatrix_projection (i : ι) : IsStarProjection (rowMatrix i (1:A)) := by
  constructor
  · change rowMatrix i (1:A)*rowMatrix i (1:A)=rowMatrix i 1
    rw [rowMatrix_mul,one_mul]
  · change star (rowMatrix i (1:A))=rowMatrix i 1
    rw [rowMatrix_star,star_one]

variable [PartialOrder A] [StarOrderedRing A]

lemma rowMatrix_trace (τ : A →ₚ[ℂ] ℂ) (h1 : τ 1=1) (i : ι) :
    trace (ι:=ι) τ (rowMatrix i (1:A))=(Fintype.card ι : ℂ)⁻¹ := by
  rw [trace_apply]
  simp [rowMatrix_apply,apply_ite,h1]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma rowMatrix_representation (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (i : ι) (a : A) :
    CyclicColumns.matrixRepresentation σ (rowMatrix i a)=
      OperatorAmplification.position ι i i (σ a) := by
  ext v j
  simp only [CyclicColumns.matrixRepresentation,CyclicColumns.matrixAction_apply,
    StarAlgHom.coe_mk,rowMatrix_apply,OperatorAmplification.position_apply,
    OperatorAmplification.single_apply]
  by_cases hj : j=i <;> simp [hj,apply_ite,ite_apply]

lemma row_corner_commutator_bound (σ : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (T : H →L[ℂ] H) {c : ℝ} (hc : 0≤c)
    (hT : ∀ a : A,‖T*σ a-σ a*T‖≤c*‖a‖) (i : ι)
    (X : CStarMatrix ι ι A) (hX : rowMatrix i (1:A)*X*rowMatrix i (1:A)=X) :
    ‖OperatorAmplification.diagonal (H:=H) ι T*CyclicColumns.matrixRepresentation σ X-
      CyclicColumns.matrixRepresentation σ X*OperatorAmplification.diagonal (H:=H) ι T‖≤c*‖X‖ := by
  have he : X=rowMatrix i (X i i) := hX.symm.trans (rowMatrix_corner i X)
  calc
    _ = ‖T*σ (X i i)-σ (X i i)*T‖ := by
      conv_lhs => rw [he,rowMatrix_representation,
        OperatorAmplification.norm_diagonal_commutator_position]
    _ ≤ c*‖X i i‖ := hT _
    _ ≤ c*‖X‖ := mul_le_mul_of_nonneg_left CStarMatrix.norm_entry_le_norm hc

end Kadison.MatrixGNS

end

end
end

end OAI
