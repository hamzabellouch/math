import OAI.InformationTheory.Entanglement.InstrumentLaw

namespace OAI

noncomputable section
open MeasureTheory Matrix
open scoped BigOperators ComplexOrder MatrixOrder MeasureTheory Kronecker
namespace SecretKey
open ChannelCompletion TensorCriterion
variable {Ω : Type*} [MeasurableSpace Ω]
variable {n r q : Type} [Fintype n] [Fintype r] [Fintype q]
  [DecidableEq n] [DecidableEq r] [DecidableEq q]
omit [DecidableEq r] in
lemma PositiveMatrixMeasure.eq_of_value {U V : PositiveMatrixMeasure Ω r}
    (h : ∀ s, MeasurableSet s → U.value s=V.value s) : U=V := by
  have he : U.entry=V.entry := by
    funext a b
    apply VectorMeasure.ext
    intro s hs
    exact congrArg (fun M : Mat r => M a b) (h s hs)
  cases U
  cases V
  cases he
  rfl
namespace CPOutcomeLaw
variable (L : CPOutcomeLaw Ω n)
omit [Fintype q] [DecidableEq r] [DecidableEq q] in
lemma ref_sandwich_entry (R : Mat (n×r)) (K : Matrix q r ℂ) (i j : n) (a b : q) :
    (((1 : Mat n) ⊗ₖ K)*R*((1 : Mat n) ⊗ₖ K)ᴴ) (i,a) (j,b)=
      ∑ c, ∑ d, K a c*R (i,c) (j,d)*star (K b d) := by
  simp only [Matrix.mul_apply,Matrix.conjTranspose_apply,Fintype.sum_prod_type,
    Matrix.kroneckerMap_apply,Matrix.one_apply,Finset.sum_mul]
  simp only [ite_mul,one_mul,zero_mul]
  simp [apply_ite,Finset.sum_ite_irrel]
  rw [Finset.sum_comm]

omit [DecidableEq r] [DecidableEq q] in
theorem reference_filter (R : Mat (n×r)) (hR : R.PosSemidef) (K : Matrix q r ℂ) :
    L.reference (((1 : Mat n) ⊗ₖ K)*R*((1 : Mat n) ⊗ₖ K)ᴴ)
      (hR.mul_mul_conjTranspose_same ((1 : Mat n) ⊗ₖ K))=
      (L.reference R hR).filter K := by
  apply PositiveMatrixMeasure.eq_of_value
  intro s hs
  ext a b
  rw [reference_value,reference_filter_value]
  simp only [ref_sandwich_entry]

omit [DecidableEq r] in
theorem reference_pure (B : Matrix r n ℂ) :
    L.reference (projector (fun a : n×r => B a.2 a.1)) (Matrix.posSemidef_vecMulVec_self_star _)=L.probe.filter B := by
  rfl

end CPOutcomeLaw
end SecretKey

end

end OAI
