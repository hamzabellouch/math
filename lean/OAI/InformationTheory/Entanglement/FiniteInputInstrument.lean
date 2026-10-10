import OAI.InformationTheory.Entanglement.DefaultNull
import OAI.InformationTheory.Entanglement.ChoiTransfer

namespace OAI

noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder MeasureTheory Kronecker
open MeasureTheory Matrix
namespace SecretKey
open ChannelCompletion TensorCriterion
variable {Ω : Type*} [MeasurableSpace Ω]
variable {n e d : Type} [Fintype n] [Fintype e] [Fintype d]
  [DecidableEq n] [DecidableEq e] [DecidableEq d]

structure FiniteInputInstrument (n : Type) [Fintype n] (Ω : Type*) [MeasurableSpace Ω] where
  law : Mat n →ₗ[ℂ] ComplexMeasure Ω
  positive : ∀ (r : Type) [Fintype r] (A : Mat (r×n)), A.PosSemidef →
    ∀ s, MeasurableSet s → Matrix.PosSemidef (fun a b => law (fun i j => A (a,i) (b,j)) s)
  total : ∀ A, law A Set.univ=Matrix.trace A
namespace FiniteInputInstrument
variable (I : FiniteInputInstrument n Ω)

def referenceLaw (A : Mat (e×n)) (hA : A.PosSemidef) : PositiveMatrixMeasure Ω e where
  entry a b := I.law (fun i j => A (a,i) (b,j))
  positive s hs := I.positive e A hA s hs

def purificationLaw (B : Matrix e n ℂ) : PositiveMatrixMeasure Ω e :=
  I.referenceLaw (projector (fun p : e×n => B p.1 p.2)) (Matrix.posSemidef_vecMulVec_self_star _)

def rawProbe : PositiveMatrixMeasure Ω n :=
  I.referenceLaw (projector (omega (n := n))) (Matrix.posSemidef_vecMulVec_self_star _)
lemma rawProbe_entry (a b : n) : I.rawProbe.entry a b=I.law (Matrix.single a b 1) := by
  change I.law (fun i j => projector (omega (n := n)) (a,i) (b,j))=_
  rw [show (fun i j => projector (omega (n := n)) (a,i) (b,j))=Matrix.single a b 1 from omega_block a b]
lemma law_entries (A : Mat n) :
    I.law A=∑ i, ∑ j, A i j • I.law (Matrix.single i j 1) := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single A]
  simp only [map_sum,← map_smul]
  simp

omit [DecidableEq e] in
theorem purificationLaw_eq_filter (B : Matrix e n ℂ) :
    I.purificationLaw B=I.rawProbe.filter B := by
  apply PositiveMatrixMeasure.ext_entry_default
  funext a b
  change I.law (fun i j => B a i*star (B b j))=
    ∑ i, ∑ j, (B a i*star (B b j)) • I.rawProbe.entry i j
  erw [I.law_entries]
  simp only [I.rawProbe_entry]
omit [DecidableEq n] [DecidableEq e] in
lemma purificationLaw_total (B : Matrix e n ℂ) :
    (I.purificationLaw B).value Set.univ=B*Bᴴ := by
  ext a b
  change I.law (fun i j => B a i*star (B b j)) Set.univ=_
  erw [I.total]
  simp only [Matrix.trace,Matrix.diag,Matrix.mul_apply,Matrix.conjTranspose_apply]
lemma rawProbe_total : I.rawProbe.value Set.univ=1 := by
  ext a b
  change I.rawProbe.entry a b Set.univ=_
  erw [I.rawProbe_entry,I.total]
  by_cases h : a=b
  · subst b; simp [Matrix.trace, Matrix.diag, Matrix.single_apply]
  · simp [Matrix.trace, Matrix.diag, Matrix.single_apply,h,Ne.symm h]

theorem rawProbe_test (E : Mat n) (s : Set Ω) :
    Matrix.trace (E*I.rawProbe.value s)=I.law Eᵀ s := by
  erw [I.law_entries]
  simp only [_root_.sum_apply,_root_.smul_apply,smul_eq_mul]
  simp only [Matrix.trace,Matrix.diag,Matrix.mul_apply,PositiveMatrixMeasure.value,
    I.rawProbe_entry,Matrix.transpose_apply]
  rw [Finset.sum_comm]

omit [DecidableEq e] [DecidableEq d] in
theorem referenceLaw_conjugation (A : Mat (e×n)) (hA : A.PosSemidef)
    (B : Matrix d e ℂ) :
    I.referenceLaw ((B ⊗ₖ (1 : Mat n))*A*(B ⊗ₖ (1 : Mat n))ᴴ)
      (hA.mul_mul_conjTranspose_same _)=(I.referenceLaw A hA).filter B := by
  apply PositiveMatrixMeasure.ext_entry_default
  funext a b
  change I.law (fun i j => ((B ⊗ₖ (1 : Mat n))*A*(B ⊗ₖ (1 : Mat n))ᴴ) (a,i) (b,j))=
    ∑ u, ∑ v, (B a u*star (B b v)) • I.law (fun i j => A (u,i) (v,j))
  have hEntry : (fun i j => ((B ⊗ₖ (1 : Mat n))*A*(B ⊗ₖ (1 : Mat n))ᴴ) (a,i) (b,j))=
      ∑ u, ∑ v, (B a u*star (B b v)) • (fun i j => A (u,i) (v,j)) := by
    ext i j
    simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
    simp only [Matrix.mul_apply,Matrix.conjTranspose_apply,Matrix.kroneckerMap_apply,
      Matrix.one_apply,Fintype.sum_prod_type,
      mul_one,mul_zero,ite_mul,zero_mul,apply_ite,star_zero]
    simp only [Finset.sum_ite_eq,Finset.mem_univ,ite_true,Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro u hu
    apply Finset.sum_congr rfl
    intro v hv
    ring
  erw [hEntry,map_sum]
  apply Finset.sum_congr rfl
  intro u hu
  erw [map_sum]
  apply Finset.sum_congr rfl
  intro v hv
  exact I.law.map_smul _ _

end FiniteInputInstrument
end SecretKey

end

end OAI
