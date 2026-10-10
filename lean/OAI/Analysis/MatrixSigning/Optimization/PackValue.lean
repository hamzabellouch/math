import Mathlib
import OAI.Analysis.MatrixSigning.Potential.SchurBlock
import OAI.Analysis.MatrixSigning.Optimization.ComplexValueProgram

namespace OAI

open Matrix

namespace CurrentKS.RationalSDP
noncomputable section
open CurrentKS.Hermitian CurrentKS.HermitianCoordinates CurrentKS.Variational Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d : ℕ}

def packValue (z : Point d) : EuclideanSpace ℝ (Fin (valueDimension d)) := WithLp.toLp 2 fun k =>
  match (valueIndex d).symm k with
  | .inl _ => z.1
  | .inr (.inl ij) => encode z.2.1 ij
  | .inr (.inr ij) => encode z.2.2 ij

def unpackValue (v : EuclideanSpace ℝ (Fin (valueDimension d))) : Point d :=
  (timeCoordinate d v,assemble (WithLp.toLp 2 (matrixCoordinate d false v)),
    assemble (WithLp.toLp 2 (matrixCoordinate d true v)))

lemma time_packValue (z : Point d) : timeCoordinate d (packValue z) = z.1 := by
  simp [timeCoordinate,packValue]
lemma matrix_packValue (z : Point d) (second : Bool) :
    matrixCoordinate d second (packValue z) = encode (if second then z.2.2 else z.2.1) := by
  funext ij
  cases second <;> simp [matrixCoordinate,packValue]
lemma unpack_packValue (z : Point d) : unpackValue (packValue z)=z := by
  simp only [unpackValue,time_packValue,matrix_packValue,Bool.false_eq_true,ite_false,ite_true]
  change (z.1,assemble (extract z.2.1),assemble (extract z.2.2))=z
  rw [assemble_extract,assemble_extract]
lemma pack_unpackValue (v : EuclideanSpace ℝ (Fin (valueDimension d))) :
    packValue (unpackValue v)=v := by
  ext k
  obtain ⟨j,rfl⟩ := (valueIndex d).surjective k
  rcases j with j | (ij | ij)
  · have hj : j=0 := Subsingleton.elim _ _
    subst j
    simp [packValue,unpackValue,timeCoordinate]
  · have he := congrArg (fun w : Space d => w ij)
      (extract_assemble (WithLp.toLp 2 (matrixCoordinate d false v)))
    simpa [packValue,unpackValue,matrixCoordinate,extract] using he
  · have he := congrArg (fun w : Space d => w ij)
      (extract_assemble (WithLp.toLp 2 (matrixCoordinate d true v)))
    simpa [packValue,unpackValue,matrixCoordinate,extract] using he

lemma complexValueProgram_iff (ε : ℝ) (S : H d) (η : H d →L[ℝ] H d)
    (ηm : Mat d → Mat d) (hηm : ∀ W : H d,ηm W=(η W : Mat d)) (z : Point d) :
    complexValueProgram ε S ηm z.1 z.2.1 z.2.2 ↔ z ∈ valueSpectrahedron ε S η := by
  have ho (A B : H d) : ((B : Mat d)-A).PosSemidef ↔ A ≤ B := by
    change ((B-A : H d) : Mat d).PosSemidef ↔ _
    rw [← mem_psdCone,mem_psd_iff_nonneg,sub_nonneg]
  simp only [complexValueProgram,hηm]
  change (valueBlock₁ S η z).PosSemidef ∧ (valueBlock₂ S η z).PosSemidef ∧
    ((z.2.1 : Mat d)-((1/400:ℝ) • Hermitian.one : H d)).PosSemidef ∧
    (((200/ε:ℝ) • Hermitian.one : H d)- (z.2.1 : Mat d)).PosSemidef ∧
    ((z.2.2 : Mat d)-((1/400:ℝ) • Hermitian.one : H d)).PosSemidef ∧
    (((200/ε:ℝ) • Hermitian.one : H d)- (z.2.2 : Mat d)).PosSemidef ∧
    0 ≤ z.1 ∧ z.1 ≤ 100 ↔ _
  rw [ho,ho,ho,ho]
  simp only [valueSpectrahedron,Set.mem_ofPred_eq,oracleBox,Set.mem_Icc]
  tauto

lemma matrixCoordinate_norm (v : EuclideanSpace ℝ (Fin (valueDimension d))) (s : Bool) :
    ‖(WithLp.toLp 2 (matrixCoordinate d s v) : Space d)‖ ≤ ((d:ℝ)^2+1)*‖v‖ := by
  have he (ij : Fin d × Fin d) : ‖matrixCoordinate d s v ij‖ ≤ ‖v‖ := by
    exact PiLp.norm_apply_le _ _
  have hs := Finset.sum_le_sum (fun ij (_ : ij ∈ (Finset.univ : Finset (Fin d × Fin d))) =>
    sq_le_sq₀ (norm_nonneg _) (norm_nonneg _) |>.mpr (he ij))
  have hh : ‖(WithLp.toLp 2 (matrixCoordinate d s v) : Space d)‖^2 ≤ (d:ℝ)^2*‖v‖^2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_prod,Fintype.card_fin,
      nsmul_eq_mul,Nat.cast_mul,pow_two] using hs
  have hd : 0 ≤ (d:ℝ)^2 := sq_nonneg _
  have hb : (d:ℝ)^2 ≤ ((d:ℝ)^2+1)^2 := by nlinarith
  have hb' := mul_le_mul_of_nonneg_right hb (sq_nonneg ‖v‖)
  have hp : 0 ≤ ((d:ℝ)^2+1)*‖v‖ := by positivity
  nlinarith [norm_nonneg (WithLp.toLp 2 (matrixCoordinate d s v) : Space d)]

end
end CurrentKS.RationalSDP

end OAI
