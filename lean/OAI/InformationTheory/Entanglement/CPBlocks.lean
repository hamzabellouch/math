import OAI.InformationTheory.Entanglement.PositiveBlock

namespace OAI

noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder Kronecker
open Matrix
namespace SecretKey
open ChannelCompletion TensorCriterion
variable {n m : Type} [Fintype n] [Fintype m] [DecidableEq m]

omit [Fintype m] [DecidableEq m] in
lemma cp_pure_block {F : Map n m} (hF : CP F) (u v : n → ℂ) :
    (fromBlocks (F (projector u)) (F (vecMulVec u (star v)))
      (F (vecMulVec u (star v)))ᴴ (F (projector v))).PosSemidef := by
  let x : Bool × n → ℂ := fun p => if p.1 then v p.2 else u p.2
  have h := hF Bool (projector x) (Matrix.posSemidef_vecMulVec_self_star x)
  let e : m ⊕ m → Bool × m := Sum.elim (fun i => (false,i)) (fun i => (true,i))
  have he : (amplify F (projector x)).submatrix e e =
      fromBlocks (F (projector u)) (F (vecMulVec u (star v)))
      (F (vecMulVec u (star v)))ᴴ (F (projector v)) := by
    ext i j
    cases i with
    | inl i => cases j <;> rfl
    | inr i => cases j with
      | inr j => rfl
      | inl j =>
        exact (h.isHermitian.apply (true,i) (false,j)).symm
  rw [← he]
  exact h.submatrix e

lemma cp_filtered_bound {F : Map n m} (hF : CP F) (u v : n → ℂ)
    (S T : Mat m) :
    traceNorm (S * F (vecMulVec u (star v)) * Tᴴ) ≤
      Real.sqrt ((Matrix.trace (S * F (projector u) * Sᴴ)).re *
        (Matrix.trace (T * F (projector v) * Tᴴ)).re) := by
  have h := (cp_pure_block hF u v).mul_mul_conjTranspose_same (fromBlocks S 0 0 T)
  simp only [Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_zero,
    Matrix.fromBlocks_multiply,Matrix.mul_zero,Matrix.zero_mul,add_zero,zero_add] at h
  apply positive_block
  convert h using 1
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]

lemma cp_filtered_reverse {F : Map n m} (hF : CP (F.comp transposeMap)) (u v : n → ℂ)
    (S T : Mat m) :
    traceNorm (S * F (vecMulVec u (star v)) * Tᴴ) ≤
      Real.sqrt ((Matrix.trace (S * F (projector v) * Sᴴ)).re *
        (Matrix.trace (T * F (projector u) * Tᴴ)).re) := by
  have he (u v : n → ℂ) : (vecMulVec (star v) (star (star u)))ᵀ = vecMulVec u (star v) := by
    ext i j
    simp [Matrix.vecMulVec_apply,Pi.star_apply,mul_comm]
  have h := cp_filtered_bound hF (star v) (star u) S T
  simpa only [LinearMap.comp_apply,transposeMap_apply,projector,he] using h

lemma trace_filter {D : Mat m} (hD : D.PosSemidef) (A : Mat m) :
    Matrix.trace (CFC.sqrt D * A * (CFC.sqrt D)ᴴ) = Matrix.trace (D*A) := by
  rw [(Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg D)).isHermitian.eq,
    Matrix.trace_mul_cycle, CFC.sqrt_mul_sqrt_self _ hD.nonneg]

lemma trace_psd_product_nonneg {A D : Mat m} (hA : A.PosSemidef) (hD : D.PosSemidef) :
    0 ≤ (Matrix.trace (D*A)).re := by
  rw [← trace_filter hD]
  exact (Complex.nonneg_iff.mp (hA.mul_mul_conjTranspose_same _).trace_nonneg).1

lemma cp_effect_direct {F : Map n m} (hF : CP F) (u v : n → ℂ)
    {D E : Mat m} (hD : D.PosSemidef) (hE : E.PosSemidef) :
    traceNorm (CFC.sqrt D * F (vecMulVec u (star v)) * CFC.sqrt E) ≤
      Real.sqrt ((Matrix.trace (D*F (projector u))).re * (Matrix.trace (E*F (projector v))).re) := by
  have h := cp_filtered_bound hF u v (CFC.sqrt D) (CFC.sqrt E)
  rw [trace_filter hD,trace_filter hE,
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg E)).isHermitian.eq] at h
  exact h

lemma cp_effect_reverse {F : Map n m} (hF : CP (F.comp transposeMap)) (u v : n → ℂ)
    {D E : Mat m} (hD : D.PosSemidef) (hE : E.PosSemidef) :
    traceNorm (CFC.sqrt D * F (vecMulVec u (star v)) * CFC.sqrt E) ≤
      Real.sqrt ((Matrix.trace (D*F (projector v))).re * (Matrix.trace (E*F (projector u))).re) := by
  have h := cp_filtered_reverse hF u v (CFC.sqrt D) (CFC.sqrt E)
  rw [trace_filter hD,trace_filter hE,
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg E)).isHermitian.eq] at h
  exact h
end SecretKey

end

end OAI
