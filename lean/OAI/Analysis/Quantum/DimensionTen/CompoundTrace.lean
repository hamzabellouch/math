import OAI.Analysis.Quantum.DimensionTen.TensorSymmetry
import OAI.Analysis.Quantum.DimensionTen.Veronese
import OAI.Analysis.Quantum.DimensionTen.MinorData

namespace OAI

section
noncomputable section
open scoped Matrix Kronecker ComplexOrder
open Matrix
namespace DimensionTen

def compound (B : Mat 4) : Mat 6 := fun i j =>
  B (exteriorPairs i).1 (exteriorPairs j).1 * B (exteriorPairs i).2 (exteriorPairs j).2 -
  B (exteriorPairs i).1 (exteriorPairs j).2 * B (exteriorPairs i).2 (exteriorPairs j).1

lemma exterior_left_entry {r : Type*} (X : Matrix (Fin 4 × Fin 4) r ℂ)
    (i : Fin 6) (j : r) :
    (exteriorIsometryᴴ * X) i j =
      (X (exteriorPairs i) j - X ((exteriorPairs i).2, (exteriorPairs i).1) j) /
        (Real.sqrt 2 : ℂ) := by
  rw [exteriorIsometry_real]
  simp [Matrix.mul_apply, Matrix.transpose_apply, exteriorIsometry,
    div_eq_mul_inv, mul_sub, Finset.sum_sub_distrib,
    mul_ite, Prod.mk.eta, mul_comm]

lemma exterior_right_entry {r : Type*} (X : Matrix r (Fin 4 × Fin 4) ℂ)
    (i : r) (j : Fin 6) :
    (X * exteriorIsometry) i j =
      (X i (exteriorPairs j) - X i ((exteriorPairs j).2, (exteriorPairs j).1)) /
        (Real.sqrt 2 : ℂ) := by
  simp [Matrix.mul_apply, exteriorIsometry, div_eq_mul_inv, sub_mul, mul_sub,
    Finset.sum_sub_distrib, ite_mul, mul_ite, Prod.mk.eta]

lemma exterior_compression_entry (X : Matrix (Fin 4 × Fin 4) (Fin 4 × Fin 4) ℂ)
    (i j : Fin 6) :
    (exteriorIsometryᴴ * X * exteriorIsometry) i j =
      (X (exteriorPairs i) (exteriorPairs j) -
       X ((exteriorPairs i).2, (exteriorPairs i).1) (exteriorPairs j) -
       X (exteriorPairs i) ((exteriorPairs j).2, (exteriorPairs j).1) +
       X ((exteriorPairs i).2, (exteriorPairs i).1)
         ((exteriorPairs j).2, (exteriorPairs j).1)) / 2 := by
  rw [exterior_right_entry, exterior_left_entry, exterior_left_entry]
  field_simp [sqrtTwo_ne]
  ring_nf
  rw [sqrtTwo_sq]

lemma exterior_compound (B : Mat 4) :
    exteriorIsometryᴴ * (B ⊗ₖ B) * exteriorIsometry = compound B := by
  ext i j
  rw [exterior_compression_entry]
  simp only [Matrix.kroneckerMap_apply, compound]
  ring

end DimensionTen

end
end

section
noncomputable section
open scoped Matrix Kronecker ComplexOrder
open Matrix
namespace DimensionTen

def complementaryIndex : Fin 6 → Fin 6 := ![5,4,3,2,1,0]
def complementarySign : Fin 6 → ℂ := ![1,-1,1,1,-1,1]

lemma hodgeComplement_adjoint : hodgeComplementᴴ = hodgeComplement := by
  ext i j
  change star (hodgeComplement j i) = hodgeComplement i j
  fin_cases i <;> fin_cases j <;> norm_num [hodgeComplement]

lemma hodge_mul_entry (A : Mat 6) (i j : Fin 6) :
    (hodgeComplement * A) i j = complementarySign i * A (complementaryIndex i) j := by
  change (∑ k : Fin 6, hodgeComplement i k * A k j) = _
  fin_cases i <;> simp [Fin.sum_univ_succ, hodgeComplement,
    complementarySign, complementaryIndex]

lemma mul_hodge_entry (A : Mat 6) (i j : Fin 6) :
    (A * hodgeComplement) i j = complementarySign j * A i (complementaryIndex j) := by
  change (∑ k : Fin 6, A i k * hodgeComplement k j) = _
  fin_cases j <;> simp [Fin.sum_univ_succ, hodgeComplement,
    complementarySign, complementaryIndex]

lemma compound_trace (B : Mat 4) :
    Matrix.trace (hodgeComplement * (compound B)ᵀ * hodgeComplementᴴ * compound B) =
      6 * B.det := by
  rw [hodgeComplement_adjoint, Border.det_four]
  change (∑ i : Fin 6, ∑ j : Fin 6,
    (hodgeComplement * (compound B)ᵀ * hodgeComplement) i j * compound B j i) = _
  simp only [mul_hodge_entry, hodge_mul_entry, Matrix.transpose_apply]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  dsimp [compound, exteriorPairs, TensorCriterion.altPair, complementaryIndex, complementarySign]
  ring

end DimensionTen

end
end

end OAI
