import Mathlib.Algebra.Star.Subalgebra
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases

namespace OAI

namespace Generator.MatrixEncoding

/-! Algebraic encoding of four corner operators by two self-adjoint matrices. -/
section
variable {R : Type*} [Ring R] [StarRing R]
local notation "Mat" => Matrix (Fin 2) (Fin 2) R

def E11 : Mat := !![1, 0; 0, 0]
def E12 : Mat := !![0, 1; 0, 0]
def E21 : Mat := !![0, 0; 1, 0]
def E22 : Mat := !![0, 0; 0, 1]
def corner (a : R) : Mat := !![a, 0; 0, 0]
def encodeA (a₁ a₂ C : R) : Mat := !![a₁, 0; 0, a₂ + C]
def encodeB (a₃ a₄ : R) : Mat := !![a₃, 1; 1, a₄]

theorem encodeA_selfAdjoint {a₁ a₂ C : R}
    (h₁ : IsSelfAdjoint a₁) (h₂ : IsSelfAdjoint a₂) (hC : IsSelfAdjoint C) :
    IsSelfAdjoint (encodeA a₁ a₂ C) := by
  apply Matrix.IsHermitian.isSelfAdjoint
  apply Matrix.IsHermitian.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [encodeA, h₁.star_eq, h₂.star_eq, hC.star_eq]

theorem encodeB_selfAdjoint {a₃ a₄ : R}
    (h₃ : IsSelfAdjoint a₃) (h₄ : IsSelfAdjoint a₄) :
    IsSelfAdjoint (encodeB a₃ a₄) := by
  apply Matrix.IsHermitian.isSelfAdjoint
  apply Matrix.IsHermitian.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [encodeB, h₃.star_eq, h₄.star_eq]

omit [StarRing R] in
theorem complement : (1 : Mat) - E11 = E22 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [E11, E22]

theorem star_E12 : star (E12 : Mat) = E21 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [E12, E21, Matrix.star_apply]

omit [StarRing R] in
theorem cut_offDiagonal (a₃ a₄ : R) : E11 * encodeB a₃ a₄ * E22 = E12 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [E11, E12, E22, encodeB, Matrix.mul_apply, Fin.sum_univ_two]

omit [StarRing R] in
theorem cut_a₁ (a₁ a₂ C : R) : E11 * encodeA a₁ a₂ C * E11 = corner a₁ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [E11, encodeA, corner, Matrix.mul_apply, Fin.sum_univ_two]

omit [StarRing R] in
theorem cut_a₂ (a₁ a₂ C : R) :
    E12 * encodeA a₁ a₂ C * E21 - corner C = corner a₂ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [E12, E21, encodeA, corner]

omit [StarRing R] in
theorem cut_a₃ (a₃ a₄ : R) : E11 * encodeB a₃ a₄ * E11 = corner a₃ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [E11, encodeB, corner, Matrix.mul_apply, Fin.sum_univ_two]

omit [StarRing R] in
theorem cut_a₄ (a₃ a₄ : R) : E12 * encodeB a₃ a₄ * E21 = corner a₄ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [E12, E21, encodeB, corner, Matrix.mul_apply, Fin.sum_univ_two]

omit [StarRing R] in
theorem matrix_reconstruction (X : Mat) :
    X = corner (X 0 0) + corner (X 0 1) * E12 +
      E21 * corner (X 1 0) + E21 * corner (X 1 1) * E12 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [corner, E12, E21]

variable {𝕜 : Type*} [CommRing 𝕜] [StarRing 𝕜] [Algebra 𝕜 R] [StarModule 𝕜 R]

theorem matrix_units_mem (NQ : StarSubalgebra 𝕜 Mat) {a₃ a₄ : R} (hE : (E11 : Mat) ∈ NQ)
    (hB : encodeB a₃ a₄ ∈ NQ) :
    (E22 : Mat) ∈ NQ ∧ (E12 : Mat) ∈ NQ ∧ (E21 : Mat) ∈ NQ := by
  have h22 : (E22 : Mat) ∈ NQ := (complement (R := R)) ▸ sub_mem NQ.one_mem hE
  have h12 : (E12 : Mat) ∈ NQ := cut_offDiagonal a₃ a₄ ▸
    NQ.mul_mem (NQ.mul_mem hE hB) h22
  exact ⟨h22, h12, (star_E12 (R := R)) ▸ star_mem h12⟩

theorem encoded_corners_mem (NQ : StarSubalgebra 𝕜 Mat) {a₁ a₂ a₃ a₄ C : R}
    (hE : (E11 : Mat) ∈ NQ) (hA : encodeA a₁ a₂ C ∈ NQ)
    (hB : encodeB a₃ a₄ ∈ NQ) (hC : corner C ∈ NQ) :
    corner a₁ ∈ NQ ∧ corner a₂ ∈ NQ ∧ corner a₃ ∈ NQ ∧ corner a₄ ∈ NQ := by
  obtain ⟨_, h12, h21⟩ := matrix_units_mem NQ hE hB
  exact ⟨cut_a₁ a₁ a₂ C ▸ NQ.mul_mem (NQ.mul_mem hE hA) hE,
    cut_a₂ a₁ a₂ C ▸ sub_mem (NQ.mul_mem (NQ.mul_mem h12 hA) h21) hC,
    cut_a₃ a₃ a₄ ▸ NQ.mul_mem (NQ.mul_mem hE hB) hE,
    cut_a₄ a₃ a₄ ▸ NQ.mul_mem (NQ.mul_mem h12 hB) h21⟩

omit [StarRing R] [StarRing 𝕜] [StarModule 𝕜 R] in
theorem corner_algebraMap (c : 𝕜) :
    corner (algebraMap 𝕜 R c) = c • (E11 : Mat) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [corner, E11, Algebra.algebraMap_eq_smul_one]

/-- The source's shift C 1_N needs no extra corner-membership hypothesis. -/
theorem encoded_corners_mem_scalar (NQ : StarSubalgebra 𝕜 Mat)
    {a₁ a₂ a₃ a₄ : R} (C : 𝕜)
    (hE : (E11 : Mat) ∈ NQ) (hA : encodeA a₁ a₂ (algebraMap 𝕜 R C) ∈ NQ)
    (hB : encodeB a₃ a₄ ∈ NQ) :
    corner a₁ ∈ NQ ∧ corner a₂ ∈ NQ ∧ corner a₃ ∈ NQ ∧ corner a₄ ∈ NQ := by
  apply encoded_corners_mem NQ hE hA hB
  rw [corner_algebraMap]
  exact NQ.smul_mem hE C

theorem eq_top_of_corner_and_units (NQ : StarSubalgebra 𝕜 Mat) (hc : ∀ a : R, corner a ∈ NQ)
    (h12 : (E12 : Mat) ∈ NQ) (h21 : (E21 : Mat) ∈ NQ) : NQ = ⊤ := by
  apply top_unique
  intro X _
  rw [matrix_reconstruction X]
  exact NQ.add_mem (NQ.add_mem (NQ.add_mem (hc _) (NQ.mul_mem (hc _) h12))
    (NQ.mul_mem h21 (hc _))) (NQ.mul_mem (NQ.mul_mem h21 (hc _)) h12)

end

/-! Algebraic diagonal identities used by the analytic gap recovery. -/
variable {R : Type*} [Ring R] [StarRing R] [Algebra ℂ R] [StarModule ℂ R]

omit [StarRing R] [Algebra ℂ R] [StarModule ℂ R] in
theorem E22_idempotent : (E22 : Matrix (Fin 2) (Fin 2) R)*E22=E22 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [E22]

omit [StarRing R] [Algebra ℂ R] [StarModule ℂ R] in
theorem E22_commute_encodeA (a₁ a₂ : R) : Commute E22 (encodeA a₁ a₂ 0) := by
  show E22*encodeA a₁ a₂ 0=encodeA a₁ a₂ 0*E22
  ext i j
  fin_cases i <;> fin_cases j <;> simp [E22,encodeA]

omit [StarRing R] [StarModule ℂ R] in
theorem encodeA_scalar_shift (a₁ a₂ : R) (C : ℂ) :
    encodeA a₁ a₂ (algebraMap ℂ R C)=C • E22+encodeA a₁ a₂ 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [encodeA,E22,Algebra.algebraMap_eq_smul_one,add_comm]

theorem scalar_shift_selfAdjoint (C : ℝ) : IsSelfAdjoint (algebraMap ℂ R (C : ℂ)) := by
  simp [IsSelfAdjoint,← algebraMap_star_comm]

end Generator.MatrixEncoding

end OAI
