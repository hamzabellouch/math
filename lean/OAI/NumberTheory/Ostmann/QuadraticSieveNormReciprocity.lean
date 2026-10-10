import OAI.NumberTheory.Ostmann.QuadraticSieveDuality

namespace OAI

namespace Ostmann.QuadraticSieve

noncomputable def finiteCoefficients (S : Finset ℕ) (b : S → ℂ) (n : ℕ) : ℂ := by
  classical
  exact if hn : n ∈ S then b ⟨n, hn⟩ else 0

@[simp] theorem finiteCoefficients_apply (S : Finset ℕ) (b : S → ℂ) (n : S) :
    finiteCoefficients S b n = b n := by
  classical
  simp [finiteCoefficients, n.property]

theorem coefficientEnergy_finiteCoefficients (S : Finset ℕ) (b : S → ℂ) :
    coefficientEnergy S (finiteCoefficients S b) = ∑ s : S, ‖b s‖ ^ 2 := by
  unfold coefficientEnergy
  rw [← Finset.sum_coe_sort S]
  simp only [finiteCoefficients_apply]

noncomputable def jacobiMatrix (V S : Finset ℕ) : Matrix V S ℂ :=
  fun v s => (jacobiSym (s.val : ℤ) v.val : ℂ)

theorem matrixEnergy_jacobiMatrix (V S : Finset ℕ) (a : ℕ → ℂ) :
    matrixEnergy (jacobiMatrix V S) (fun s : S => a s) = jacobiEnergy V S a := by
  unfold matrixEnergy jacobiMatrix jacobiEnergy
  rw [← Finset.sum_coe_sort V]
  apply Finset.sum_congr rfl
  intro v hv
  rw [← Finset.sum_coe_sort S]
  congr 2
  apply Finset.sum_congr rfl
  intro s hs
  ring

theorem matrixEnergy_jacobiMatrix_adjoint (V S : Finset ℕ) (b : V → ℂ) :
    matrixEnergy (jacobiMatrix V S).conjTranspose b =
      numeratorEnergy 1 S V (finiteCoefficients V b) := by
  unfold matrixEnergy jacobiMatrix numeratorEnergy
  rw [← Finset.sum_coe_sort S]
  apply Finset.sum_congr rfl
  intro s hs
  rw [← Finset.sum_coe_sort V]
  congr 2
  apply Finset.sum_congr rfl
  intro v hv
  simp only [finiteCoefficients_apply, one_mul]
  change star (jacobiSym (s.val : ℤ) v.val : ℂ) * b v =
    b v * (jacobiSym (s.val : ℤ) v.val : ℂ)
  rw [star_intCast]
  ring

theorem quadraticNorm_le_two_swap (V S : Finset ℕ)
    (hV : ∀ v ∈ V, Odd v) (hS : ∀ s ∈ S, Odd s) :
    quadraticNorm V S ≤ 2 * quadraticNorm S V := by
  classical
  have hK : 0 ≤ 2 * quadraticNorm S V := mul_nonneg (by norm_num) (quadraticNorm_nonneg S V)
  have htrans : ∀ b : V → ℂ,
      matrixEnergy (jacobiMatrix V S).conjTranspose b ≤
        (2 * quadraticNorm S V) * ∑ v : V, ‖b v‖ ^ 2 := by
    intro b
    rw [matrixEnergy_jacobiMatrix_adjoint]
    rw [← coefficientEnergy_finiteCoefficients V b]
    exact numeratorEnergy_le_of_unsigned S V (finiteCoefficients V b) 1 hS hV
      (quadraticNorm_nonneg S V) (jacobiEnergy_le_quadraticNorm S V)
  apply quadraticNorm_le_of_bound V S hK
  intro a
  have ht := matrix_energy_duality (jacobiMatrix V S).conjTranspose hK htrans
    (fun s : S => a s)
  rw [Matrix.conjTranspose_conjTranspose, matrixEnergy_jacobiMatrix] at ht
  rw [coefficientEnergy, ← Finset.sum_coe_sort S]
  exact ht

end Ostmann.QuadraticSieve

end OAI
