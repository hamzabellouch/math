import OAI.Probability.InvariantIsing.Cavity.CavityReservoirFrame

namespace OAI

/-! Reservoir rotations fix the physical cavity columns exactly. -/

noncomputable section
open scoped BigOperators Matrix

namespace InvariantIsing

def cavityReservoirRotation {N n : ℕ} (V : Orthogonal N) : Orthogonal (N + n) := by
  let D : Matrix (Fin N ⊕ Fin n) (Fin N ⊕ Fin n) ℝ :=
    Matrix.fromBlocks (V : Matrix (Fin N) (Fin N) ℝ) 0 0 1
  let e : Fin N ⊕ Fin n ≃ Fin (N + n) := finSumFinEquiv
  refine ⟨D.submatrix e.symm e.symm, (Matrix.mem_orthogonalGroup_iff' _ ℝ).mpr ?_⟩
  change D.transpose.submatrix e.symm e.symm * D.submatrix e.symm e.symm = 1
  rw [Matrix.submatrix_mul_equiv]
  have hD : D.transpose * D = 1 := by
    have hV := (Matrix.mem_orthogonalGroup_iff' (Fin N) ℝ).mp V.property
    simp only [D, Matrix.fromBlocks_transpose, Matrix.transpose_zero, Matrix.transpose_one,
      Matrix.fromBlocks_multiply, hV, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
      Matrix.one_mul, Matrix.fromBlocks_one]
  rw [hD, Matrix.submatrix_one_equiv]

lemma cavityReservoirRotation_last {N n : ℕ} (V : Orthogonal N)
    (i : Fin (N + n)) (j : Fin n) :
    (cavityReservoirRotation (n := n) V : Matrix (Fin (N + n)) (Fin (N + n)) ℝ)
      i (Fin.natAdd N j) = if i = Fin.natAdd N j then 1 else 0 := by
  obtain ⟨a, rfl⟩ := (finSumFinEquiv : Fin N ⊕ Fin n ≃ Fin (N + n)).surjective i
  cases a with
  | inl i =>
    have hij : i.castAdd n ≠ Fin.natAdd N j := by
      intro h
      have hh := congrArg (finSumFinEquiv.symm : Fin (N + n) → Fin N ⊕ Fin n) h
      simp only [finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_natAdd] at hh
      cases hh
    simp [cavityReservoirRotation, Matrix.submatrix_apply, Matrix.fromBlocks, hij]
  | inr i =>
    simp [cavityReservoirRotation, Matrix.submatrix_apply, Matrix.fromBlocks, Matrix.one_apply]

lemma cavityReservoirRotation_first {N n : ℕ} (V : Orthogonal N)
    (i j : Fin N) :
    (cavityReservoirRotation (n := n) V : Matrix (Fin (N + n)) (Fin (N + n)) ℝ)
      (i.castAdd n) (j.castAdd n) = (V : Matrix (Fin N) (Fin N) ℝ) i j := by
  simp [cavityReservoirRotation, Matrix.submatrix_apply, Matrix.fromBlocks]

lemma cavityReservoirRotation_lowerLeft {N n : ℕ} (V : Orthogonal N)
    (i : Fin n) (j : Fin N) :
    (cavityReservoirRotation (n := n) V : Matrix (Fin (N + n)) (Fin (N + n)) ℝ)
      (Fin.natAdd N i) (j.castAdd n) = 0 := by
  simp [cavityReservoirRotation, Matrix.submatrix_apply, Matrix.fromBlocks]

lemma cavityReservoirRotation_conjugate {N n : ℕ} (V : Orthogonal N)
    (J : Matrix (Fin (N + n)) (Fin (N + n)) ℝ) :
    ((cavityReservoirRotation (n := n) V : Matrix (Fin (N + n)) (Fin (N + n)) ℝ).transpose *
      J * (cavityReservoirRotation (n := n) V : Matrix (Fin (N + n)) (Fin (N + n)) ℝ)).submatrix
        (Fin.castAdd n) (Fin.castAdd n) =
      (V : Matrix (Fin N) (Fin N) ℝ).transpose *
        J.submatrix (Fin.castAdd n) (Fin.castAdd n) * (V : Matrix (Fin N) (Fin N) ℝ) := by
  ext i j
  change (∑ k : Fin (N + n), (∑ l : Fin (N + n),
    (cavityReservoirRotation (n := n) V : Matrix (Fin (N + n)) (Fin (N + n)) ℝ)
      l (i.castAdd n) * J l k) *
    (cavityReservoirRotation (n := n) V : Matrix (Fin (N + n)) (Fin (N + n)) ℝ)
      k (j.castAdd n)) =
    ∑ k : Fin N, (∑ l : Fin N, (V : Matrix (Fin N) (Fin N) ℝ) l i *
      J (l.castAdd n) (k.castAdd n)) * (V : Matrix (Fin N) (Fin N) ℝ) k j
  simp only [Fin.sum_univ_add, cavityReservoirRotation_first,
    cavityReservoirRotation_lowerLeft, zero_mul, mul_zero, Finset.sum_const_zero, add_zero]

lemma cavityReservoirRotation_cavityColumns {N n : ℕ}
    (U : Matrix (Fin (N + n)) (Fin (N + n)) ℝ) (V : Orthogonal N) :
    (fun (i : Fin (N + n)) (j : Fin n) => (U *
      (cavityReservoirRotation (n := n) V : Matrix (Fin (N + n)) (Fin (N + n)) ℝ))
        i (Fin.natAdd N j)) =
      fun i j => U i (Fin.natAdd N j) := by
  ext i j
  simp only [Matrix.mul_apply, cavityReservoirRotation_last, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]

end InvariantIsing

end

end OAI
