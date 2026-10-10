import OAI.Analysis.GroupDeterminants.DefectProjections

namespace OAI

noncomputable section
open scoped BigOperators Pointwise

namespace GroupRingDeterminant
open LampDraft LampProjectionDraft
variable {H d : Type} [Group H] [Fintype d] [DecidableEq d]

lemma lamp_projection_data (X Y : Matrix d d (MonoidAlgebra (ZMod 2) H))
    (hXY : X * Y = 1) (hYX : Y * X ≠ 1) :
    ∃ (D : ℕ), Odd D ∧ ∃ P : Matrix (d ⊕ Unit) (d ⊕ Unit) (MonoidAlgebra ℚ (LampGroup H)),
      P * P = P ∧ IsSelfAdjoint P ∧ (Fintype.card d : ℚ) < ∑ i, (P i i).coeff 1 ∧
      ∃ Z : Matrix (d ⊕ Unit) (d ⊕ Unit) (MonoidAlgebra ℤ (LampGroup H)),
        Z.map toRat = (D : ℚ) • P ∧
        ∃ u : Matrix (d ⊕ Unit) d (MonoidAlgebra (ZMod 2) (LampGroup H)),
        ∃ v : Matrix d (d ⊕ Unit) (MonoidAlgebra (ZMod 2) (LampGroup H)),
          u * v = Z.map (toMod 2) := by
  classical
  obtain ⟨S, hS, u, v, huv⟩ := binary_defect_factorization_lamp X Y hXY hYX
  let p := projection H S
  let D := denominator H S
  let P : Matrix (d ⊕ Unit) (d ⊕ Unit) (MonoidAlgebra ℚ (LampGroup H)) :=
    Matrix.fromBlocks 1 0 0 (Matrix.diagonal (fun _ : Unit => p))
  let Z : Matrix (d ⊕ Unit) (d ⊕ Unit) (MonoidAlgebra ℤ (LampGroup H)) :=
    Matrix.fromBlocks ((D : ℤ) • 1) 0 0 (Matrix.diagonal (fun _ : Unit => numerator H S))
  have hp : p * p = p := (projection_idempotent H S).eq
  have hps : star p = p := (projection_selfAdjoint H S).star_eq
  refine ⟨D, denominator_odd H S, P, ?_, ?_, ?_, Z, ?_, u, v, ?_⟩
  · dsimp only [P]
    rw [Matrix.fromBlocks_multiply]
    simp only [Matrix.one_mul, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
      Matrix.diagonal_mul_diagonal, hp]
  · change Matrix.conjTranspose P = P
    dsimp only [P]
    rw [Matrix.fromBlocks_conjTranspose]
    simp only [Matrix.conjTranspose_one, Matrix.conjTranspose_zero, Matrix.diagonal_conjTranspose]
    congr 2
    funext i
    exact hps
  · have he : (∑ i, (P i i).coeff 1) = (Fintype.card d : ℚ) + (p.coeff 1) := by
      simp [P, Fintype.sum_sum_type]
    rw [he, lt_add_iff_pos_right]
    rw [show p = projection H S from rfl, projection_trace H S hS]
    positivity
  · apply Matrix.ext
    intro i j
    rcases i with i | i <;> rcases j with j | j
    · change fullIntToRat H (((D : ℤ) • (1 : Matrix d d _)) i j) =
        (D : ℚ) • (1 : Matrix d d _) i j
      rw [show (((D : ℤ) • (1 : Matrix d d _)) i j) = (D : ℤ) • ((1 : Matrix d d _) i j) from rfl,
        fullIntToRat_zsmul]
      simp [Matrix.one_apply]
    · simp [Z, P, Matrix.map_apply]
    · simp [Z, P, Matrix.map_apply]
    · cases i; cases j
      exact numerator_toRat H S
  · rw [huv]
    apply Matrix.ext
    intro i j
    rcases i with i | i <;> rcases j with j | j
    · change (1 : Matrix d d _) i j = fullIntToBin H (((D : ℤ) • (1 : Matrix d d _)) i j)
      rw [show (((D : ℤ) • (1 : Matrix d d _)) i j) = (D : ℤ) • ((1 : Matrix d d _) i j) from rfl,
        fullIntToBin_zsmul]
      simp [Matrix.one_apply, (denominator_odd H S).natCast_zmod_two, D]
    · simp [Z, Matrix.map_apply, Matrix.fromBlocks]
    · simp [Z, Matrix.map_apply, Matrix.fromBlocks]
    · cases i; cases j
      rfl

end GroupRingDeterminant

end

end OAI
