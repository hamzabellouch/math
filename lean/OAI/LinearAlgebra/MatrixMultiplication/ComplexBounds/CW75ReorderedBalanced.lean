import OAI.LinearAlgebra.MatrixMultiplication.Tensor.MatrixBalancing
import OAI.LinearAlgebra.MatrixMultiplication.ComplexBounds.CW75ReorderedFinite

namespace OAI

/-! Explicit complex square and rectangular matrix multiplication bounds. -/

noncomputable section

namespace MatrixMultiplication.CW75ReorderedBalanced

open MatrixMultiplication.Foundation CW75LabelHierarchy MatrixBalancing

def witness (counts : Scalar → ℕ) (t : ℕ) : ComplexWitness.FiniteRectangularWitness where
  outer := CW75ReorderedFinite.rows counts t * CW75ReorderedFinite.inner counts t
  inner := CW75ReorderedFinite.columns counts t ^ 2
  multiplicity := CW75ReorderedFinite.copies counts t ^ 2
  rank := CW75ReorderedFinite.rankBudget counts t ^ 2
  outer_pos := Nat.mul_pos (CW75ReorderedFinite.rows_pos counts t)
    (CW75ReorderedFinite.inner_pos counts t)
  inner_pos := pow_pos (CW75ReorderedFinite.columns_pos counts t) 2
  multiplicity_pos := pow_pos (CW75ReorderedFinite.copies_pos counts t) 2
  rank_pos := pow_pos (CW75ReorderedFinite.rankBudget_pos counts t) 2
  order := 2 * CW75ReorderedFinite.order counts t
  degree := 2 * CW75ReorderedFinite.degree counts t
  approximation := finiteBalanced (CW75ReorderedFinite.approximation counts t)

@[simp] theorem witness_outer (counts : Scalar → ℕ) (t : ℕ) :
    (witness counts t).outer =
      CW75ReorderedFinite.rows counts t * CW75ReorderedFinite.inner counts t := rfl

@[simp] theorem witness_inner (counts : Scalar → ℕ) (t : ℕ) :
    (witness counts t).inner = CW75ReorderedFinite.columns counts t ^ 2 := rfl

@[simp] theorem witness_multiplicity (counts : Scalar → ℕ) (t : ℕ) :
    (witness counts t).multiplicity = CW75ReorderedFinite.copies counts t ^ 2 := rfl

@[simp] theorem witness_rank (counts : Scalar → ℕ) (t : ℕ) :
    (witness counts t).rank = CW75ReorderedFinite.rankBudget counts t ^ 2 := rfl

theorem witness_volume (counts : Scalar → ℕ) (t : ℕ) :
    (witness counts t).outer ^ 2 * (witness counts t).inner =
      (witness counts t).multiplicity := by
  simp only [witness_outer, witness_inner, witness_multiplicity, ← mul_pow,
    CW75ReorderedFinite.volume_eq_copies]

theorem witness_dimensions (counts : Scalar → ℕ) (t : ℕ) :
    (witness counts t).outer =
        ConditionalLabels.stagePairingSize counts ComplexWitness.curveLabels 5
            ComplexWitness.curveReaderPair .xz t *
          ConditionalLabels.stagePairingSize counts ComplexWitness.curveLabels 5
            ComplexWitness.curveReaderPair .xy t ∧
    (witness counts t).inner =
        ConditionalLabels.stagePairingSize counts ComplexWitness.curveLabels 5
            ComplexWitness.curveReaderPair .yz t ^ 2 := by
  rcases CW75ReorderedFinite.dimensions_eq_pairingSize counts t with ⟨hr, hi, hc⟩
  simp only [witness_outer, witness_inner, hr, hi, hc, and_self]

end MatrixMultiplication.CW75ReorderedBalanced

end

end OAI
