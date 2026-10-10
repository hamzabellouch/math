import OAI.LinearAlgebra.MatrixMultiplication.ComplexBounds.CW75ReorderedExecution
import OAI.LinearAlgebra.MatrixMultiplication.Separation.ExecutionApproximation

namespace OAI

/-! Explicit complex square and rectangular matrix multiplication bounds. -/

noncomputable section

namespace MatrixMultiplication.CW75ReorderedFinite

open MatrixMultiplication.Foundation CW75LabelHierarchy StageHierarchyResources
open ExecutionPairingBudget CW75ReorderedWords CW75ReorderedExecution ComplexWitness
open scoped BigOperators Classical

attribute [local irreducible] CW75LabelHierarchy.retainedWords

def blocks (counts : Scalar → ℕ) (t : ℕ) : ℕ := t * ∑ a, counts a

def copies (counts : Scalar → ℕ) (t : ℕ) : ℕ :=
  Fintype.card (ExactWords (fun a => t * counts a))

def rows (counts : Scalar → ℕ) (t : ℕ) : ℕ := (realize counts t).shape.rows
def inner (counts : Scalar → ℕ) (t : ℕ) : ℕ := (realize counts t).shape.inner
def columns (counts : Scalar → ℕ) (t : ℕ) : ℕ := (realize counts t).shape.columns

def rankBudget (counts : Scalar → ℕ) (t : ℕ) : ℕ :=
  27 ^ blocks counts t * stageAuxiliaryBudget counts curveLabels 5 t

def order (counts : Scalar → ℕ) (t : ℕ) : ℕ :=
  6 * blocks counts t * ((realize counts t).execution.order + 1) +
    (realize counts t).execution.order

def degree (counts : Scalar → ℕ) (t : ℕ) : ℕ :=
  18 * blocks counts t * ((realize counts t).execution.order + 1) +
    (realize counts t).execution.leftDegree +
    (realize counts t).execution.middleDegree +
    (realize counts t).execution.rightDegree

def sourceApproximation (counts : Scalar → ℕ) (t : ℕ) :
    Tensor.PolynomialApproximation (CW75InitialExecution.fullSource (blocks counts t))
      (27 ^ blocks counts t) (6 * blocks counts t) (18 * blocks counts t) := by
  simpa only [CW75InitialExecution.fullSource, show (3 : ℕ) ^ 3 = 27 by norm_num,
    show (2 : ℕ) * 3 = 6 by norm_num, show (6 : ℕ) * 3 = 18 by norm_num] using
    (CoppersmithWinograd.approximation.power 3).power (blocks counts t)

def labelEquiv (counts : Scalar → ℕ) (t : ℕ) :
    Fin (copies counts t) ≃ Prefix counts t 5 :=
  Fintype.equivOfCardEq ((Fintype.card_fin (copies counts t)).trans
    (realize_label_card counts t).symm)

def designatedX {counts : Scalar → ℕ} {t : ℕ} (p : Prefix counts t 5) :
    Coordinate counts t := longX (terminalWord p).val

def designatedY {counts : Scalar → ℕ} {t : ℕ} (p : Prefix counts t 5) :
    Coordinate counts t := longY (terminalWord p).val

def designatedZ {counts : Scalar → ℕ} {t : ℕ} (p : Prefix counts t 5) :
    Coordinate counts t := longZ (terminalWord p).val

theorem designated_coefficient_one (counts : Scalar → ℕ) (t : ℕ)
    (p : Prefix counts t 5) :
    CW75InitialExecution.fullSource (blocks counts t)
      (designatedX p) (designatedY p) (designatedZ p) = 1 := by
  unfold CW75InitialExecution.fullSource Tensor.power
  apply Finset.prod_eq_one
  intro i _
  apply Finset.prod_eq_one
  intro j _
  have hs := CW75Primitive.original_support _ _ _
    (coefficient_ne_zero ((terminalWord p).val i)) j
  simp only [CoppersmithWinograd.tensor, designatedX, designatedY, designatedZ,
    longX, longY, longZ]
  exact ite_eq_left hs

def leftSelect (counts : Scalar → ℕ) (t : ℕ)
    (u : Fin (copies counts t) × (Fin (rows counts t) × Fin (inner counts t))) :
    Coordinate counts t × (Prefix counts t 5 × (realize counts t).PX) :=
  (designatedX (labelEquiv counts t u.1),
    (labelEquiv counts t u.1, (realize counts t).shape.left.symm u.2))

def middleSelect (counts : Scalar → ℕ) (t : ℕ)
    (v : Fin (copies counts t) × (Fin (inner counts t) × Fin (columns counts t))) :
    Coordinate counts t × (Prefix counts t 5 × (realize counts t).PY) :=
  (designatedY (labelEquiv counts t v.1),
    (labelEquiv counts t v.1, (realize counts t).shape.middle.symm v.2))

def rightSelect (counts : Scalar → ℕ) (t : ℕ)
    (w : Fin (copies counts t) × (Fin (columns counts t) × Fin (rows counts t))) :
    Coordinate counts t × (Prefix counts t 5 × (realize counts t).PZ) :=
  (designatedZ (labelEquiv counts t w.1),
    (labelEquiv counts t w.1, (realize counts t).shape.right.symm w.2))

theorem selected_output (counts : Scalar → ℕ) (t : ℕ) :
    Tensor.pullback (leftSelect counts t) (middleSelect counts t) (rightSelect counts t)
      (LocalMaps.originalScale (CW75InitialExecution.fullSource (blocks counts t))
        (realize counts t).execution.value) =
      Tensor.directSum (fun _ : Fin (copies counts t) =>
        Tensor.matrixCoefficients (K := ℂ) (Fin (rows counts t))
          (Fin (inner counts t)) (Fin (columns counts t))) := by
  funext u v w
  simp only [Tensor.pullback, LocalMaps.originalScale, leftSelect, middleSelect, rightSelect]
  rw [realize_value]
  simp only [MatrixCoordinates.tensor, Tensor.pullback]
  by_cases h : u.1 = v.1 ∧ u.1 = w.1
  · have hv : v.1 = u.1 := h.1.symm
    have hw : w.1 = u.1 := h.2.symm
    have hc := designated_coefficient_one counts t (labelEquiv counts t u.1)
    simp only [designatedX, designatedY, designatedZ] at hc
    simp only [hv, hw, designatedX, designatedY, designatedZ, hc,
      Tensor.directSum, true_and, ite_true, one_mul]
    simp only [rows, inner, columns,
      (realize counts t).shape.left.apply_symm_apply u.2,
      (realize counts t).shape.middle.apply_symm_apply v.2,
      (realize counts t).shape.right.apply_symm_apply w.2]
    unfold Tensor.matrixCoefficients
    split_ifs <;> rfl
  · have hn : ¬ (labelEquiv counts t u.1 = labelEquiv counts t v.1 ∧
        labelEquiv counts t u.1 = labelEquiv counts t w.1 ∧
        designatedX (labelEquiv counts t u.1) =
          longX (terminalWord (labelEquiv counts t u.1)).val ∧
        designatedY (labelEquiv counts t v.1) =
          longY (terminalWord (labelEquiv counts t u.1)).val ∧
        designatedZ (labelEquiv counts t w.1) =
          longZ (terminalWord (labelEquiv counts t u.1)).val) := by
      intro he
      exact h ⟨(labelEquiv counts t).injective he.1,
        (labelEquiv counts t).injective he.2.1⟩
    simp only [Tensor.directSum, ite_eq_right h, ite_eq_right hn, mul_zero]

def approximation (counts : Scalar → ℕ) (t : ℕ) :
    Tensor.PolynomialApproximation
      (Tensor.directSum (fun _ : Fin (copies counts t) =>
        Tensor.matrixCoefficients (K := ℂ) (Fin (rows counts t))
          (Fin (inner counts t)) (Fin (columns counts t))))
      (rankBudget counts t) (order counts t) (degree counts t) := by
  have supported : ∀ x y z : Coordinate counts t,
      ¬ CW75InitialExecution.support x y z →
        CW75InitialExecution.fullSource (blocks counts t) x y z = 0 := by
    intro x y z hs
    exact not_ne_iff.mp hs
  have full := ExecutionApproximation.approximation (realize counts t).execution
    (sourceApproximation counts t) supported
  have selected := full.pullback (leftSelect counts t) (middleSelect counts t)
    (rightSelect counts t)
  rw [selected_output] at selected
  simpa only [rankBudget, order, degree, realize_rankBound] using selected

theorem dimensions_positive (counts : Scalar → ℕ) (t : ℕ) :
    0 < rows counts t ∧ 0 < inner counts t ∧ 0 < columns counts t :=
  (realize counts t).shape_positive

theorem volume_eq_copies (counts : Scalar → ℕ) (t : ℕ) :
    rows counts t * inner counts t * columns counts t = copies counts t :=
  realize_volume counts t

theorem rows_pos (counts : Scalar → ℕ) (t : ℕ) : 0 < rows counts t :=
  (dimensions_positive counts t).1

theorem inner_pos (counts : Scalar → ℕ) (t : ℕ) : 0 < inner counts t :=
  (dimensions_positive counts t).2.1

theorem columns_pos (counts : Scalar → ℕ) (t : ℕ) : 0 < columns counts t :=
  (dimensions_positive counts t).2.2

theorem copies_pos (counts : Scalar → ℕ) (t : ℕ) : 0 < copies counts t := by
  rw [← volume_eq_copies]
  exact Nat.mul_pos (Nat.mul_pos (rows_pos counts t) (inner_pos counts t))
    (columns_pos counts t)

theorem rankBudget_pos (counts : Scalar → ℕ) (t : ℕ) : 0 < rankBudget counts t := by
  apply Nat.mul_pos (pow_pos (by decide) _)
  rw [← realize_rankBound]
  exact lt_of_lt_of_le (by
    change 0 < rows counts t * inner counts t * columns counts t
    rw [volume_eq_copies]
    exact copies_pos counts t) (realize_pairing_budget counts t)

theorem dimensions_eq_pairingSize (counts : Scalar → ℕ) (t : ℕ) :
    rows counts t =
        ConditionalLabels.stagePairingSize counts curveLabels 5 curveReaderPair .xz t ∧
    inner counts t =
        ConditionalLabels.stagePairingSize counts curveLabels 5 curveReaderPair .xy t ∧
    columns counts t =
        ConditionalLabels.stagePairingSize counts curveLabels 5 curveReaderPair .yz t :=
  realize_dimensions counts t

theorem rank_power (counts : Scalar → ℕ) (t n : ℕ) :
    Tensor.RankAtMost
      (Tensor.power (Tensor.directSum (fun _ : Fin (copies counts t) =>
        Tensor.matrixCoefficients (K := ℂ) (Fin (rows counts t))
          (Fin (inner counts t)) (Fin (columns counts t)))) n)
      ((degree counts t * n + 1) * rankBudget counts t ^ n) :=
  (approximation counts t).rank_power n

end MatrixMultiplication.CW75ReorderedFinite

end

end OAI
