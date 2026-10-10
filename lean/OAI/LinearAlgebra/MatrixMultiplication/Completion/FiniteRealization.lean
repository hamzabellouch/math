import OAI.LinearAlgebra.MatrixMultiplication.Completion.Scripts
import OAI.LinearAlgebra.MatrixMultiplication.Completion.Execution
import OAI.LinearAlgebra.MatrixMultiplication.Separation.ExecutionApproximation
import OAI.LinearAlgebra.MatrixMultiplication.Tensor.ComplexExecutionPairingBudget
import OAI.LinearAlgebra.MatrixMultiplication.Separation.ComplexFiniteMMRealization

namespace OAI

/-! Readable tensor completion and its finite arithmetic realization. -/

noncomputable section

namespace MatrixMultiplication.CompletionFiniteRealization

open MatrixMultiplication.Foundation RecursiveCompletion
open scoped BigOperators Classical

theorem power_coefficient_one {X Y Z : Type*} (T : Tensor ℂ X Y Z)
    (unit : ∀ x y z, T x y z ≠ 0 → T x y z = 1) (n : ℕ)
    (x : Fin n → X) (y : Fin n → Y) (z : Fin n → Z)
    (supported : Tensor.power T n x y z ≠ 0) : Tensor.power T n x y z = 1 := by
  apply Finset.prod_eq_one
  intro i hi
  exact unit _ _ _ ((Finset.prod_ne_zero_iff.mp supported) i hi)

theorem complete_coefficient_one {X Y Z : Type*} (S : FlaggedTensor X Y Z)
    (unit : ∀ x y z, S.tensor x y z ≠ 0 → S.tensor x y z = 1)
    (center : Color) (m : ℕ) (x : Fin m → X) (y : Fin m → Y) (z : Fin m → Z)
    (supported : (complete S center m).tensor x y z ≠ 0) :
    (complete S center m).tensor x y z = 1 := by
  rw [complete_tensor] at supported ⊢
  split_ifs at supported ⊢ with hweight
  · exact power_coefficient_one S.tensor unit m x y z supported
  · exact False.elim (supported rfl)

theorem script_coefficient_one {X Y Z : Type*} (S : FlaggedTensor X Y Z)
    (unit : ∀ x y z, S.tensor x y z ≠ 0 → S.tensor x y z = 1) (s : Script) :
    ∀ x y z, (s.tensor S).tensor x y z ≠ 0 → (s.tensor S).tensor x y z = 1 := by
  induction s with
  | base => exact unit
  | step prior center m ih => exact complete_coefficient_one (prior.tensor S) ih center m

def scriptSourceApproximation {X Y Z : Type*}
    [Fintype X] [Fintype Y] [Fintype Z] (S : FlaggedTensor X Y Z) {d D : ℕ}
    (source : Tensor.PolynomialApproximation S.tensor 3 d D) (s : Script) (blocks : ℕ) :
    Tensor.PolynomialApproximation (Tensor.power (s.tensor S).tensor blocks)
      (3 ^ (s.factors * blocks)) (s.order d * blocks) (s.degree D * blocks) := by
  simpa only [pow_mul] using (s.approximation S source).power blocks

open CompletionHierarchyWords CompletionExecution ExecutionPairingBudget

variable {A X Y Z : Type} [Fintype A]
variable (H : ReadableHierarchy A X Y Z) (counts : A → ℕ) (t : ℕ)

def blocks : ℕ := t * ∑ a, counts a

def copies : ℕ := Fintype.card (Prefix H counts t H.depth)

def rows : ℕ := (realize H counts t).shape.rows
def inner : ℕ := (realize H counts t).shape.inner
def columns : ℕ := (realize H counts t).shape.columns

def order (d : ℕ) : ℕ :=
  d * blocks counts t * ((realize H counts t).execution.order + 1) +
    (realize H counts t).execution.order

def degree (D : ℕ) : ℕ :=
  D * blocks counts t * ((realize H counts t).execution.order + 1) +
    (realize H counts t).execution.leftDegree +
    (realize H counts t).execution.middleDegree +
    (realize H counts t).execution.rightDegree

def labelEquiv : Fin (copies H counts t) ≃ Prefix H counts t H.depth :=
  (Fintype.equivFin _).symm

variable (complete : Function.Injective (labelRecordOf H.labels H.depth))

def designatedX (p : Prefix H counts t H.depth) : Coordinate X counts t :=
  longX H (terminalWord H complete p).val

def designatedY (p : Prefix H counts t H.depth) : Coordinate Y counts t :=
  longY H (terminalWord H complete p).val

def designatedZ (p : Prefix H counts t H.depth) : Coordinate Z counts t :=
  longZ H (terminalWord H complete p).val

theorem leading_shape
    (x : Coordinate X counts t × (Prefix H counts t H.depth × (realize H counts t).PX))
    (y : Coordinate Y counts t × (Prefix H counts t H.depth × (realize H counts t).PY))
    (z : Coordinate Z counts t × (Prefix H counts t H.depth × (realize H counts t).PZ)) :
    (realize H counts t).execution.value x y z =
      if x.2.1 = y.2.1 ∧ x.2.1 = z.2.1 ∧
        x.1 = designatedX H counts t complete x.2.1 ∧
        y.1 = designatedY H counts t complete x.2.1 ∧
        z.1 = designatedZ H counts t complete x.2.1
      then (realize H counts t).shape.tensor x.2.2 y.2.2 z.2.2 else 0 := by
  rw [(realize H counts t).normal]
  simp only [prefixValue, terminal_eligible_iff H complete,
    designatedX, designatedY, designatedZ]
  rfl

def leftSelect
    (u : Fin (copies H counts t) × (Fin (rows H counts t) × Fin (inner H counts t))) :
    Coordinate X counts t × (Prefix H counts t H.depth × (realize H counts t).PX) :=
  (designatedX H counts t complete (labelEquiv H counts t u.1),
    (labelEquiv H counts t u.1, (realize H counts t).shape.left.symm u.2))

def middleSelect
    (v : Fin (copies H counts t) × (Fin (inner H counts t) × Fin (columns H counts t))) :
    Coordinate Y counts t × (Prefix H counts t H.depth × (realize H counts t).PY) :=
  (designatedY H counts t complete (labelEquiv H counts t v.1),
    (labelEquiv H counts t v.1, (realize H counts t).shape.middle.symm v.2))

def rightSelect
    (w : Fin (copies H counts t) × (Fin (columns H counts t) × Fin (rows H counts t))) :
    Coordinate Z counts t × (Prefix H counts t H.depth × (realize H counts t).PZ) :=
  (designatedZ H counts t complete (labelEquiv H counts t w.1),
    (labelEquiv H counts t w.1, (realize H counts t).shape.right.symm w.2))

theorem designated_coefficient_one (T : Tensor ℂ X Y Z)
    (unit : ∀ a, T (H.x a) (H.y a) (H.z a) = 1)
    (p : Prefix H counts t H.depth) :
    Tensor.power T (blocks counts t) (designatedX H counts t complete p)
      (designatedY H counts t complete p) (designatedZ H counts t complete p) = 1 := by
  apply Finset.prod_eq_one
  intro i _
  exact unit ((terminalWord H complete p).val i)

theorem selected_output (T : Tensor ℂ X Y Z)
    (unit : ∀ a, T (H.x a) (H.y a) (H.z a) = 1) :
    Tensor.pullback (leftSelect H counts t complete) (middleSelect H counts t complete)
      (rightSelect H counts t complete)
      (LocalMaps.originalScale (Tensor.power T (blocks counts t))
        (realize H counts t).execution.value) =
      Tensor.directSum (fun _ : Fin (copies H counts t) =>
        Tensor.matrixMultiplication (rows H counts t) (inner H counts t) (columns H counts t)) := by
  funext u v w
  simp only [Tensor.pullback, LocalMaps.originalScale, leftSelect, middleSelect, rightSelect]
  rw [leading_shape H counts t complete]
  simp only [MatrixCoordinates.tensor, Tensor.pullback]
  by_cases h : u.1 = v.1 ∧ u.1 = w.1
  · have hv : v.1 = u.1 := h.1.symm
    have hw : w.1 = u.1 := h.2.symm
    simp only [hv, hw, designated_coefficient_one H counts t complete T unit,
      Tensor.directSum, true_and, ite_true, one_mul,
      Tensor.matrixMultiplication_eq_matrixCoefficients, rows, inner, columns]
    rw [(realize H counts t).shape.left.apply_symm_apply u.2,
      (realize H counts t).shape.middle.apply_symm_apply v.2,
      (realize H counts t).shape.right.apply_symm_apply w.2]
  · have hn : ¬ (labelEquiv H counts t u.1 = labelEquiv H counts t v.1 ∧
        labelEquiv H counts t u.1 = labelEquiv H counts t w.1 ∧
        True ∧
        designatedY H counts t complete (labelEquiv H counts t v.1) =
          designatedY H counts t complete (labelEquiv H counts t u.1) ∧
        designatedZ H counts t complete (labelEquiv H counts t w.1) =
          designatedZ H counts t complete (labelEquiv H counts t u.1)) := by
      intro he
      exact h ⟨(labelEquiv H counts t).injective he.1,
        (labelEquiv H counts t).injective he.2.1⟩
    simp only [Tensor.directSum, ite_eq_right h, ite_eq_right hn, mul_zero]

theorem dimensions_positive :
    0 < rows H counts t ∧ 0 < inner H counts t ∧ 0 < columns H counts t :=
  (realize H counts t).shape_positive

include complete in
theorem volume_eq_copies :
    rows H counts t * inner H counts t * columns H counts t = copies H counts t :=
  (realize_volume H counts t complete).trans (realize_label_card H counts t complete).symm

include complete in
theorem copies_pos : 0 < copies H counts t := by
  rw [← volume_eq_copies H counts t complete]
  exact Nat.mul_pos (Nat.mul_pos (dimensions_positive H counts t).1
    (dimensions_positive H counts t).2.1) (dimensions_positive H counts t).2.2

theorem auxiliaryRank_pos : 0 < (realize H counts t).execution.rankBound :=
  lt_of_lt_of_le
    (Nat.mul_pos (Nat.mul_pos (dimensions_positive H counts t).1
      (dimensions_positive H counts t).2.1) (dimensions_positive H counts t).2.2)
    (realize H counts t).pairing_budget

variable [Fintype X] [Fintype Y] [Fintype Z]

def sourceApproximation {T : Tensor ℂ X Y Z} {factors d D : ℕ}
    (source : Tensor.PolynomialApproximation T (3 ^ factors) d D) :
    Tensor.PolynomialApproximation (Tensor.power T (blocks counts t))
      (3 ^ (factors * blocks counts t)) (d * blocks counts t) (D * blocks counts t) := by
  simpa only [pow_mul] using source.power (blocks counts t)

def approximation {T : Tensor ℂ X Y Z} {factors d D : ℕ}
    (source : Tensor.PolynomialApproximation T (3 ^ factors) d D)
    (supported : ∀ x y z, T x y z ≠ 0 → ∃ a, H.x a = x ∧ H.y a = y ∧ H.z a = z)
    (unit : ∀ a, T (H.x a) (H.y a) (H.z a) = 1) :
    Tensor.PolynomialApproximation
      (Tensor.directSum (fun _ : Fin (copies H counts t) =>
        Tensor.matrixMultiplication (rows H counts t) (inner H counts t) (columns H counts t)))
      (3 ^ (factors * blocks counts t) * (realize H counts t).execution.rankBound)
      (order H counts t d) (degree H counts t D) := by
  have hs : ∀ x y z, ¬ support H counts t x y z →
      Tensor.power T (blocks counts t) x y z = 0 := by
    intro x y z outside
    by_contra nonzero
    apply outside
    intro i
    exact supported _ _ _ ((Finset.prod_ne_zero_iff.mp nonzero) i (Finset.mem_univ i))
  have full := ExecutionApproximation.approximation (realize H counts t).execution
    (sourceApproximation counts t source) hs
  have selected := full.pullback (leftSelect H counts t complete)
    (middleSelect H counts t complete) (rightSelect H counts t complete)
  rw [selected_output H counts t complete T unit] at selected
  exact selected

def realization {T : Tensor ℂ X Y Z} {factors d D : ℕ}
    (source : Tensor.PolynomialApproximation T (3 ^ factors) d D)
    (supported : ∀ x y z, T x y z ≠ 0 → ∃ a, H.x a = x ∧ H.y a = y ∧ H.z a = z)
    (unit : ∀ a, T (H.x a) (H.y a) (H.z a) = 1)
    (factors_pos : 0 < factors) (blocks_pos : 0 < blocks counts t) : FiniteMMRealization where
  occurrences := factors * blocks counts t
  multiplicity := copies H counts t
  auxiliaryRank := (realize H counts t).execution.rankBound
  rows := rows H counts t
  inner := inner H counts t
  columns := columns H counts t
  occurrences_pos := Nat.mul_pos factors_pos blocks_pos
  multiplicity_pos := copies_pos H counts t complete
  auxiliaryRank_pos := auxiliaryRank_pos H counts t
  rows_pos := (dimensions_positive H counts t).1
  inner_pos := (dimensions_positive H counts t).2.1
  columns_pos := (dimensions_positive H counts t).2.2
  order := order H counts t d
  degree := degree H counts t D
  approximation := approximation H counts t complete source supported unit

section Projections

variable {T : Tensor ℂ X Y Z} {factors d D : ℕ}
variable (source : Tensor.PolynomialApproximation T (3 ^ factors) d D)
variable (supported : ∀ x y z, T x y z ≠ 0 →
  ∃ a, H.x a = x ∧ H.y a = y ∧ H.z a = z)
variable (unit : ∀ a, T (H.x a) (H.y a) (H.z a) = 1)
variable (factors_pos : 0 < factors) (blocks_pos : 0 < blocks counts t)

@[simp] theorem realization_occurrences :
    (realization H counts t complete source supported unit factors_pos blocks_pos).occurrences =
      factors * blocks counts t := rfl

@[simp] theorem realization_multiplicity :
    (realization H counts t complete source supported unit factors_pos blocks_pos).multiplicity =
      copies H counts t := rfl

@[simp] theorem realization_auxiliaryRank :
    (realization H counts t complete source supported unit factors_pos blocks_pos).auxiliaryRank =
      StageHierarchyResources.stageAuxiliaryBudget counts H.labels H.depth t :=
  realize_rankBound H counts t

@[simp] theorem realization_rows :
    (realization H counts t complete source supported unit factors_pos blocks_pos).rows =
      rows H counts t := rfl

@[simp] theorem realization_inner :
    (realization H counts t complete source supported unit factors_pos blocks_pos).inner =
      inner H counts t := rfl

@[simp] theorem realization_columns :
    (realization H counts t complete source supported unit factors_pos blocks_pos).columns =
      columns H counts t := rfl

@[simp] theorem realization_volume :
    (realization H counts t complete source supported unit factors_pos blocks_pos).rates.volume =
      copies H counts t :=
  volume_eq_copies H counts t complete

end Projections

end MatrixMultiplication.CompletionFiniteRealization

end

end OAI
