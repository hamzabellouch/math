import OAI.LinearAlgebra.MatrixMultiplication.Tensor.ComplexLocalMaps
import OAI.LinearAlgebra.MatrixMultiplication.Entropy.ComplexOrientationRates
import OAI.LinearAlgebra.MatrixMultiplication.Separation.ComplexRationalTypes
import OAI.LinearAlgebra.MatrixMultiplication.Tensor.ComplexMatrixTensor
import OAI.LinearAlgebra.MatrixMultiplication.Polynomial.ComplexPolynomialWitnessProduct
import OAI.LinearAlgebra.MatrixMultiplication.Polynomial.ComplexPolynomialDegenerationComposition

namespace OAI

/-! Polynomial tensor restrictions and exact coefficient extraction. -/

noncomputable section

namespace MatrixMultiplication.Foundation.PolynomialLocalConstruction

open scoped BigOperators
open Tensor LocalMaps OrientationRates

variable {X Y Z AX AY AZ Label Grade : Type*}
variable [Fintype AX] [Fintype AY] [Fintype AZ]

def kernel {OX OY OZ : Type*}
    (auxiliary : Tensor ℂ AX AY AZ)
    (leftMap : X → OX → AX → Polynomial ℂ)
    (middleMap : Y → OY → AY → Polynomial ℂ)
    (rightMap : Z → OZ → AZ → Polynomial ℂ) :
    Tensor (Polynomial ℂ) (X × OX) (Y × OY) (Z × OZ) :=
  fiberTransform leftMap middleMap rightMap
    (fun x y z => Polynomial.C (auxiliary x.2 y.2 z.2))

def separatedKernel [DecidableEq Label] [DecidableEq Grade]
    {m a b c : ℕ}
    (gradeOf : X → Y → Z → Orientation → Fin m → Grade)
    (word : Label → Orientation → Fin m → Grade) :
    Tensor ℂ (X × (Label × (Fin a × Fin b)))
      (Y × (Label × (Fin b × Fin c))) (Z × (Label × (Fin c × Fin a))) :=
  fun x y z =>
    if x.2.1 = y.2.1 ∧ x.2.1 = z.2.1 ∧
        gradeOf x.1 y.1 z.1 = word x.2.1 then
      matrixCoefficients (Fin a) (Fin b) (Fin c) x.2.2 y.2.2 z.2.2
    else 0

structure Primitive (X Y Z AX AY AZ Label Grade : Type*)
    [Fintype AX] [Fintype AY] [Fintype AZ] [Fintype Grade] [Fintype Label]
    [DecidableEq Label] [DecidableEq Grade] (m a b c : ℕ) where
  length_pos : 0 < m
  leftDim_pos : 0 < a
  middleDim_pos : 0 < b
  rightDim_pos : 0 < c
  labels_nonempty : Nonempty Label
  auxiliary : Tensor ℂ AX AY AZ
  rankBound : ℕ
  auxiliary_rank : RankAtMost auxiliary rankBound
  order : ℕ
  leftDegree : ℕ
  middleDegree : ℕ
  rightDegree : ℕ
  leftMap : X → (Label × (Fin a × Fin b)) → AX → Polynomial ℂ
  middleMap : Y → (Label × (Fin b × Fin c)) → AY → Polynomial ℂ
  rightMap : Z → (Label × (Fin c × Fin a)) → AZ → Polynomial ℂ
  left_degree : ∀ x u i, (leftMap x u i).degree ≤ leftDegree
  middle_degree : ∀ y v j, (middleMap y v j).degree ≤ middleDegree
  right_degree : ∀ z w k, (rightMap z w k).degree ≤ rightDegree
  support : X → Y → Z → Prop
  gradeOf : X → Y → Z → Orientation → Fin m → Grade
  law : RationalLaw Grade
  word : Label → Orientation → Fin m → Grade
  word_injective : Function.Injective word
  exact_type : ∀ label orientation grade,
    (Fintype.card {i // word label orientation i = grade} : ℚ) =
      (m : ℚ) * law.mass grade
  designatedX : Label → X
  designatedY : Label → Y
  designatedZ : Label → Z
  designated_support : ∀ label,
    support (designatedX label) (designatedY label) (designatedZ label)
  designated_word : ∀ label,
    gradeOf (designatedX label) (designatedY label) (designatedZ label) = word label
  vanishes : ∀ x y z, support x.1 y.1 z.1 → ∀ j < order,
    (kernel auxiliary leftMap middleMap rightMap x y z).coeff j = 0
  leading : ∀ x y z, support x.1 y.1 z.1 →
    (kernel auxiliary leftMap middleMap rightMap x y z).coeff order =
      separatedKernel gradeOf word x y z

namespace Primitive

variable [Fintype Grade] [Fintype Label] [DecidableEq Label] [DecidableEq Grade]
variable {m a b c : ℕ}
variable (P : Primitive X Y Z AX AY AZ Label Grade m a b c)

def output (original : Tensor ℂ X Y Z) :
    Tensor ℂ (X × (Label × (Fin a × Fin b)))
      (Y × (Label × (Fin b × Fin c))) (Z × (Label × (Fin c × Fin a))) :=
  originalScale original (separatedKernel P.gradeOf P.word)

theorem designated_injective :
    Function.Injective (fun label =>
      (P.designatedX label, P.designatedY label, P.designatedZ label)) := by
  intro first second h
  apply P.word_injective
  calc
    P.word first = P.gradeOf (P.designatedX first) (P.designatedY first)
        (P.designatedZ first) := (P.designated_word first).symm
    _ = P.gradeOf (P.designatedX second) (P.designatedY second)
        (P.designatedZ second) := congrArg (fun xyz => P.gradeOf xyz.1 xyz.2.1 xyz.2.2) h
    _ = P.word second := P.designated_word second

theorem word_mass_pos (label : Label) (orientation : Orientation) (slot : Fin m) :
    0 < P.law.mass (P.word label orientation slot) := by
  have hcount : 0 < Fintype.card
      {i // P.word label orientation i = P.word label orientation slot} :=
    Fintype.card_pos_iff.mpr ⟨⟨slot, rfl⟩⟩
  have hpositive : (0 : ℚ) <
      (Fintype.card {i // P.word label orientation i = P.word label orientation slot} : ℚ) := by
    exact_mod_cast hcount
  rw [P.exact_type] at hpositive
  by_contra hn
  have hnonpos : P.law.mass (P.word label orientation slot) ≤ 0 := le_of_not_gt hn
  exact (not_lt_of_ge (mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg m) hnonpos)) hpositive

theorem word_allowed (allows : Grade → Prop)
    (outside : ∀ grade, ¬ allows grade → P.law.mass grade = 0)
    (label : Label) (orientation : Orientation) (slot : Fin m) :
    allows (P.word label orientation slot) := by
  by_contra h
  have hp := P.word_mass_pos label orientation slot
  rw [outside _ h] at hp
  exact (lt_irrefl 0) hp

theorem polynomial_substitution (original : Tensor ℂ X Y Z) :
    fiberTransform P.leftMap P.middleMap P.rightMap
      (fun x y z => Polynomial.C (Tensor.product original P.auxiliary x y z)) =
      originalScale (fun x y z => Polynomial.C (original x y z))
        (kernel P.auxiliary P.leftMap P.middleMap P.rightMap) := by
  have h := fiberTransform_originalScale P.leftMap P.middleMap P.rightMap
    (fun x y z => Polynomial.C (original x y z))
    (fun x y z => Polynomial.C (P.auxiliary x.2 y.2 z.2))
  have hinput :
      (fun x y z => Polynomial.C (Tensor.product original P.auxiliary x y z)) =
        originalScale (fun x y z => Polynomial.C (original x y z))
          (fun x y z => Polynomial.C (P.auxiliary x.2 y.2 z.2)) := by
    funext x y z
    simp only [Tensor.product, originalScale, map_mul]
  rw [hinput]
  simpa only [kernel] using h

def InputSupported (original : Tensor ℂ X Y Z) : Prop :=
  ∀ x y z, ¬ P.support x y z → original x y z = 0

variable [Fintype X] [Fintype Y] [Fintype Z]

def degeneration (original : Tensor ℂ X Y Z) (supported : P.InputSupported original) :
    PolynomialRestrictionDegeneration (Tensor.product original P.auxiliary)
      (P.output original) P.order P.leftDegree P.middleDegree P.rightDegree := by
  classical
  refine {
    leftMap := fiberMatrix P.leftMap
    middleMap := fiberMatrix P.middleMap
    rightMap := fiberMatrix P.rightMap
    left_degree := ?_
    middle_degree := ?_
    right_degree := ?_
    vanishes := ?_
    leading := ?_
  }
  · intro x i
    by_cases h : x.1 = i.1
    · simpa only [fiberMatrix, ite_eq_left h] using P.left_degree x.1 x.2 i.2
    · simp only [fiberMatrix, ite_eq_right h, Polynomial.degree_zero]
      exact bot_le
  · intro y j
    by_cases h : y.1 = j.1
    · simpa only [fiberMatrix, ite_eq_left h] using P.middle_degree y.1 y.2 j.2
    · simp only [fiberMatrix, ite_eq_right h, Polynomial.degree_zero]
      exact bot_le
  · intro z k
    by_cases h : z.1 = k.1
    · simpa only [fiberMatrix, ite_eq_left h] using P.right_degree z.1 z.2 k.2
    · simp only [fiberMatrix, ite_eq_right h, Polynomial.degree_zero]
      exact bot_le
  · intro x y z j hj
    rw [← fiberTransform_eq_restrict, P.polynomial_substitution]
    simp only [originalScale, Polynomial.coeff_C_mul]
    by_cases hs : P.support x.1 y.1 z.1
    · rw [P.vanishes x y z hs j hj, mul_zero]
    · rw [supported x.1 y.1 z.1 hs, zero_mul]
  · intro x y z
    rw [← fiberTransform_eq_restrict, P.polynomial_substitution]
    simp only [originalScale, Polynomial.coeff_C_mul, output]
    by_cases hs : P.support x.1 y.1 z.1
    · rw [P.leading x y z hs]
    · rw [supported x.1 y.1 z.1 hs]
      simp only [zero_mul]

def DesignatedCoefficients (original : Tensor ℂ X Y Z) : Prop :=
  ∀ label, original (P.designatedX label) (P.designatedY label)
    (P.designatedZ label) = 1

omit [Fintype X] [Fintype Y] [Fintype Z] in
theorem output_pullback (original : Tensor ℂ X Y Z)
    (coefficients : P.DesignatedCoefficients original) :
    Tensor.pullback
      (fun u : Label × (Fin a × Fin b) => (P.designatedX u.1, u))
      (fun v : Label × (Fin b × Fin c) => (P.designatedY v.1, v))
      (fun w : Label × (Fin c × Fin a) => (P.designatedZ w.1, w))
      (P.output original) =
      Tensor.directSum (fun _ : Label =>
        matrixCoefficients (K := ℂ) (Fin a) (Fin b) (Fin c)) := by
  funext x y z
  by_cases h : x.1 = y.1 ∧ x.1 = z.1
  · have hy : y.1 = x.1 := h.1.symm
    have hz : z.1 = x.1 := h.2.symm
    have hc : original (P.designatedX x.1) (P.designatedY x.1)
        (P.designatedZ x.1) = 1 := coefficients x.1
    simp only [Tensor.pullback, output, originalScale, separatedKernel,
      Tensor.directSum, hy, hz, P.designated_word, hc, and_true, ite_true, one_mul]
  · have hn : ¬ (x.1 = y.1 ∧ x.1 = z.1 ∧
        P.gradeOf (P.designatedX x.1) (P.designatedY y.1) (P.designatedZ z.1) =
          P.word x.1) := by
      intro hs
      exact h ⟨hs.1, hs.2.1⟩
    simp only [Tensor.pullback, output, originalScale, separatedKernel,
      Tensor.directSum, ite_eq_right hn, ite_eq_right h, mul_zero]

def terminalApproximation {original : Tensor ℂ X Y Z} {r d D : ℕ}
    (source : PolynomialApproximation original r d D)
    (supported : P.InputSupported original)
    (coefficients : P.DesignatedCoefficients original) :
    PolynomialApproximation
      (Tensor.directSum (fun _ : Label =>
        matrixCoefficients (K := ℂ) (Fin a) (Fin b) (Fin c)))
      (r * P.rankBound) (d * (P.order + 1) + P.order)
      (D * (P.order + 1) + P.leftDegree + P.middleDegree + P.rightDegree) := by
  have combined := source.productExact P.auxiliary P.rankBound P.auxiliary_rank
  have transformed := (P.degeneration original supported).compose combined
  have selected := transformed.pullback
    (fun u : Label × (Fin a × Fin b) => (P.designatedX u.1, u))
    (fun v : Label × (Fin b × Fin c) => (P.designatedY v.1, v))
    (fun w : Label × (Fin c × Fin a) => (P.designatedZ w.1, w))
  rw [P.output_pullback original coefficients] at selected
  exact selected

end Primitive
end MatrixMultiplication.Foundation.PolynomialLocalConstruction

end

end OAI
