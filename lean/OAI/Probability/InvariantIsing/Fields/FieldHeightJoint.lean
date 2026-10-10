import OAI.Probability.InvariantIsing.Fields.FieldFiniteNeighborhood
import OAI.Probability.InvariantIsing.Fields.FieldHeightUpdate

namespace OAI

/-! The literal field-height chart as a finite joint affine covariance
recursion. No admissibility proof is built into this chart. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped BigOperators NNReal

namespace InvariantIsing

def fieldHeightSlope {n : ℕ} (j : Fin (n + 1)) (i : Fin (n + 1)) : ℝ :=
  (if i = j then 1 else 0) -
    if hj : j.val = 0 then 0 else if i = (⟨j.val - 1, by omega⟩ : Fin (n + 1)) then 1 else 0

lemma fieldHeightSlope_variance {n : ℕ} (j : Fin (n + 1)) (r : Fin (n + 1) → ℝ) :
    fieldFiniteVariance 0 (fieldHeightSlope j) r = fieldHeightIncrement r j := by
  classical
  unfold fieldFiniteVariance fieldHeightSlope fieldHeightIncrement
  rw [zero_add]
  simp only [sub_mul, Finset.sum_sub_distrib]
  by_cases hj : j.val = 0
  · simp [hj]
  · simp [hj]

def fieldHeightFiniteStep (h : FieldStep) (j : Fin (h.depth + 1)) : FieldFiniteStep (h.depth + 1) where
  base := 0
  slope := fieldHeightSlope j
  exponent := h.cut j.castSucc

def fieldHeightFiniteList (h : FieldStep) : List (FieldFiniteStep (h.depth + 1)) :=
  List.ofFn (fieldHeightFiniteStep h)

lemma fieldFiniteValue_scalar_list {n : ℕ} (L : List (FieldFiniteStep n))
    (r : Fin n → ℝ) (z : ℝ) :
    fieldFiniteValue L (r, z) =
      fieldScalarValue (L.map (fun av =>
        (av.exponent, Real.toNNReal (fieldFiniteVariance av.base av.slope r))))
        (fun y => Real.log (Real.cosh y)) z := by
  induction L generalizing z with
  | nil => rfl
  | cons av L ih =>
    change gaussianTransform (fieldFiniteVariance av.base av.slope r) av.exponent
      (fun y => fieldFiniteValue L (r, y)) z =
      gaussianOperator av.exponent (Real.toNNReal (fieldFiniteVariance av.base av.slope r))
        (fieldScalarValue (L.map fun bv =>
          (bv.exponent, Real.toNNReal (fieldFiniteVariance bv.base bv.slope r)))
          (fun y => Real.log (Real.cosh y))) z
    rw [gaussianOperator_toNNReal]
    rw [field_gaussianTransform_eq_operator]
    rw [gaussianOperator_toNNReal]
    congr 2
    funext y
    exact ih y

def fieldHeightJointValue (h : FieldStep) (r : Fin (h.depth + 1) → ℝ) (z : ℝ) : ℝ :=
  fieldFiniteValue (fieldHeightFiniteList h) (r, z) - r (Fin.last h.depth) / 2

lemma fieldHeightJointValue_scalar (h : FieldStep) (r : Fin (h.depth + 1) → ℝ) (z : ℝ) :
    fieldHeightJointValue h r z =
      fieldScalarValue (List.ofFn fun j : Fin (h.depth + 1) =>
        (h.cut j.castSucc, Real.toNNReal (fieldHeightIncrement r j)))
        (fun y => Real.log (Real.cosh y)) z - r (Fin.last h.depth) / 2 := by
  unfold fieldHeightJointValue
  rw [fieldFiniteValue_scalar_list]
  congr 2
  rw [fieldHeightFiniteList, List.map_ofFn]
  apply congrArg List.ofFn
  funext j
  change (h.cut j.castSucc, Real.toNNReal (fieldFiniteVariance 0 (fieldHeightSlope j) r)) = _
  rw [fieldHeightSlope_variance]

lemma fieldHeightJointValue_update (h : FieldStep) (i : Fin (h.depth + 1)) (t z : ℝ) :
    fieldHeightJointValue h (Function.update h.height i (h.height i + t)) z =
      fieldHeightCoordinateValue h i t z :=
  fieldHeightJointValue_scalar h _ z

lemma fieldHeightJointValue_eq_fieldValue (h : FieldStep)
    (r : Fin (h.depth + 1) → ℝ) (hr0 : ∀ i, 0 ≤ r i) (hrmono : Monotone r) (z : ℝ) :
    fieldHeightJointValue h r z = fieldValue (fieldWithHeights h r hr0 hrmono) z := by
  let k := fieldWithHeights h r hr0 hrmono
  have he : (List.ofFn fun j : Fin (h.depth + 1) =>
      (h.cut j.castSucc, Real.toNNReal (fieldHeightIncrement r j))) = fieldAllIncrements k := by
    unfold fieldAllIncrements
    apply congrArg List.ofFn
    funext j
    apply Prod.ext
    · rfl
    · exact Real.toNNReal_of_nonneg (fieldIncrement_nonneg k j)
  rw [fieldHeightJointValue_scalar, he]
  exact fieldAllIncrements_value k z

end InvariantIsing

end

end OAI
