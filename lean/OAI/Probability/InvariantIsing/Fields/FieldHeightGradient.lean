import OAI.Probability.InvariantIsing.Fields.FieldHeightCone
import OAI.Probability.InvariantIsing.Fields.FieldFiniteDirections

namespace OAI

/-! Identification of the jointly constructed height gradient with the
actual scalar magnetization. The terminal centering is retained explicitly. -/

noncomputable section
open IsingPerceptron Set
open scoped BigOperators

namespace InvariantIsing

lemma fieldFinite_centered_coordinate_derivative (h : FieldStep)
    {I : Set (Fin (h.depth + 1) → ℝ)} (F : FieldFiniteFamily (h.depth + 1) I)
    (r : Fin (h.depth + 1) → ℝ) (hr : r ∈ I) (i : Fin (h.depth + 1)) :
    HasDerivAt (fun t : ℝ => F.U (Function.update r i (r i + t), 0) -
      (Function.update r i (r i + t)) (Fin.last h.depth) / 2)
      (F.P i (r, 0) - if i = Fin.last h.depth then 1 / 2 else 0) 0 := by
  classical
  have hd := F.coordinate_derivative r 0 hr i
  by_cases hi : i = Fin.last h.depth
  · subst i
    have hc : HasDerivAt (fun t : ℝ => (r (Fin.last h.depth) + t) / 2) (1 / 2 : ℝ) 0 :=
      ((hasDerivAt_id (0 : ℝ)).const_add (r (Fin.last h.depth))).div_const 2
    convert hd.sub hc using 1
    · funext t
      simp only [Pi.sub_apply, Function.update_self]
    · simp
  · have hn : Fin.last h.depth ≠ i := Ne.symm hi
    simpa [Function.update_of_ne hn, hi] using
      hd.sub_const (r (Fin.last h.depth) / 2)

/-- The exact literal-height gradient. `F` is derivative data constructed
from the finite Gaussian recursion; the equality of its value is the only
identification required here. -/
theorem fieldHeight_gradient_identification (h : FieldStep)
    {I : Set (Fin (h.depth + 1) → ℝ)} (F : FieldFiniteFamily (h.depth + 1) I)
    (hU : F.U = fieldFiniteValue (fieldHeightFiniteList h))
    (r : Fin (h.depth + 1) → ℝ) (hr : r ∈ I)
    (hs : r ∈ fieldStrictHeightCone h.depth) (i : Fin (h.depth + 1)) :
    F.P i (r, 0) - (if i = Fin.last h.depth then 1 / 2 else 0) =
      -(h.cut i.succ - h.cut i.castSucc) / 2 *
        fieldMagnetizationLevel (fieldStepOfStrictHeights h r hs) i := by
  let k := fieldStepOfStrictHeights h r hs
  have hd := fieldFinite_centered_coordinate_derivative h F r hr i
  have he : (fun t : ℝ => F.U (Function.update r i (r i + t), 0) -
      (Function.update r i (r i + t)) (Fin.last h.depth) / 2) =
      fun t => fieldHeightCoordinateValue k i t 0 := by
    funext t
    rw [hU]
    change fieldHeightJointValue k (Function.update k.height i (k.height i + t)) 0 = _
    exact fieldHeightJointValue_update k i t 0
  rw [he] at hd
  have hk := hasDerivAt_fieldHeightCoordinate k i
    (fun j => fieldStepOfStrictHeights_strict h r hs j)
  exact hd.unique hk

end InvariantIsing

end

end OAI
