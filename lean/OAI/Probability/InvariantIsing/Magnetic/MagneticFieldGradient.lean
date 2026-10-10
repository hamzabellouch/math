import OAI.Probability.InvariantIsing.Magnetic.MagneticFieldLevels
import OAI.Probability.InvariantIsing.Magnetic.MagneticFieldHeightDerivative
import OAI.Probability.InvariantIsing.Fields.FieldHeightGradient
import OAI.Probability.InvariantIsing.Fields.FieldHeightLists

namespace OAI

/-! The exact physical height gradient at an arbitrary bias, and hence
at the bias realizing a prescribed magnetization. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped BigOperators NNReal

namespace InvariantIsing

lemma hasDerivAt_fieldInteriorChart_bias (h : FieldStep) (i : Fin h.depth)
    (hstrict : ∀ j, 0 < (fieldIncrement h j).2) (b : ℝ) :
    HasDerivAt (fun t => fieldInteriorChart h i t b)
      (-(h.cut i.castSucc.succ - h.cut i.castSucc.castSucc) / 2 *
        magneticLevelAtBias h b i.castSucc) 0 := by
  have hd := hasDerivAt_fieldInteriorChart h i hstrict b
  rw [magneticLevelAtBias_allSquares]
  exact hd

private lemma magnetic_terminal_list_zero (h : FieldStep) :
    fieldTerminalIncrements ((fieldAllIncrements h).take h.depth)
      (fieldIncrement h (Fin.last h.depth)).2 (fieldIncrement h (Fin.last h.depth)).1 0 =
      fieldAllIncrements h := by
  have he := updated_increments_final h 0
  simp only [add_zero, Function.update_eq_self] at he
  rw [← he]
  unfold fieldAllIncrements
  apply congrArg List.ofFn
  funext j
  apply Prod.ext
  · rfl
  · exact Real.toNNReal_of_nonneg (fieldIncrement_nonneg h j)

lemma hasDerivAt_fieldFinalChart_bias (h : FieldStep)
    (hstrict : ∀ j, 0 < (fieldIncrement h j).2) (b : ℝ) :
    HasDerivAt (fun t => fieldFinalChart h t b)
      (-(1 - h.cut (Fin.last h.depth).castSucc) / 2 *
        magneticLevelAtBias h b (Fin.last h.depth)) 0 := by
  let L := fieldAllIncrements h
  have hP : ∀ av ∈ L.take h.depth, 0 < (av.2 : ℝ) := fun av hav =>
    fieldAllIncrements_strict h hstrict av (List.mem_of_mem_take hav)
  have ht : (0 : ℝ) ∈ Ioi (-(fieldIncrement h (Fin.last h.depth)).2) := by
    change -(fieldIncrement h (Fin.last h.depth)).2 < 0
    linarith [hstrict (Fin.last h.depth)]
  have hd := hasDerivAt_fieldTerminalValue (L.take h.depth) hP
    (fieldIncrement h (Fin.last h.depth)).2 (fieldIncrement h (Fin.last h.depth)).1
    (h.height (Fin.last h.depth)) 0 b ht
  have hs := fieldScalarSquares_congr_list (magnetic_terminal_list_zero h)
    (fun y => Real.log (Real.cosh y)) Real.tanh
    (fieldTerminalLevel (L.take h.depth) (fieldIncrement h (Fin.last h.depth)).2
      (fieldIncrement h (Fin.last h.depth)).1 0)
    ⟨(Fin.last h.depth).val + 1, by simp⟩ (by
      simp [fieldTerminalLevel, fieldAppendIndex, L])
  rw [congrFun hs b, ← magneticLevelAtBias_allSquares] at hd
  exact hd

lemma hasDerivAt_fieldHeightCoordinate_bias (h : FieldStep)
    (i : Fin (h.depth + 1)) (hstrict : ∀ j, 0 < (fieldIncrement h j).2) (b : ℝ) :
    HasDerivAt (fun t => fieldHeightCoordinateValue h i t b)
      (-(h.cut i.succ - h.cut i.castSucc) / 2 * magneticLevelAtBias h b i) 0 := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · have he : (fun t => fieldHeightCoordinateValue h (Fin.last h.depth) t b) =
        fun t => fieldFinalChart h t b := by
      funext t
      exact fieldHeightCoordinateValue_final h t b
    rw [he]
    simpa only [Fin.succ_last, h.last] using hasDerivAt_fieldFinalChart_bias h hstrict b
  · have he : (fun t => fieldHeightCoordinateValue h j.castSucc t b) =
        fun t => fieldInteriorChart h j t b := by
      funext t
      exact fieldHeightCoordinateValue_interior h j t b
    rw [he]
    exact hasDerivAt_fieldInteriorChart_bias h j hstrict b

lemma fieldFinite_centered_coordinate_derivative_bias (h : FieldStep)
    {I : Set (Fin (h.depth + 1) → ℝ)} (F : FieldFiniteFamily (h.depth + 1) I)
    (r : Fin (h.depth + 1) → ℝ) (hr : r ∈ I) (i : Fin (h.depth + 1)) (b : ℝ) :
    HasDerivAt (fun t : ℝ => F.U (Function.update r i (r i + t), b) -
      (Function.update r i (r i + t)) (Fin.last h.depth) / 2)
      (F.P i (r, b) - if i = Fin.last h.depth then 1 / 2 else 0) 0 := by
  classical
  have hd := F.coordinate_derivative r b hr i
  by_cases hi : i = Fin.last h.depth
  · subst i
    have hc : HasDerivAt (fun t : ℝ => (r (Fin.last h.depth) + t) / 2) (1 / 2 : ℝ) 0 :=
      ((hasDerivAt_id (0 : ℝ)).const_add (r (Fin.last h.depth))).div_const 2
    convert hd.sub hc using 1
    · funext t
      simp only [Pi.sub_apply, Function.update_self]
    · simp
  · have hn : Fin.last h.depth ≠ i := Ne.symm hi
    simpa [Function.update_of_ne hn, hi] using hd.sub_const (r (Fin.last h.depth) / 2)

theorem magneticHeight_gradient_identification (h : FieldStep)
    {I : Set (Fin (h.depth + 1) → ℝ)} (F : FieldFiniteFamily (h.depth + 1) I)
    (hU : F.U = fieldFiniteValue (fieldHeightFiniteList h))
    (r : Fin (h.depth + 1) → ℝ) (hr : r ∈ I)
    (hs : r ∈ fieldStrictHeightCone h.depth) (i : Fin (h.depth + 1)) (b : ℝ) :
    F.P i (r, b) - (if i = Fin.last h.depth then 1 / 2 else 0) =
      -(h.cut i.succ - h.cut i.castSucc) / 2 *
        magneticLevelAtBias (fieldStepOfStrictHeights h r hs) b i := by
  let k := fieldStepOfStrictHeights h r hs
  have hd := fieldFinite_centered_coordinate_derivative_bias h F r hr i b
  have he : (fun t : ℝ => F.U (Function.update r i (r i + t), b) -
      (Function.update r i (r i + t)) (Fin.last h.depth) / 2) =
      fun t => fieldHeightCoordinateValue k i t b := by
    funext t
    rw [hU]
    change fieldHeightJointValue k (Function.update k.height i (k.height i + t)) b = _
    exact fieldHeightJointValue_update k i t b
  rw [he] at hd
  have hk := hasDerivAt_fieldHeightCoordinate_bias k i
    (fun j => fieldStepOfStrictHeights_strict h r hs j) b
  exact hd.unique hk

lemma magneticHeight_optimized_gradient (h : FieldStep)
    {I : Set (Fin (h.depth + 1) → ℝ)} (F : FieldFiniteFamily (h.depth + 1) I)
    (hU : F.U = fieldFiniteValue (fieldHeightFiniteList h))
    {s : ℝ} (_hs : |s| < 1) (r : Fin (h.depth + 1) → ℝ) (hr : r ∈ I)
    (hrs : r ∈ fieldStrictHeightCone h.depth) (i : Fin (h.depth + 1)) :
    F.P i (r, magneticHeightBias h s r) -
        (if i = Fin.last h.depth then 1 / 2 else 0) =
      -(h.cut i.succ - h.cut i.castSucc) / 2 *
        magneticFieldLevel (fieldStepOfStrictHeights h r hrs) s i := by
  rw [magneticHeight_gradient_identification h F hU r hr hrs i,
    magneticHeightBias_eq h s r hrs]
  rfl

end InvariantIsing

end

end OAI
