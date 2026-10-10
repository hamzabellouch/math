import OAI.Probability.InvariantIsing.Fields.FieldCoordinateDerivative
import OAI.Probability.InvariantIsing.Fields.FieldMagnetization

namespace OAI

/-! Coordinate charts for the exact finite field functional. The charts
use its original Gaussian increments and change a single covariance height. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped NNReal

namespace InvariantIsing

def fieldAllIncrements (h : FieldStep) : List (ℝ × ℝ≥0) :=
  List.ofFn fun i : Fin (h.depth + 1) =>
    ((fieldIncrement h i).1, NNReal.mk (fieldIncrement h i).2 (fieldIncrement_nonneg h i))

@[simp] lemma fieldAllIncrements_length (h : FieldStep) :
    (fieldAllIncrements h).length = h.depth + 1 := by simp [fieldAllIncrements]

lemma fieldAllIncrements_value (h : FieldStep) (z : ℝ) :
    fieldScalarValue (fieldAllIncrements h) (fun y => Real.log (Real.cosh y)) z -
      h.height (Fin.last h.depth) / 2 = fieldValue h z := by
  unfold fieldScalarValue fieldAllIncrements fieldValue
  rw [← List.foldr_map (f := fun av : ℝ × ℝ≥0 => (av.1, (av.2 : ℝ)))
    (g := fun av f => gaussianOperator av.1 av.2 f), List.map_ofFn]
  rfl

lemma fieldAllIncrements_strict (h : FieldStep)
    (hstrict : ∀ i, 0 < (fieldIncrement h i).2) :
    ∀ av ∈ fieldAllIncrements h, 0 < (av.2 : ℝ) := by
  intro av hav
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hav
  exact hstrict i

private lemma list_split_two {α : Type*} (L : List α) (i : ℕ)
    (hi : i + 1 < L.length) :
    L = L.take i ++ L[i] :: L[i + 1] :: L.drop (i + 2) := by
  rw [← List.drop_eq_getElem_cons (show i + 1 < L.length from hi)]
  rw [← List.drop_eq_getElem_cons (show i < L.length by omega)]
  exact (List.take_append_drop i L).symm

/-- This changes the height at an interior cell, keeping the final
height and every other increment fixed. -/
def fieldInteriorChart (h : FieldStep) (i : Fin h.depth) (t z : ℝ) : ℝ :=
  let L := fieldAllIncrements h
  fieldScalarValue
    (fieldAdjacentIncrements (L.take i.val) (L.drop (i.val + 2))
      (fieldIncrement h i.castSucc).2 (fieldIncrement h i.succ).2
      (fieldIncrement h i.castSucc).1 (fieldIncrement h i.succ).1 t)
    (fun y => Real.log (Real.cosh y)) z - h.height (Fin.last h.depth) / 2

private lemma interior_list_zero (h : FieldStep) (i : Fin h.depth) :
    fieldAdjacentIncrements ((fieldAllIncrements h).take i.val)
      ((fieldAllIncrements h).drop (i.val + 2))
      (fieldIncrement h i.castSucc).2 (fieldIncrement h i.succ).2
      (fieldIncrement h i.castSucc).1 (fieldIncrement h i.succ).1 0 =
      fieldAllIncrements h := by
  let L := fieldAllIncrements h
  have hlen : L.length = h.depth + 1 := fieldAllIncrements_length h
  have hget (j : Fin (h.depth + 1)) : L[j.val] =
      ((fieldIncrement h j).1,
        NNReal.mk (fieldIncrement h j).2 (fieldIncrement_nonneg h j)) := by
    exact List.getElem_ofFn _
  unfold fieldAdjacentIncrements
  simp only [add_zero, sub_zero]
  have hcast : i.castSucc.val = i.val := rfl
  have hsucc : i.succ.val = i.val + 1 := rfl
  rw [show (Real.toNNReal (fieldIncrement h i.castSucc).2) =
      NNReal.mk (fieldIncrement h i.castSucc).2 (fieldIncrement_nonneg h i.castSucc) by
        change Real.toNNReal (↑(NNReal.mk (fieldIncrement h i.castSucc).2
          (fieldIncrement_nonneg h i.castSucc))) = _
        exact Real.toNNReal_coe,
    show (Real.toNNReal (fieldIncrement h i.succ).2) =
      NNReal.mk (fieldIncrement h i.succ).2 (fieldIncrement_nonneg h i.succ) by
        change Real.toNNReal (↑(NNReal.mk (fieldIncrement h i.succ).2
          (fieldIncrement_nonneg h i.succ))) = _
        exact Real.toNNReal_coe]
  rw [← hget i.castSucc, ← hget i.succ]
  exact (list_split_two L i.val (by rw [hlen]; omega)).symm

lemma fieldInteriorChart_zero (h : FieldStep) (i : Fin h.depth) (z : ℝ) :
    fieldInteriorChart h i 0 z = fieldValue h z := by
  dsimp only [fieldInteriorChart]
  rw [interior_list_zero]
  exact fieldAllIncrements_value h z

/-- The analogous final-height chart changes the last increment and the
normalizing diagonal covariance together. -/
def fieldFinalChart (h : FieldStep) (t z : ℝ) : ℝ :=
  let L := fieldAllIncrements h
  fieldScalarValue
    (fieldTerminalIncrements (L.take h.depth) (fieldIncrement h (Fin.last h.depth)).2
      (fieldIncrement h (Fin.last h.depth)).1 t)
    (fun y => Real.log (Real.cosh y)) z - (h.height (Fin.last h.depth) + t) / 2

lemma fieldAllIncrements_root (h : FieldStep) :
    fieldAllIncrements h = (0, NNReal.mk (h.height 0) (h.nonneg 0)) ::
      scalarFieldIncrements h := by
  unfold fieldAllIncrements scalarFieldIncrements
  rw [List.ofFn_succ]
  congr 1
  apply Prod.ext
  · exact h.first
  · apply Subtype.ext
    simp [fieldIncrement]

lemma fieldAllSquares_magnetization (h : FieldStep) (i : Fin (h.depth + 1)) :
    fieldScalarSquares (fieldAllIncrements h) (fun y => Real.log (Real.cosh y))
      Real.tanh ⟨i.val + 1, by simp only [fieldAllIncrements_length]; omega⟩ 0 = fieldMagnetizationLevel h i := by
  have hroot := fieldAllIncrements_root h
  let j : Fin ((scalarFieldIncrements h).length + 1) :=
    Fin.cast (by rw [scalarFieldIncrements_length]) i
  have hs := fieldScalarSquares_congr_list hroot
    (fun y => Real.log (Real.cosh y)) Real.tanh
    ⟨i.val + 1, by simp only [fieldAllIncrements_length]; omega⟩ j.succ (by rfl)
  rw [congrFun hs 0]
  change fieldSpinTransition 0 (NNReal.mk (h.height 0) (h.nonneg 0))
    (fieldScalarValue (scalarFieldIncrements h) (fun y => Real.log (Real.cosh y)))
    (fieldScalarSquares (scalarFieldIncrements h)
      (fun y => Real.log (Real.cosh y)) Real.tanh j) 0 = _
  simp only [fieldSpinTransition, integral_tilted_eq_div, zero_mul, Real.exp_zero,
    one_mul, integral_const, measureReal_def, measure_univ, ENNReal.toReal_one,
    one_smul, div_one]
  rfl

private lemma terminal_list_zero (h : FieldStep) :
    fieldTerminalIncrements ((fieldAllIncrements h).take h.depth)
      (fieldIncrement h (Fin.last h.depth)).2 (fieldIncrement h (Fin.last h.depth)).1 0 =
      fieldAllIncrements h := by
  let L := fieldAllIncrements h
  have hlen : L.length = h.depth + 1 := fieldAllIncrements_length h
  have hget : L[h.depth] = ((fieldIncrement h (Fin.last h.depth)).1,
      NNReal.mk (fieldIncrement h (Fin.last h.depth)).2
        (fieldIncrement_nonneg h (Fin.last h.depth))) := by
    exact List.getElem_ofFn _
  unfold fieldTerminalIncrements
  simp only [add_zero]
  rw [show Real.toNNReal (fieldIncrement h (Fin.last h.depth)).2 =
      NNReal.mk (fieldIncrement h (Fin.last h.depth)).2
        (fieldIncrement_nonneg h (Fin.last h.depth)) by
      change Real.toNNReal (↑(NNReal.mk (fieldIncrement h (Fin.last h.depth)).2
        (fieldIncrement_nonneg h (Fin.last h.depth)))) = _
      exact Real.toNNReal_coe, ← hget]
  rw [List.take_concat_get' L h.depth (by rw [hlen]; omega)]
  exact List.take_of_length_le (by rw [hlen])

lemma fieldFinalChart_zero (h : FieldStep) (z : ℝ) :
    fieldFinalChart h 0 z = fieldValue h z := by
  dsimp only [fieldFinalChart]
  rw [terminal_list_zero, add_zero]
  exact fieldAllIncrements_value h z

lemma hasDerivAt_fieldInteriorChart (h : FieldStep) (i : Fin h.depth)
    (hstrict : ∀ j, 0 < (fieldIncrement h j).2) (z : ℝ) :
    HasDerivAt (fun t => fieldInteriorChart h i t z)
      (-((fieldIncrement h i.succ).1 - (fieldIncrement h i.castSucc).1) / 2 *
        fieldScalarSquares (fieldAllIncrements h) (fun y => Real.log (Real.cosh y))
          Real.tanh ⟨i.val + 1, by simp⟩ z) 0 := by
  let L := fieldAllIncrements h
  have hP : ∀ av ∈ L.take i.val, 0 < (av.2 : ℝ) := fun av hav =>
    fieldAllIncrements_strict h hstrict av (List.mem_of_mem_take hav)
  have hS : ∀ av ∈ L.drop (i.val + 2), 0 < (av.2 : ℝ) := fun av hav =>
    fieldAllIncrements_strict h hstrict av (List.mem_of_mem_drop hav)
  have ht : (0 : ℝ) ∈ Ioo (-(fieldIncrement h i.castSucc).2)
      (fieldIncrement h i.succ).2 := ⟨by linarith [hstrict i.castSucc], hstrict i.succ⟩
  have hd := (hasDerivAt_fieldAdjacentValue (L.take i.val) (L.drop (i.val + 2)) hP hS
    (fieldIncrement h i.castSucc).2 (fieldIncrement h i.succ).2
    (fieldIncrement h i.castSucc).1 (fieldIncrement h i.succ).1 0 z ht).sub_const
      (h.height (Fin.last h.depth) / 2)
  change HasDerivAt _ _ 0
  convert hd using 1
  · rfl
  · apply congrArg (fun r : ℝ => -((fieldIncrement h i.succ).1 -
      (fieldIncrement h i.castSucc).1) / 2 * r)
    apply congrFun
    apply fieldScalarSquares_congr_list (interior_list_zero h i).symm
    simp only [fieldAdjacentLevel, fieldAppendIndex, List.length_take,
      fieldAllIncrements_length, L, List.length_cons, Fin.val_one]
    omega

/-- The exact interior coordinate gradient in `fld:gradient`, expressed
with the already constructed physical magnetization-overlap levels. -/
lemma hasDerivAt_fieldInteriorChart_magnetization (h : FieldStep) (i : Fin h.depth)
    (hstrict : ∀ j, 0 < (fieldIncrement h j).2) :
    HasDerivAt (fun t => fieldInteriorChart h i t 0)
      (-(h.cut i.castSucc.succ - h.cut i.castSucc.castSucc) / 2 *
        fieldMagnetizationLevel h i.castSucc) 0 := by
  have hd := hasDerivAt_fieldInteriorChart h i hstrict 0
  have hs : fieldScalarSquares (fieldAllIncrements h)
      (fun y => Real.log (Real.cosh y)) Real.tanh
      ⟨i.val + 1, by simp⟩ 0 =
      fieldMagnetizationLevel h i.castSucc := by
    simpa only [Fin.val_castSucc] using fieldAllSquares_magnetization h i.castSucc
  rw [hs] at hd
  exact hd

lemma hasDerivAt_fieldFinalChart (h : FieldStep)
    (hstrict : ∀ j, 0 < (fieldIncrement h j).2) :
    HasDerivAt (fun t => fieldFinalChart h t 0)
      (-(1 - h.cut (Fin.last h.depth).castSucc) / 2 *
        fieldMagnetizationLevel h (Fin.last h.depth)) 0 := by
  let L := fieldAllIncrements h
  have hP : ∀ av ∈ L.take h.depth, 0 < (av.2 : ℝ) := fun av hav =>
    fieldAllIncrements_strict h hstrict av (List.mem_of_mem_take hav)
  have ht : (0 : ℝ) ∈ Ioi (-(fieldIncrement h (Fin.last h.depth)).2) := by
    change -(fieldIncrement h (Fin.last h.depth)).2 < 0
    linarith [hstrict (Fin.last h.depth)]
  have hd := hasDerivAt_fieldTerminalValue (L.take h.depth) hP
    (fieldIncrement h (Fin.last h.depth)).2 (fieldIncrement h (Fin.last h.depth)).1
    (h.height (Fin.last h.depth)) 0 0 ht
  have hs := fieldScalarSquares_congr_list (terminal_list_zero h)
    (fun y => Real.log (Real.cosh y)) Real.tanh
    (fieldTerminalLevel (L.take h.depth) (fieldIncrement h (Fin.last h.depth)).2
      (fieldIncrement h (Fin.last h.depth)).1 0)
    ⟨(Fin.last h.depth).val + 1, by simp⟩ (by
      simp [fieldTerminalLevel, fieldAppendIndex, L])
  rw [congrFun hs 0, fieldAllSquares_magnetization] at hd
  exact hd

end InvariantIsing

end

end OAI
