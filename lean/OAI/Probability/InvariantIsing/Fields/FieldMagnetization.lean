import OAI.Probability.InvariantIsing.Fields.FieldScalarOverlap
import OAI.Probability.InvariantIsing.Fields.FieldLevelPath

namespace OAI

/-! Actual magnetization-overlap path for a finite scalar Ising field. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped NNReal

namespace InvariantIsing

/-- The non-root Gaussian increments in the given field step. -/
def scalarFieldIncrements (h : FieldStep) : List (ℝ × ℝ≥0) :=
  List.ofFn (fun i : Fin h.depth => ((fieldIncrement h i.succ).1,
    NNReal.mk (fieldIncrement h i.succ).2 (fieldIncrement_nonneg h i.succ)))

lemma scalarFieldIncrements_length (h : FieldStep) :
    (scalarFieldIncrements h).length = h.depth := by simp [scalarFieldIncrements]

lemma scalarFieldIncrements_positive (h : FieldStep) :
    ∀ av ∈ scalarFieldIncrements h, 0 < av.1 := by
  intro av hav
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hav
  exact fieldIncrement_tail_positive h i

lemma scalarFieldIncrements_value (h : FieldStep) :
    fieldScalarValue (scalarFieldIncrements h) (fun z => Real.log (Real.cosh z)) =
      (List.ofFn (fun i : Fin h.depth => fieldIncrement h i.succ)).foldr
        (fun av f => gaussianOperator av.1 av.2 f) (fun z => Real.log (Real.cosh z)) := by
  unfold fieldScalarValue scalarFieldIncrements
  rw [← List.foldr_map (f := fun av : ℝ × ℝ≥0 => (av.1, (av.2 : ℝ)))
    (g := fun av f => gaussianOperator av.1 av.2 f), List.map_ofFn]
  rfl

lemma fieldValue_scalar_chain (h : FieldStep) :
    fieldValue h 0 = gaussianOperator 0 (h.height 0)
      (fieldScalarValue (scalarFieldIncrements h) (fun z => Real.log (Real.cosh z))) 0 -
      h.height (Fin.last h.depth) / 2 := by
  rw [scalarFieldIncrements_value, fieldValue, List.ofFn_succ, List.foldr_cons]
  have hroot : fieldIncrement h 0 = (0, h.height 0) := by
    simp [fieldIncrement, h.first]
  rw [hroot]

/-- The physical squared conditional spin means, averaged over the root
Gaussian. These are the `B_i(h)` of the field derivative formula. -/
def fieldMagnetizationLevel (h : FieldStep) (i : Fin (h.depth + 1)) : ℝ :=
  fieldScalarOverlaps (scalarFieldIncrements h) (NNReal.mk (h.height 0) (h.nonneg 0))
    (fun z => Real.log (Real.cosh z)) Real.tanh
    (Fin.cast (by rw [scalarFieldIncrements_length]) i)

private lemma measurable_field_tanh : Measurable Real.tanh := by
  change Measurable (fun x : ℝ => Real.tanh x)
  simp only [Real.tanh_eq]
  fun_prop

lemma fieldMagnetizationLevel_mem_unit (h : FieldStep) (i : Fin (h.depth + 1)) :
    fieldMagnetizationLevel h i ∈ Icc (0 : ℝ) 1 := by
  exact fieldScalarOverlaps_mem_unit (scalarFieldIncrements h) _ (scalarFieldIncrements_positive h)
    measurable_logCosh logCosh_linearGrowth measurable_field_tanh field_abs_tanh_le_one _

lemma fieldMagnetizationLevel_monotone (h : FieldStep) :
    Monotone (fieldMagnetizationLevel h) := by
  have hm := fieldScalarOverlaps_monotone (scalarFieldIncrements h)
    (NNReal.mk (h.height 0) (h.nonneg 0)) (scalarFieldIncrements_positive h)
    measurable_logCosh logCosh_linearGrowth measurable_field_tanh field_abs_tanh_le_one
  intro i j hij
  apply hm
  exact hij

/-- A globally defined admissible representative on the field partition. -/
def fieldMagnetizationPath (h : FieldStep) : InvariantIsing.OverlapPath :=
  fieldLevelPath h (fieldMagnetizationLevel h) (fieldMagnetizationLevel_monotone h)
    (fieldMagnetizationLevel_mem_unit h)

lemma fieldMagnetizationPath_on_cell (h : FieldStep) (i : Fin (h.depth + 1))
    {s : ℝ} (hs : s ∈ Ioo (h.cut i.castSucc) (h.cut i.succ)) :
    fieldMagnetizationPath h s = fieldMagnetizationLevel h i :=
  fieldLevelPath_on_cell h _ _ _ i hs

lemma fieldMagnetizationLevel_tied (h : FieldStep) (i : Fin h.depth)
    (hi : h.height i.castSucc = h.height i.succ) :
    fieldMagnetizationLevel h i.castSucc = fieldMagnetizationLevel h i.succ := by
  let j : Fin (scalarFieldIncrements h).length :=
    Fin.cast (scalarFieldIncrements_length h).symm i
  have hvar : ((scalarFieldIncrements h).get j).2 = 0 := by
    have hg : (scalarFieldIncrements h).get j =
        ((fieldIncrement h i.succ).1,
          NNReal.mk (fieldIncrement h i.succ).2 (fieldIncrement_nonneg h i.succ)) := by
      exact List.get_ofFn (fun k : Fin h.depth => ((fieldIncrement h k.succ).1,
        NNReal.mk (fieldIncrement h k.succ).2 (fieldIncrement_nonneg h k.succ))) j
    rw [hg]
    apply Subtype.ext
    change (fieldIncrement h i.succ).2 = 0
    simp only [fieldIncrement, Fin.val_succ, Nat.succ_ne_zero,
      dite_false, Nat.add_sub_cancel]
    change h.height i.succ - h.height i.castSucc = 0
    exact sub_eq_zero.mpr hi.symm
  have he := fieldScalarOverlaps_tied_increment (scalarFieldIncrements h)
    (NNReal.mk (h.height 0) (h.nonneg 0)) (fun z => Real.log (Real.cosh z)) Real.tanh j hvar
  change fieldScalarOverlaps _ _ _ _ _ = fieldScalarOverlaps _ _ _ _ _
  convert he using 1 <;> congr 1

end InvariantIsing

end

end OAI
