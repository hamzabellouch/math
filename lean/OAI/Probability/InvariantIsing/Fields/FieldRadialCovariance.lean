import OAI.Probability.InvariantIsing.Fields.FieldRadialOverlap
import OAI.Probability.InvariantIsing.Fields.FieldScalarScaling
import OAI.Probability.InvariantIsing.Fields.FieldMagnetization

namespace OAI

/-! Radial monotonicity of the actual finite-field overlap levels. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

def fieldScaleCovariance (h : FieldStep) (c : ℝ≥0) : FieldStep where
  depth := h.depth
  cut := h.cut
  ordered_cut := h.ordered_cut
  first := h.first
  last := h.last
  height := fun i => (c : ℝ) ^ 2 * h.height i
  nonneg := fun i => mul_nonneg (sq_nonneg _) (h.nonneg i)
  ordered_height := fun _i _j hij => mul_le_mul_of_nonneg_left (h.ordered_height hij) (sq_nonneg _)

lemma scalarFieldIncrements_scale (h : FieldStep) (c : ℝ≥0) :
    scalarFieldIncrements (fieldScaleCovariance h c) =
      fieldScaleIncrements c (scalarFieldIncrements h) := by
  unfold scalarFieldIncrements fieldScaleIncrements
  rw [List.map_ofFn]
  congr 1
  funext i
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    change (fieldIncrement (fieldScaleCovariance h c) i.succ).2 =
      (c : ℝ) ^ 2 * (fieldIncrement h i.succ).2
    simp only [fieldIncrement, fieldScaleCovariance]
    split_ifs <;> ring

private lemma overlaps_congr_list (L M : List (ℝ × ℝ≥0)) (he : L = M)
    (root : ℝ≥0) (F a : ℝ → ℝ) (i : Fin (L.length + 1)) (j : Fin (M.length + 1))
    (hij : i.val = j.val) :
    fieldScalarOverlaps L root F a i = fieldScalarOverlaps M root F a j := by
  subst M
  have hij' : i = j := Fin.ext hij
  subst j
  rfl

lemma fieldMagnetizationLevel_scale (h : FieldStep) (c : ℝ≥0)
    (i : Fin (h.depth + 1)) :
    fieldMagnetizationLevel (fieldScaleCovariance h c) i =
      fieldScalarOverlaps (scalarFieldIncrements h) (NNReal.mk (h.height 0) (h.nonneg 0))
        (fun z => Real.log (Real.cosh ((c : ℝ) * z)))
        (fun z => Real.tanh ((c : ℝ) * z))
        (Fin.cast (by rw [scalarFieldIncrements_length]) i) := by
  have hm : Measurable Real.tanh := by
    change Measurable (fun z : ℝ => Real.tanh z)
    simp only [Real.tanh_eq]
    fun_prop
  have he := fieldScalarOverlaps_scale_position c (scalarFieldIncrements h)
    (NNReal.mk (h.height 0) (h.nonneg 0)) measurable_logCosh hm
    (Fin.cast (by rw [scalarFieldIncrements_length]) i)
  rw [he]
  unfold fieldMagnetizationLevel
  have hroot : NNReal.mk ((fieldScaleCovariance h c).height 0)
      ((fieldScaleCovariance h c).nonneg 0) = c ^ 2 * NNReal.mk (h.height 0) (h.nonneg 0) := by
    apply Subtype.ext
    rfl
  rw [hroot]
  exact overlaps_congr_list _ _ (scalarFieldIncrements_scale h c) _ _ _ _ _ rfl

theorem fieldMagnetizationLevel_radial (h : FieldStep) {c d : ℝ≥0}
    (hcd : c ≤ d) (i : Fin (h.depth + 1)) :
    fieldMagnetizationLevel (fieldScaleCovariance h c) i ≤
      fieldMagnetizationLevel (fieldScaleCovariance h d) i := by
  rw [fieldMagnetizationLevel_scale, fieldMagnetizationLevel_scale]
  exact fieldScalarOverlaps_radial _ _ (scalarFieldIncrements_positive h) c.coe_nonneg
    (by exact_mod_cast hcd) _

end InvariantIsing

end

end OAI
