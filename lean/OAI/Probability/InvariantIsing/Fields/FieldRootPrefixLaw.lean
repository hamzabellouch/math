import OAI.Probability.InvariantIsing.Fields.FieldRootOrder
import OAI.Probability.InvariantIsing.Fields.FieldHeightChart

namespace OAI

/-! Exact identification of the original magnetization levels after
splitting off the root and an unchanged prefix of scalar transitions. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

lemma fieldMagnetizationLevel_root_prefix (h : FieldStep)
    (P S : List (ℝ × ℝ≥0)) (root : ℝ≥0)
    (hL : fieldAllIncrements h = (0, root) :: (P ++ S))
    (i : Fin (h.depth + 1)) (j : Fin (P.length + 1)) (hij : i.val = j.val) :
    fieldMagnetizationLevel h i =
      fieldScalarOverlaps P root
        (fieldScalarValue S (fun z => Real.log (Real.cosh z)))
        (fieldScalarMean S (fun z => Real.log (Real.cosh z)) Real.tanh) j := by
  let i' : Fin ((fieldAllIncrements h).length + 1) :=
    ⟨i.val + 1, by simp only [fieldAllIncrements_length]; omega⟩
  have he := fieldScalarSquares_congr_list hL (fun z => Real.log (Real.cosh z))
    Real.tanh i' (fieldPrefixIndex P S j).succ (by
      simp only [i', fieldPrefixIndex, Fin.val_succ]
      omega)
  rw [← fieldAllSquares_magnetization h i]
  change fieldScalarSquares (fieldAllIncrements h) (fun z => Real.log (Real.cosh z))
    Real.tanh i' 0 = _
  rw [congrFun he 0]
  change fieldSpinTransition 0 root (fieldScalarValue (P ++ S) (fun z => Real.log (Real.cosh z)))
    (fieldScalarSquares (P ++ S) (fun z => Real.log (Real.cosh z))
      Real.tanh (fieldPrefixIndex P S j)) 0 = _
  rw [fieldScalarSquares_append_prefix]
  simp only [fieldSpinTransition, integral_tilted_eq_div, zero_mul, Real.exp_zero,
    one_mul, integral_const, measureReal_def, measure_univ, ENNReal.toReal_one,
    one_smul, div_one]
  rfl

end InvariantIsing

end

end OAI
