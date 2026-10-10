import OAI.Probability.InvariantIsing.Fields.FieldMagnetizationModulus
import OAI.Probability.InvariantIsing.Magnetic.MagneticFieldLevels

namespace OAI

/-! The overlap modulus is uniform in the root bias, including the
optimizing bias for a prescribed magnetization. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped NNReal
namespace InvariantIsing

lemma magneticLevelAtBias_increment_le (h : FieldStep) (b : ℝ) {V : ℝ}
    (hV : h.height (Fin.last h.depth) ≤ V) (i : Fin h.depth) :
    magneticLevelAtBias h b i.succ - magneticLevelAtBias h b i.castSucc ≤
      (h.height i.succ - h.height i.castSucc) * fieldGaussianMomentCap (Real.sqrt V) := by
  let L := scalarFieldIncrements h
  let j : Fin L.length := Fin.cast (scalarFieldIncrements_length h).symm i
  have hL := scalarFieldIncrements_positive h
  have hζ : ∀ av ∈ L, av.1 ≤ 1 := by
    intro av hav
    obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hav
    change h.cut k.succ.castSucc ≤ 1
    rw [← h.last]
    exact h.ordered_cut.monotone (Fin.le_last _)
  have hvar : ∀ av ∈ L, (av.2 : ℝ) ≤ V := by
    intro av hav
    obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hav
    exact (fieldIncrement_le_last h k.succ).trans hV
  have hget : ((L.get j).2 : ℝ) = h.height i.succ - h.height i.castSucc := by
    have hg : L.get j = ((fieldIncrement h i.succ).1,
        NNReal.mk (fieldIncrement h i.succ).2 (fieldIncrement_nonneg h i.succ)) := by
      exact List.get_ofFn (fun k : Fin h.depth => ((fieldIncrement h k.succ).1,
        NNReal.mk (fieldIncrement h k.succ).2 (fieldIncrement_nonneg h k.succ))) j
    rw [hg]
    change (fieldIncrement h i.succ).2 = _
    simp only [fieldIncrement, Fin.val_succ, Nat.succ_ne_zero, dite_false, Nat.add_sub_cancel]
    rfl
  have hval := fieldScalarValue_regular L hL measurable_logCosh logCosh_linearGrowth
  have hm : Measurable Real.tanh := by
    change Measurable (fun x : ℝ => Real.tanh x)
    simp only [Real.tanh_eq]
    fun_prop
  have hreg := fieldScalarSquares_regular L hL measurable_logCosh logCosh_linearGrowth
    hm field_abs_tanh_le_one
  have hbnd (i : Fin (L.length+1)) (z : ℝ) :
      |fieldScalarSquares L (fun z => Real.log (Real.cosh z)) Real.tanh i z| ≤ 1 := by
    rw [abs_of_nonneg ((hreg i).2 z).1]
    exact ((hreg i).2 z).2
  change fieldSpinTransition 0 _ _
      (fieldScalarSquares L (fun z => Real.log (Real.cosh z)) Real.tanh j.succ) b -
    fieldSpinTransition 0 _ _
      (fieldScalarSquares L (fun z => Real.log (Real.cosh z)) Real.tanh j.castSucc) b ≤ _
  rw [← fieldSpinTransition_sub 0 _ hval.1 hval.2
    (hreg j.succ).1 (hreg j.castSucc).1 (hbnd j.succ) (hbnd j.castSucc)]
  calc
    _ ≤ fieldSpinTransition 0 _ (fieldScalarValue L (fun z => Real.log (Real.cosh z)))
        (fun _ => ((L.get j).2 : ℝ) * fieldGaussianMomentCap (Real.sqrt V)) b :=
      fieldSpinTransition_mono_test 0 _ _
        ((hreg j.succ).1.sub (hreg j.castSucc).1) measurable_const
        (fun z => (abs_sub _ _).trans (add_le_add (hbnd j.succ z) (hbnd j.castSucc z)))
        (fun _ => le_rfl) (fieldScalarSquares_increment_le L hL hζ hvar j) b
    _ = _ := by rw [fieldSpinTransition_const 0 _ hval.1 hval.2, hget]

theorem magneticLevelAtBias_sub_le (h : FieldStep) (b : ℝ) {V : ℝ}
    (hV : h.height (Fin.last h.depth) ≤ V)
    (i j : Fin (h.depth + 1)) (hij : i ≤ j) :
    magneticLevelAtBias h b j - magneticLevelAtBias h b i ≤
      (h.height j - h.height i) * fieldGaussianMomentCap (Real.sqrt V) := by
  have hm : Monotone (fun i => h.height i * fieldGaussianMomentCap (Real.sqrt V) -
      magneticLevelAtBias h b i) := by
    apply Fin.monotone_iff_le_succ.mpr
    intro k
    have hk := magneticLevelAtBias_increment_le h b hV k
    nlinarith
  have hh := hm hij
  nlinarith

theorem magneticLevelAtBias_abs_sub_le (h : FieldStep) (b : ℝ) {V : ℝ}
    (hV : h.height (Fin.last h.depth) ≤ V) (i j : Fin (h.depth + 1)) :
    |magneticLevelAtBias h b i - magneticLevelAtBias h b j| ≤
      |h.height i - h.height j| * fieldGaussianMomentCap (Real.sqrt V) := by
  rcases le_total i j with hij | hji
  · rw [abs_of_nonpos (sub_nonpos.mpr (magneticLevelAtBias_monotone h b hij)), neg_sub,
      abs_of_nonpos (sub_nonpos.mpr (h.ordered_height hij)), neg_sub]
    exact magneticLevelAtBias_sub_le h b hV i j hij
  · rw [abs_of_nonneg (sub_nonneg.mpr (magneticLevelAtBias_monotone h b hji)),
      abs_of_nonneg (sub_nonneg.mpr (h.ordered_height hji))]
    exact magneticLevelAtBias_sub_le h b hV j i hji


lemma magneticFieldLevel_abs_sub_le (h : FieldStep) {V : ℝ}
    (hV : h.height (Fin.last h.depth) ≤ V) (s : ℝ) (i j : Fin (h.depth+1)) :
    |magneticFieldLevel h s i - magneticFieldLevel h s j| ≤
      |h.height i-h.height j| * fieldGaussianMomentCap (Real.sqrt V) :=
  magneticLevelAtBias_abs_sub_le h (magneticBias h s) hV i j

end InvariantIsing

end

end OAI
