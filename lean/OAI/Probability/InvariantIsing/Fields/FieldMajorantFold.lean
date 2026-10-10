import OAI.Probability.InvariantIsing.Fields.FieldMajorantGaussian
import OAI.Probability.InvariantIsing.Fields.FieldBounds

namespace OAI

/-! The one-step majorant iterated through the actual finite field recursion. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace InvariantIsing

lemma gaussianOperator_mono {F G : ℝ → ℝ} (hF : Measurable F) (hG : Measurable G)
    (hFG : IsingPerceptron.HasLinearGrowth F) (hGG : IsingPerceptron.HasLinearGrowth G)
    (h : ∀ z, F z ≤ G z) {a : ℝ} (ha : 0 ≤ a) (v z : ℝ) :
    gaussianOperator a v F z ≤ gaussianOperator a v G z := by
  by_cases ha0 : a = 0
  · simp only [gaussianOperator, ha0, ite_true]
    apply integral_mono
      (IsingPerceptron.gaussian_linearGrowth_integrable
        (hF.comp (measurable_const.add (measurable_id.const_mul _)))
        ((hFG.add_left z).scale_argument (Real.sqrt v)) _ _)
      (IsingPerceptron.gaussian_linearGrowth_integrable
        (hG.comp (measurable_const.add (measurable_id.const_mul _)))
        ((hGG.add_left z).scale_argument (Real.sqrt v)) _ _)
    exact fun y => h _
  · have hap : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
    rw [gaussianOperator_eq_transform, gaussianOperator_eq_transform]
    simp only [IsingPerceptron.gaussianTransform, ha0, ite_false]
    exact IsingPerceptron.logMean_mono (gaussianReal 0 1) hap
      (IsingPerceptron.integrable_exp_of_linearGrowth _
        (IsingPerceptron.gaussianReal_exponentialNormMoments _ _)
        (hF.comp (measurable_const.add (measurable_id.const_mul _)))
        ((hFG.add_left z).scale_argument (Real.sqrt v)) a)
      (IsingPerceptron.integrable_exp_of_linearGrowth _
        (IsingPerceptron.gaussianReal_exponentialNormMoments _ _)
        (hG.comp (measurable_const.add (measurable_id.const_mul _)))
        ((hGG.add_left z).scale_argument (Real.sqrt v)) a)
      (fun y => h _)

lemma linearGrowth_const_add {F : ℝ → ℝ} (hF : IsingPerceptron.HasLinearGrowth F)
    (c : ℝ) : IsingPerceptron.HasLinearGrowth (fun z => c + F z) := by
  obtain ⟨C, L, hC, hL, h⟩ := hF
  refine ⟨|c| + C, L, add_nonneg (abs_nonneg _) hC, hL, fun z => ?_⟩
  exact (abs_add_le _ _).trans (by linarith [h z])

lemma gaussianOperator_const_add {F : ℝ → ℝ} (hF : Measurable F)
    (hFG : IsingPerceptron.HasLinearGrowth F) (c a v z : ℝ) :
    gaussianOperator a v (fun x => c + F x) z = c + gaussianOperator a v F z := by
  simp only [gaussianOperator_eq_transform]
  exact congrFun (IsingPerceptron.gaussianTransform_const_add hF hFG v a c) z

lemma gaussianOperator_positive_growth {F : ℝ → ℝ} (hF : Measurable F)
    (hFG : IsingPerceptron.HasLinearGrowth F) {a : ℝ} (ha : 0 < a) (v : ℝ) :
    Measurable (gaussianOperator a v F) ∧
      IsingPerceptron.HasLinearGrowth (gaussianOperator a v F) := by
  rw [gaussianOperator_eq_transform]
  exact ⟨IsingPerceptron.measurable_gaussianTransform hF v a,
    IsingPerceptron.gaussianTransform_positive_linearGrowth hF hFG v ha⟩

lemma gaussianOperator_fold_growth (L : List (ℝ × ℝ))
    (hL : ∀ av ∈ L, 0 < av.1) {F : ℝ → ℝ} (hF : Measurable F)
    (hFG : IsingPerceptron.HasLinearGrowth F) :
    Measurable (L.foldr (fun av f => gaussianOperator av.1 av.2 f) F) ∧
      IsingPerceptron.HasLinearGrowth
        (L.foldr (fun av f => gaussianOperator av.1 av.2 f) F) := by
  induction L with
  | nil => exact ⟨hF, hFG⟩
  | cons av L ih =>
    have ht := ih (fun bv hb => hL bv (List.mem_cons_of_mem _ hb))
    exact gaussianOperator_positive_growth ht.1 ht.2 (hL av (List.mem_cons_self)) av.2

/-- Only positive exponents occur in the non-root part of the recursion. -/
lemma gaussianOperator_fold_majorant (L : List (ℝ × ℝ))
    (hL : ∀ av ∈ L, 0 < av.1 ∧ 0 ≤ av.2) {d : ℝ} (hd : 0 < d)
    (hd1 : d ≤ 1) (z : ℝ) :
    (L.foldr (fun av f => gaussianOperator av.1 av.2 f)
      (fun x => Real.log (Real.cosh x))) z ≤ fieldMajorant d z +
        (L.map (fun av => max av.1 d * av.2 / 2)).sum := by
  induction L generalizing z with
  | nil => simpa using logcosh_le_fieldMajorant hd hd1 z
  | cons av L ih =>
    have htail : ∀ bv ∈ L, 0 < bv.1 ∧ 0 ≤ bv.2 :=
      fun bv hb => hL bv (List.mem_cons_of_mem _ hb)
    have hav := hL av (List.mem_cons_self)
    have hT := gaussianOperator_fold_growth L (fun bv hb => (htail bv hb).1)
      IsingPerceptron.measurable_logCosh IsingPerceptron.logCosh_linearGrowth
    let c := (L.map (fun bv => max bv.1 d * bv.2 / 2)).sum
    have hm : gaussianOperator av.1 av.2
        (L.foldr (fun bv f => gaussianOperator bv.1 bv.2 f)
          (fun x => Real.log (Real.cosh x))) z ≤
        gaussianOperator av.1 av.2 (fun x => c + fieldMajorant d x) z := by
      apply gaussianOperator_mono hT.1 (measurable_const.add (measurable_fieldMajorant d))
        hT.2 (linearGrowth_const_add (fieldMajorant_linearGrowth hd) c) _ hav.1.le
      intro x
      simpa only [c, Pi.add_apply, add_comm] using ih htail x
    rw [gaussianOperator_const_add (measurable_fieldMajorant d)
      (fieldMajorant_linearGrowth hd)] at hm
    have hc := gaussianOperator_fieldMajorant hd hav.1.le hav.2 z
    simp only [List.foldr_cons, List.map_cons, List.sum_cons]
    dsimp only [c] at hm
    linarith

lemma fieldIncrement_nonneg (h : FieldStep) (i : Fin (h.depth + 1)) :
    0 ≤ (fieldIncrement h i).2 := by
  unfold fieldIncrement
  split_ifs with hi
  · simpa using h.nonneg i
  · apply sub_nonneg.mpr
    apply h.ordered_height
    change i.val - 1 ≤ i.val
    omega

lemma fieldIncrement_tail_positive (h : FieldStep) (i : Fin h.depth) :
    0 < (fieldIncrement h i.succ).1 := by
  change 0 < h.cut i.succ.castSucc
  rw [← h.first]
  apply h.ordered_cut
  change 0 < i.val + 1
  omega

/-- Iteration through the actual finite field, with the initial zero exponent
handled by ordinary Gaussian expectation. -/
lemma fieldValue_majorant_sum (h : FieldStep) {d : ℝ} (hd : 0 < d) (hd1 : d ≤ 1)
    (z : ℝ) :
    fieldValue h z ≤ fieldMajorant d z +
      ((List.ofFn (fieldIncrement h)).map (fun av => max av.1 d * av.2 / 2)).sum -
        h.height (Fin.last h.depth) / 2 := by
  let L := List.ofFn (fun i : Fin h.depth => fieldIncrement h i.succ)
  have hL : ∀ av ∈ L, 0 < av.1 ∧ 0 ≤ av.2 := by
    intro av hav
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hav
    exact ⟨fieldIncrement_tail_positive h i, fieldIncrement_nonneg h i.succ⟩
  have hT := gaussianOperator_fold_growth L (fun av hav => (hL av hav).1)
    IsingPerceptron.measurable_logCosh IsingPerceptron.logCosh_linearGrowth
  let c := (L.map (fun av => max av.1 d * av.2 / 2)).sum
  have hroot : fieldIncrement h 0 = (0, h.height 0) := by
    simp [fieldIncrement, h.first]
  have hm := gaussianOperator_mono hT.1 (measurable_const.add (measurable_fieldMajorant d))
    hT.2 (linearGrowth_const_add (fieldMajorant_linearGrowth hd) c)
    (fun x => by simpa only [c, Pi.add_apply, add_comm] using gaussianOperator_fold_majorant L hL hd hd1 x)
    (show 0 ≤ (0 : ℝ) from le_rfl) (h.height 0) z
  change gaussianOperator 0 (h.height 0)
      (L.foldr (fun av f => gaussianOperator av.1 av.2 f)
        (fun x => Real.log (Real.cosh x))) z ≤
    gaussianOperator 0 (h.height 0) (fun x => c + fieldMajorant d x) z at hm
  rw [gaussianOperator_const_add (measurable_fieldMajorant d)
    (fieldMajorant_linearGrowth hd)] at hm
  have hc := gaussianOperator_fieldMajorant hd (show 0 ≤ (0 : ℝ) from le_rfl)
    (h.nonneg 0) z
  simp only [max_eq_right hd.le] at hc
  simp only [fieldValue, List.ofFn_succ, List.foldr_cons, List.map_cons, List.sum_cons, hroot]
  change gaussianOperator 0 (h.height 0)
      (L.foldr (fun av f => gaussianOperator av.1 av.2 f)
        (fun x => Real.log (Real.cosh x))) z - h.height (Fin.last h.depth) / 2 ≤
    fieldMajorant d z + (max 0 d * h.height 0 / 2 + c) - h.height (Fin.last h.depth) / 2
  rw [max_eq_right hd.le]
  linarith

end InvariantIsing

end

end OAI
