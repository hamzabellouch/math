import OAI.Probability.InvariantIsing.Fields.FieldScalarChain

namespace OAI

/-! The scalar field's actual level overlaps. Their ordering is the
conditional Jensen inequality, and zero increments give exact ties. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped NNReal

namespace InvariantIsing

lemma fieldScalarSquares_monotone (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) {F a : ℝ → ℝ}
    (hF : Measurable F) (hG : HasLinearGrowth F)
    (ha : Measurable a) (haB : ∀ u, |a u| ≤ 1) (z : ℝ) :
    Monotone (fun i => fieldScalarSquares L F a i z) := by
  induction L generalizing z with
  | nil =>
    intro i j _
    exact le_rfl
  | cons av L ih =>
    have htail (bv) (hb : bv ∈ L) := hL bv (List.mem_cons_of_mem av hb)
    have hval := fieldScalarValue_regular L htail hF hG
    have hmean := fieldScalarMean_regular L htail hF hG ha haB
    have hreg := fieldScalarSquares_regular L htail hF hG ha haB
    apply Fin.monotone_iff_le_succ.mpr
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · change (fieldSpinTransition av.1 av.2 (fieldScalarValue L F) (fieldScalarMean L F a) z) ^ 2 ≤
        fieldSpinTransition av.1 av.2 (fieldScalarValue L F) (fieldScalarSquares L F a 0) z
      have he : fieldScalarSquares L F a 0 = fun u => (fieldScalarMean L F a u) ^ 2 := by
        funext u
        exact fieldScalarSquares_zero L F a u
      rw [he]
      exact fieldSpinTransition_square_le av.1 av.2 hval.1 hval.2 hmean.1 hmean.2 z
    · change fieldSpinTransition av.1 av.2 (fieldScalarValue L F)
          (fieldScalarSquares L F a j.castSucc) z ≤
        fieldSpinTransition av.1 av.2 (fieldScalarValue L F)
          (fieldScalarSquares L F a j.succ) z
      apply fieldSpinTransition_mono_test av.1 av.2 (fieldScalarValue L F)
        (hreg j.castSucc).1 (hreg j.succ).1
        (fun u => by rw [abs_of_nonneg ((hreg j.castSucc).2 u).1]; exact ((hreg j.castSucc).2 u).2)
        (fun u => by rw [abs_of_nonneg ((hreg j.succ).2 u).1]; exact ((hreg j.succ).2 u).2)
      intro u
      exact ih htail u (by change j.val ≤ j.val + 1; omega)

lemma fieldScalarSquares_tied_increment (L : List (ℝ × ℝ≥0))
    (F a : ℝ → ℝ) (i : Fin L.length) (hi : (L.get i).2 = 0) :
    fieldScalarSquares L F a i.castSucc = fieldScalarSquares L F a i.succ := by
  induction L with
  | nil => exact Fin.elim0 i
  | cons av L ih =>
    revert hi
    refine Fin.cases ?_ (fun j => ?_) i
    · intro hi
      have hav : av.2 = 0 := by simpa only [List.get_cons_zero] using hi
      funext z
      simp only [Fin.castSucc_zero, fieldScalarSquares, Fin.cons_zero, Fin.cons_succ, fieldScalarMean,
        hav, fieldSpinTransition_zero_variance, fieldScalarSquares_zero]
    · intro hi
      have hj : (L.get j).2 = 0 := by
        change (L.get j).2 = 0 at hi
        exact hi
      funext z
      change fieldSpinTransition av.1 av.2 (fieldScalarValue L F)
          (fieldScalarSquares L F a j.castSucc) z =
        fieldSpinTransition av.1 av.2 (fieldScalarValue L F)
          (fieldScalarSquares L F a j.succ) z
      rw [ih j hj]

/-- Root Gaussian averaging produces the level second moments `B_i`. -/
def fieldScalarOverlaps (L : List (ℝ × ℝ≥0)) (root : ℝ≥0)
    (F a : ℝ → ℝ) (i : Fin (L.length + 1)) : ℝ :=
  ∫ z, fieldScalarSquares L F a i z ∂gaussianReal 0 root

lemma fieldScalarOverlaps_mem_unit (L : List (ℝ × ℝ≥0)) (root : ℝ≥0)
    (hL : ∀ av ∈ L, 0 < av.1) {F a : ℝ → ℝ}
    (hF : Measurable F) (hG : HasLinearGrowth F)
    (ha : Measurable a) (haB : ∀ u, |a u| ≤ 1) (i : Fin (L.length + 1)) :
    fieldScalarOverlaps L root F a i ∈ Icc (0 : ℝ) 1 := by
  have hr := fieldScalarSquares_regular L hL hF hG ha haB i
  have hi : Integrable (fieldScalarSquares L F a i) (gaussianReal 0 root) :=
    Integrable.of_bound hr.1.aestronglyMeasurable 1
      (Filter.Eventually.of_forall (fun z => by rw [Real.norm_eq_abs, abs_of_nonneg (hr.2 z).1]; exact (hr.2 z).2))
  refine ⟨integral_nonneg (fun z => (hr.2 z).1), ?_⟩
  have h := integral_mono hi (integrable_const (1 : ℝ)) (fun z => (hr.2 z).2)
  simpa only [fieldScalarOverlaps, integral_const, measureReal_def, measure_univ, ENNReal.toReal_one,
    one_smul] using h

lemma fieldScalarOverlaps_monotone (L : List (ℝ × ℝ≥0)) (root : ℝ≥0)
    (hL : ∀ av ∈ L, 0 < av.1) {F a : ℝ → ℝ}
    (hF : Measurable F) (hG : HasLinearGrowth F)
    (ha : Measurable a) (haB : ∀ u, |a u| ≤ 1) :
    Monotone (fieldScalarOverlaps L root F a) := by
  have hi (i : Fin (L.length + 1)) : Integrable (fieldScalarSquares L F a i) (gaussianReal 0 root) := by
    have hr := fieldScalarSquares_regular L hL hF hG ha haB i
    exact Integrable.of_bound hr.1.aestronglyMeasurable 1
      (Filter.Eventually.of_forall (fun z => by rw [Real.norm_eq_abs, abs_of_nonneg (hr.2 z).1]; exact (hr.2 z).2))
  intro i j hij
  exact integral_mono (hi i) (hi j) (fun z => fieldScalarSquares_monotone L hL hF hG ha haB z hij)

lemma fieldScalarOverlaps_tied_increment (L : List (ℝ × ℝ≥0)) (root : ℝ≥0)
    (F a : ℝ → ℝ) (i : Fin L.length) (hi : (L.get i).2 = 0) :
    fieldScalarOverlaps L root F a i.castSucc = fieldScalarOverlaps L root F a i.succ := by
  unfold fieldScalarOverlaps
  rw [fieldScalarSquares_tied_increment L F a i hi]

end InvariantIsing

end

end OAI
