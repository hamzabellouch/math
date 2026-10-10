import OAI.Probability.InvariantIsing.Fields.FieldScalarOverlap
import OAI.Probability.InvariantIsing.Fields.FieldCovarianceScaling

namespace OAI

/-! Change of position units for the actual finite conditional spin
chain. The spin observable acquires no multiplicative derivative factor. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped NNReal

namespace InvariantIsing

def fieldScaleIncrements (c : ℝ≥0) (L : List (ℝ × ℝ≥0)) : List (ℝ × ℝ≥0) :=
  L.map (fun av => (av.1, c ^ 2 * av.2))

lemma fieldScaleIncrements_length (c : ℝ≥0) (L : List (ℝ × ℝ≥0)) :
    (fieldScaleIncrements c L).length = L.length := by
  simp only [fieldScaleIncrements, List.length_map]

private lemma scalar_value_measurable (L : List (ℝ × ℝ≥0))
    {F : ℝ → ℝ} (hF : Measurable F) : Measurable (fieldScalarValue L F) := by
  induction L with
  | nil => exact hF
  | cons av L ih =>
    change Measurable (gaussianOperator av.1 av.2 (fieldScalarValue L F))
    rw [gaussianOperator_eq_transform]
    exact measurable_gaussianTransform ih _ _

private lemma scalar_mean_measurable (L : List (ℝ × ℝ≥0))
    {F a : ℝ → ℝ} (hF : Measurable F) (ha : Measurable a) :
    Measurable (fieldScalarMean L F a) := by
  induction L with
  | nil => exact ha
  | cons av L ih =>
    exact measurable_fieldSpinTransition av.1 av.2 (scalar_value_measurable L hF) ih

private lemma scalar_squares_measurable (L : List (ℝ × ℝ≥0))
    {F a : ℝ → ℝ} (hF : Measurable F) (ha : Measurable a) :
    ∀ i, Measurable (fieldScalarSquares L F a i) := by
  induction L with
  | nil => intro i; exact ha.pow_const 2
  | cons av L ih =>
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact (scalar_mean_measurable (av :: L) hF ha).pow_const 2
    · exact measurable_fieldSpinTransition av.1 av.2 (scalar_value_measurable L hF) (ih j)

lemma fieldSpinTransition_scale_position (ζ : ℝ) (v c : ℝ≥0)
    {F a : ℝ → ℝ} (hF : Measurable F) (ha : Measurable a) (z : ℝ) :
    fieldSpinTransition ζ v (fun u => F (c * u)) (fun u => a (c * u)) z =
      fieldSpinTransition ζ (c ^ 2 * v) F a (c * z) := by
  have hFc : Measurable (fun u => F ((c : ℝ) * u)) := hF.comp (measurable_id.const_mul _)
  have hac : Measurable (fun u => a ((c : ℝ) * u)) := ha.comp (measurable_id.const_mul _)
  rw [fieldSpinTransition_eq_standard ζ v hFc hac,
    fieldSpinTransition_eq_standard ζ (c ^ 2 * v) hF ha,
    gaussianTiltAverage_eq_div, gaussianTiltAverage_eq_div]
  have hs : Real.sqrt ((c ^ 2 * v : ℝ≥0) : ℝ) = c * Real.sqrt (v : ℝ) := by
    rw [NNReal.coe_mul, NNReal.coe_pow, Real.sqrt_mul (sq_nonneg _),
      Real.sqrt_sq c.coe_nonneg]
  have he (u : ℝ) : (c : ℝ) * (z + Real.sqrt (v : ℝ) * u) =
      c * z + (c * Real.sqrt (v : ℝ)) * u := by ring
  simp only [hs, he]

lemma fieldScalarValue_scale_position (c : ℝ≥0) (L : List (ℝ × ℝ≥0))
    (F : ℝ → ℝ) (z : ℝ) :
    fieldScalarValue L (fun u => F (c * u)) z =
      fieldScalarValue (fieldScaleIncrements c L) F (c * z) := by
  induction L generalizing z with
  | nil => rfl
  | cons av L ih =>
    have he : fieldScalarValue L (fun u => F (c * u)) =
        fun u => fieldScalarValue (fieldScaleIncrements c L) F (c * u) := funext ih
    change gaussianOperator av.1 av.2 (fieldScalarValue L (fun u => F (c * u))) z =
      gaussianOperator av.1 (c ^ 2 * av.2 : ℝ≥0) (fieldScalarValue (fieldScaleIncrements c L) F) (c * z)
    rw [he]
    simpa only [NNReal.coe_mul, NNReal.coe_pow] using
      gaussianOperator_scale_position av.1 av.2 c c.coe_nonneg _ z

lemma fieldScalarMean_scale_position (c : ℝ≥0) (L : List (ℝ × ℝ≥0))
    {F a : ℝ → ℝ} (hF : Measurable F) (ha : Measurable a) (z : ℝ) :
    fieldScalarMean L (fun u => F (c * u)) (fun u => a (c * u)) z =
      fieldScalarMean (fieldScaleIncrements c L) F a (c * z) := by
  induction L generalizing z with
  | nil => rfl
  | cons av L ih =>
    have hv : fieldScalarValue L (fun u => F (c * u)) =
        fun u => fieldScalarValue (fieldScaleIncrements c L) F (c * u) :=
      funext (fieldScalarValue_scale_position c L F)
    have hm : fieldScalarMean L (fun u => F (c * u)) (fun u => a (c * u)) =
        fun u => fieldScalarMean (fieldScaleIncrements c L) F a (c * u) := funext ih
    change fieldSpinTransition av.1 av.2 (fieldScalarValue L (fun u => F (c * u)))
        (fieldScalarMean L (fun u => F (c * u)) (fun u => a (c * u))) z =
      fieldSpinTransition av.1 (c ^ 2 * av.2) (fieldScalarValue (fieldScaleIncrements c L) F)
        (fieldScalarMean (fieldScaleIncrements c L) F a) (c * z)
    rw [hv, hm]
    exact fieldSpinTransition_scale_position av.1 av.2 c
      (scalar_value_measurable _ hF) (scalar_mean_measurable _ hF ha) z

lemma fieldScalarSquares_scale_position (c : ℝ≥0) (L : List (ℝ × ℝ≥0))
    {F a : ℝ → ℝ} (hF : Measurable F) (ha : Measurable a)
    (i : Fin (L.length + 1)) (z : ℝ) :
    fieldScalarSquares L (fun u => F (c * u)) (fun u => a (c * u)) i z =
      fieldScalarSquares (fieldScaleIncrements c L) F a
        (Fin.cast (by rw [fieldScaleIncrements_length]) i) (c * z) := by
  induction L generalizing z with
  | nil => rfl
  | cons av L ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa only [Fin.cast_zero, fieldScalarSquares_zero] using
        congrArg (fun x : ℝ => x ^ 2) (fieldScalarMean_scale_position c (av :: L) hF ha z)
    · have hv : fieldScalarValue L (fun u => F (c * u)) =
          fun u => fieldScalarValue (fieldScaleIncrements c L) F (c * u) :=
        funext (fieldScalarValue_scale_position c L F)
      have hq : fieldScalarSquares L (fun u => F (c * u)) (fun u => a (c * u)) j =
          fun u => fieldScalarSquares (fieldScaleIncrements c L) F a
            (Fin.cast (by simp only [fieldScaleIncrements_length, List.length_cons]) j) (c * u) := funext (ih j)
      change fieldSpinTransition av.1 av.2 (fieldScalarValue L (fun u => F (c * u)))
          (fieldScalarSquares L (fun u => F (c * u)) (fun u => a (c * u)) j) z =
        fieldSpinTransition av.1 (c ^ 2 * av.2) (fieldScalarValue (fieldScaleIncrements c L) F)
          (fieldScalarSquares (fieldScaleIncrements c L) F a
            (Fin.cast (by simp only [fieldScaleIncrements_length, List.length_cons]) j)) (c * z)
      rw [hv, hq]
      exact fieldSpinTransition_scale_position av.1 av.2 c
        (scalar_value_measurable _ hF) (scalar_squares_measurable _ hF ha _) z

lemma fieldScalarOverlaps_scale_position (c : ℝ≥0) (L : List (ℝ × ℝ≥0))
    (root : ℝ≥0) {F a : ℝ → ℝ} (hF : Measurable F) (ha : Measurable a)
    (i : Fin (L.length + 1)) :
    fieldScalarOverlaps L root (fun u => F (c * u)) (fun u => a (c * u)) i =
      fieldScalarOverlaps (fieldScaleIncrements c L) (c ^ 2 * root) F a
        (Fin.cast (by rw [fieldScaleIncrements_length]) i) := by
  have hs : NNReal.mk ((c : ℝ) ^ 2) (sq_nonneg _) = c ^ 2 := by
    apply Subtype.ext
    rfl
  have hm : (gaussianReal 0 root).map (fun u : ℝ => (c : ℝ) * u) =
      gaussianReal 0 (c ^ 2 * root) := by
    simpa only [mul_zero, hs] using
      gaussianReal_map_const_mul (μ := 0) (v := root) (c : ℝ)
  unfold fieldScalarOverlaps
  simp_rw [fieldScalarSquares_scale_position c L hF ha i]
  rw [← hm]
  have hc : Measurable (fun u : ℝ => (c : ℝ) * u) := measurable_const.mul measurable_id
  exact (integral_map hc.aemeasurable
    (scalar_squares_measurable _ hF ha _).aestronglyMeasurable).symm

end InvariantIsing

end

end OAI
