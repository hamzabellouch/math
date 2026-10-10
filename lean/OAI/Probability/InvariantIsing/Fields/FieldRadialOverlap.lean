import OAI.Probability.InvariantIsing.Fields.FieldScalarSquareOrder

namespace OAI

/-! Radial increase of the actual conditional spin products, expressed
in the original Gaussian position units. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped NNReal

namespace InvariantIsing

lemma fieldScalarOverlaps_radial (L : List (ℝ × ℝ≥0)) (root : ℝ≥0)
    (hL : ∀ av ∈ L, 0 < av.1) {c d : ℝ} (hc : 0 ≤ c) (hcd : c ≤ d)
    (i : Fin (L.length + 1)) :
    fieldScalarOverlaps L root (fun z => Real.log (Real.cosh (c * z)))
        (fun z => Real.tanh (c * z)) i ≤
      fieldScalarOverlaps L root (fun z => Real.log (Real.cosh (d * z)))
        (fun z => Real.tanh (d * z)) i := by
  have hd : 0 ≤ d := hc.trans hcd
  have hFm (r : ℝ) : Measurable (fun z => Real.log (Real.cosh (r * z))) :=
    measurable_logCosh.comp (measurable_id.const_mul r)
  have hFg (r : ℝ) : HasLinearGrowth (fun z => Real.log (Real.cosh (r * z))) :=
    logCosh_linearGrowth.scale_argument r
  have hFe (r : ℝ) : Function.Even (fun z => Real.log (Real.cosh (r * z))) := by
    intro z
    simp only [mul_neg, Real.cosh_neg]
  have ham (r : ℝ) : Measurable (fun z => Real.tanh (r * z)) := by
    simp only [Real.tanh_eq]
    fun_prop
  have hao (r : ℝ) : Function.Odd (fun z => Real.tanh (r * z)) := by
    intro z
    simp only [mul_neg, Real.tanh_neg]
  have hamo (r : ℝ) (hr : 0 ≤ r) : MonotoneOn (fun z => Real.tanh (r * z)) (Ici 0) := by
    intro x _hx y _hy hxy
    exact field_tanh_monotone (mul_le_mul_of_nonneg_left hxy hr)
  have hap (r : ℝ) (hr : 0 ≤ r) : ∀ z ∈ Ici (0 : ℝ), 0 ≤ Real.tanh (r * z) :=
    fun z hz => field_tanh_nonneg (mul_nonneg hr hz)
  have haB (r : ℝ) : ∀ z : ℝ, |Real.tanh (r * z)| ≤ 1 :=
    fun z => field_abs_tanh_le_one (r * z)
  have hab : ∀ z ∈ Ici (0 : ℝ), Real.tanh (c * z) ≤ Real.tanh (d * z) :=
    fun z hz => field_tanh_monotone (mul_le_mul_of_nonneg_right hcd hz)
  have horder := fieldScalarSquares_order L hL (hFm c) (hFm d) (hFg c) (hFg d)
    (hFe c) (hFe d) (field_logcosh_scaled_difference_monotone hc hcd)
    (ham c) (ham d) (hao c) (hao d) (hamo c hc) (hamo d hd)
    (hap c hc) (hap d hd) (haB c) (haB d) hab
  have hi (r : ℝ) : Integrable
      (fieldScalarSquares L (fun z => Real.log (Real.cosh (r * z)))
        (fun z => Real.tanh (r * z)) i) (gaussianReal 0 root) := by
    have hr := fieldScalarSquares_regular L hL (hFm r) (hFg r) (ham r) (haB r) i
    exact Integrable.of_bound hr.1.aestronglyMeasurable 1
      (Filter.Eventually.of_forall (fun z => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hr.2 z).1]
        exact (hr.2 z).2))
  exact integral_mono (hi c) (hi d) (horder i)

end InvariantIsing

end

end OAI
