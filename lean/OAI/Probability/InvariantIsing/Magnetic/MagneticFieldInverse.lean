import OAI.Probability.InvariantIsing.Magnetic.MagneticFieldCurvature

namespace OAI

/-! The unique interior minimizing bias is the inverse physical mean-spin
map. Its derivative and the magnetization envelope formula are actual
consequences of the scalar Gaussian recursion. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set Filter
open scoped Topology

namespace InvariantIsing

def magneticBias (h : FieldStep) : ℝ → ℝ := Function.invFun (fieldBiasMean h)

lemma fieldBiasMean_magneticBias (h : FieldStep) {s : ℝ} (hs : |s| < 1) :
    fieldBiasMean h (magneticBias h s) = s := by
  obtain ⟨b, hb⟩ := exists_magneticBias_minimum h hs
  exact Function.invFun_eq ⟨b, magneticBiasMean_eq_of_minimum h hb⟩

lemma magneticBias_minimizes (h : FieldStep) {s : ℝ} (hs : |s| < 1) :
    ∀ c, magneticBiasObjective h s (magneticBias h s) ≤ magneticBiasObjective h s c := by
  obtain ⟨b, hb⟩ := exists_magneticBias_minimum h hs
  have he : magneticBias h s = b := (strictMono_fieldBiasMean h).injective
    ((fieldBiasMean_magneticBias h hs).trans (magneticBiasMean_eq_of_minimum h hb).symm)
  rwa [he]

lemma constrainedFieldValue_magneticBias (h : FieldStep) {s : ℝ} (hs : |s| < 1) :
    constrainedFieldValue h s = fieldValue h (magneticBias h s) - magneticBias h s * s :=
  constrainedFieldValue_eq_at_minimum h (magneticBias_minimizes h hs)

lemma continuousAt_magneticBias (h : FieldStep) {s : ℝ} (hs : |s| < 1) :
    ContinuousAt (magneticBias h) s := by
  have hs' := abs_lt.mp hs
  have hN : Ioo (-1 : ℝ) 1 ∈ 𝓝 s := Ioo_mem_nhds hs'.1 hs'.2
  apply tendsto_order.2
  constructor
  · intro l hl
    have hm : fieldBiasMean h l < s := by
      rw [← fieldBiasMean_magneticBias h hs]
      exact strictMono_fieldBiasMean h hl
    filter_upwards [hN, Ioi_mem_nhds hm] with t ht hmt
    apply (strictMono_fieldBiasMean h).lt_iff_lt.mp
    rw [fieldBiasMean_magneticBias h (abs_lt.mpr ht)]
    exact hmt
  · intro u hu
    have hm : s < fieldBiasMean h u := by
      rw [← fieldBiasMean_magneticBias h hs]
      exact strictMono_fieldBiasMean h hu
    filter_upwards [hN, Iio_mem_nhds hm] with t ht hmt
    apply (strictMono_fieldBiasMean h).lt_iff_lt.mp
    rw [fieldBiasMean_magneticBias h (abs_lt.mpr ht)]
    exact hmt

lemma hasDerivAt_magneticBias (h : FieldStep) {s : ℝ} (hs : |s| < 1) :
    HasDerivAt (magneticBias h) (fieldBiasCurvature h (magneticBias h s))⁻¹ s := by
  have hs' := abs_lt.mp hs
  apply HasDerivAt.of_local_left_inverse (continuousAt_magneticBias h hs)
    (hasDerivAt_fieldBiasMean h (magneticBias h s))
    (fieldBiasCurvature_pos h _).ne'
  filter_upwards [Ioo_mem_nhds hs'.1 hs'.2] with t ht
  exact fieldBiasMean_magneticBias h (abs_lt.mpr ht)

lemma hasDerivAt_constrainedFieldValue_magnetization (h : FieldStep) {s : ℝ}
    (hs : |s| < 1) :
    HasDerivAt (constrainedFieldValue h) (-magneticBias h s) s := by
  have hb := hasDerivAt_magneticBias h hs
  have hd := ((hasDerivAt_fieldValue_bias h (magneticBias h s)).comp s hb).sub
    (hb.mul (hasDerivAt_id s))
  have he : (fun t => fieldValue h (magneticBias h t) - magneticBias h t * t) =ᶠ[𝓝 s]
      constrainedFieldValue h := by
    have hs' := abs_lt.mp hs
    filter_upwards [Ioo_mem_nhds hs'.1 hs'.2] with t ht
    exact (constrainedFieldValue_magneticBias h (abs_lt.mpr ht)).symm
  have heq : fieldBiasMean h (magneticBias h s) *
      (fieldBiasCurvature h (magneticBias h s))⁻¹ -
      ((fieldBiasCurvature h (magneticBias h s))⁻¹ * s + magneticBias h s * 1) =
      -magneticBias h s := by
    rw [fieldBiasMean_magneticBias h hs]
    ring
  simp only [id_eq] at hd
  rw [heq] at hd
  exact hd.congr_of_eventuallyEq he.symm

end InvariantIsing

end

end OAI
