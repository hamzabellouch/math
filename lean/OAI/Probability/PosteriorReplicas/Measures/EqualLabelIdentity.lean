import OAI.Probability.PosteriorReplicas.Measures.EqualRightMeasure
import OAI.Probability.PosteriorReplicas.Measures.TiltNormalization

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology BoundedContinuousFunction
noncomputable section
namespace PosteriorReplicas

lemma equal_base_measures {d k m : ℕ} (hd : k + m + 2 ≤ d)
    (hk : 1 ≤ k) (hm : 1 ≤ m) (base : BaseLaw) :
    leftBaseMeasure d k m base = rightBaseMeasure d k m base := by
  have := leftBaseMeasure_finite hd hk base
  apply ext_of_forall_lintegral_eq_of_IsFiniteMeasure
  intro H
  have hc : Continuous (fun z => (H z : ℝ≥0∞)) := ENNReal.continuous_coe.comp H.continuous
  have hb : ∀ z, (H z : ℝ≥0∞) ≤ (nndist 0 H : ℝ≥0∞) :=
    fun z => ENNReal.coe_le_coe.mpr (H.apply_le_nndist_zero z)
  exact tendsto_nhds_unique
    (equalApprox_left_limit hd hk hm base hc _ ENNReal.coe_ne_top hb)
    (equalApprox_right_limit hd hk hm base hc _ ENNReal.coe_ne_top hb)

lemma equal_label_base_identity {d k m : ℕ} (hd : k + m + 2 ≤ d)
    (hk : 1 ≤ k) (hm : 1 ≤ m) (base : BaseLaw)
    {H : EqualSpace d k m → ℝ≥0∞} (hH : Measurable H) :
    equalLabelLeft base (fun _ => 1) H = equalLabelRight base (fun _ => 1) H := by
  rw [← leftBaseMeasure_eq_equalLabelLeft (by omega) (by omega) base hH,
    equal_base_measures hd hk hm base,
    rightBaseMeasure_eq_equalLabelRight (by omega) (by omega) base hH]

lemma equal_label_tilt_identity {d k m : ℕ} (hd : k + m + 2 ≤ d)
    (hk : 1 ≤ k) (hm : 1 ≤ m) (base : BaseLaw) {f : Vec d → ℝ≥0∞}
    (hf : Measurable f) {L : ℝ≥0∞} (hL : L ≠ ∞) (hfL : ∀ x, f x ≤ L)
    {H : EqualSpace d k m → ℝ≥0∞} (hH : Measurable H) :
    equalLabelLeft base f H = equalLabelRight base f H := by
  have : NeZero d := ⟨by omega⟩
  rw [equalLabelLeft_tilt base hf hL hfL hH, equalLabelRight_tilt base hf hL hfL hH]
  exact equal_label_base_identity hd hk hm base (by fun_prop)

lemma equal_label_tilt_finite {d k m : ℕ} (hd : k + m + 2 ≤ d)
    (hk : 1 ≤ k) (hm : 1 ≤ m) (base : BaseLaw) {f : Vec d → ℝ≥0∞}
    (hf : Measurable f) {L : ℝ≥0∞} (hL : L ≠ ∞) (hfL : ∀ x, f x ≤ L) :
    equalLabelLeft (k := k) (m := m) base f (fun _ => 1) < ∞ := by
  have := leftBaseMeasure_finite hd hk base
  rw [equalLabelLeft_tilt base hf hL hfL measurable_const,
    ← leftBaseMeasure_eq_equalLabelLeft (by omega) (by omega) base (by fun_prop)]
  apply lt_of_le_of_lt (lintegral_mono (g := fun _ => L^(m+1)) ?_)
    (by simpa using ENNReal.mul_lt_top (ENNReal.pow_lt_top (lt_top_iff_ne_top.mpr hL)) (measure_lt_top _ univ))
  intro z
  simp only [mul_one]
  simpa using Finset.prod_le_prod (fun i (_ : i ∈ (Finset.univ : Finset (Fin (m+1)))) => hfL (z.2.2 i))

theorem equalLabelMeasureIdentity : EqualLabelMeasureIdentity := by
  intro d k m hk hm hd base f hf hbounded
  obtain ⟨L,hL,hfL⟩ := hbounded
  have hdim : k + m + 2 ≤ d := by omega
  exact ⟨equal_label_tilt_finite hdim hk hm base hf hL hfL,
    fun H hH => equal_label_tilt_identity hdim hk hm base hf hL hfL hH⟩

end PosteriorReplicas
end

end OAI
