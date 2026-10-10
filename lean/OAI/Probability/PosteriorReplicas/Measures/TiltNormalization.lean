import OAI.Probability.PosteriorReplicas.Measures.EqualBaseMeasures

namespace OAI

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
noncomputable section
namespace PosteriorReplicas

lemma bounded_withDensity_finite {X : Type*} [MeasurableSpace X] (μ : Measure X)
    [IsFiniteMeasure μ] {f : X → ℝ≥0∞} {L : ℝ≥0∞} (hL : L ≠ ∞) (hfL : ∀ x, f x ≤ L) :
    IsFiniteMeasure (μ.withDensity f) := by
  apply isFiniteMeasure_withDensity
  exact ne_top_of_le_ne_top (by simpa using ENNReal.mul_ne_top hL (measure_ne_top μ univ))
    (lintegral_mono hfL)

lemma tiltedFiber_probability {d k : ℕ} (base : BaseLaw) {f : Vec d → ℝ≥0∞}
    {L : ℝ≥0∞} (hL : L ≠ ∞) (hfL : ∀ x, f x ≤ L) (A : Rows d k) (y : Labels k) :
    IsProbabilityMeasure (tiltedFiber base f A y) := by
  unfold tiltedFiber
  split_ifs with ha
  · infer_instance
  · constructor
    rw [Measure.smul_apply, smul_eq_mul, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    change (tiltMass base f A y)⁻¹ * tiltMass base f A y = 1
    exact ENNReal.inv_mul_cancel ha (tiltMass_ne_top base hL hfL A y)

lemma tiltMass_smul_tiltedFiber {d k : ℕ} (base : BaseLaw) {f : Vec d → ℝ≥0∞}
    (hf : Measurable f) {L : ℝ≥0∞} (hL : L ≠ ∞) (hfL : ∀ x, f x ≤ L)
    (A : Rows d k) (y : Labels k) :
    tiltMass base f A y • tiltedFiber base f A y = (baseFiber base A y).withDensity f := by
  by_cases ha : tiltMass base f A y = 0
  · have hz : f =ᵐ[baseFiber base A y] 0 := (lintegral_eq_zero_iff hf).mp ha
    rw [ha, zero_smul, withDensity_congr_ae hz, withDensity_zero]
  · rw [tiltedFiber, ite_eq_right ha, smul_smul,
      ENNReal.mul_inv_cancel ha (tiltMass_ne_top base hL hfL A y), one_smul]

lemma pi_tiltMass_smul {d k n : ℕ} (base : BaseLaw) {f : Vec d → ℝ≥0∞}
    (hf : Measurable f) {L : ℝ≥0∞} (hL : L ≠ ∞) (hfL : ∀ x, f x ≤ L)
    (A : Rows d k) (y : Labels k) :
    Measure.pi (fun _ : Fin n => (baseFiber base A y).withDensity f) =
      (tiltMass base f A y)^n • Measure.pi (fun _ : Fin n => tiltedFiber base f A y) := by
  have := bounded_withDensity_finite (baseFiber base A y) hL hfL
  have := tiltedFiber_probability base hL hfL A y
  apply Measure.pi_eq
  intro s hs
  rw [Measure.smul_apply, smul_eq_mul, Measure.pi_pi]
  simp_rw [← tiltMass_smul_tiltedFiber base hf hL hfL A y, Measure.smul_apply,
    smul_eq_mul]
  rw [Finset.prod_mul_distrib]
  simp

lemma weighted_fiber_pi_integral {d k n : ℕ} (base : BaseLaw) {f : Vec d → ℝ≥0∞}
    (hf : Measurable f) {L : ℝ≥0∞} (hL : L ≠ ∞) (hfL : ∀ x, f x ≤ L)
    (A : Rows d k) (y : Labels k) {g : (Fin n → Vec d) → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ u, (∏ i, f (u i)) * g u ∂Measure.pi (fun _ => baseFiber base A y) =
      (tiltMass base f A y)^n * ∫⁻ u, g u ∂Measure.pi (fun _ => tiltedFiber base f A y) := by
  have := bounded_withDensity_finite (baseFiber base A y) hL hfL
  have he := lintegral_withDensity_eq_lintegral_mul
    (Measure.pi (fun _ : Fin n => baseFiber base A y))
    (show Measurable (fun u : Fin n → Vec d => ∏ i, f (u i)) by fun_prop) hg
  simp only [Pi.mul_apply] at he
  rw [← he, ← pi_withDensity _ _ (fun _ => hf), pi_tiltMass_smul base hf hL hfL A y,
    lintegral_smul_measure, smul_eq_mul]

lemma equalLabelLeft_tilt {d k m : ℕ} (base : BaseLaw) {f : Vec d → ℝ≥0∞}
    (hf : Measurable f) {L : ℝ≥0∞} (hL : L ≠ ∞) (hfL : ∀ x, f x ≤ L)
    {H : EqualSpace d k m → ℝ≥0∞} (hH : Measurable H) :
    equalLabelLeft base f H = equalLabelLeft base (fun _ => 1)
      (fun z => (∏ i, f (z.2.2 i)) * H z) := by
  unfold equalLabelLeft
  simp only [projectedDensity, tiltMass_one, mul_one, tiltedFiber_one]
  apply lintegral_congr
  intro A
  apply lintegral_congr
  intro y
  rw [weighted_fiber_pi_integral base hf hL hfL A y (by fun_prop), mul_pow, mul_assoc]

lemma equalLabelRight_tilt {d k m : ℕ} [NeZero d] (base : BaseLaw) {f : Vec d → ℝ≥0∞}
    (hf : Measurable f) {L : ℝ≥0∞} (hL : L ≠ ∞) (hfL : ∀ x, f x ≤ L)
    {H : EqualSpace d k m → ℝ≥0∞} (hH : Measurable H) :
    equalLabelRight base f H = equalLabelRight base (fun _ => 1)
      (fun z => (∏ i, f (z.2.2 i)) * H z) := by
  have := bounded_withDensity_finite (base.measure d) hL hfL
  unfold equalLabelRight
  simp only [show (fun _ : Vec d => (1 : ℝ≥0∞)) = 1 from rfl, withDensity_one]
  rw [pi_withDensity _ _ (fun _ => hf)]

  have hfprod : Measurable (fun u : Tuple d m => ∏ i, f (u i)) := by fun_prop
  rw [lintegral_withDensity_eq_lintegral_mul_non_measurable _ hfprod
    (Filter.Eventually.of_forall fun u => lt_top_iff_ne_top.mpr
      (ENNReal.prod_ne_top (fun i _ => ne_top_of_le_ne_top hL (hfL _))))]
  congr 1
  apply lintegral_congr
  intro u
  rw [lintegral_const_mul _ (show Measurable
    (fun rows : Rows d k => H (rows, labels rows (u 0), u)) from hH.comp (by fun_prop))]
  dsimp only [Pi.mul_apply]
  ac_rfl

end PosteriorReplicas
end

end OAI
