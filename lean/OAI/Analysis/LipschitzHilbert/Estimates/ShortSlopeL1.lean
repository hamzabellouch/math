import OAI.Analysis.LipschitzHilbert.Estimates.ShortSlopeOperator

namespace OAI

/-! Integrable time-kernel errors have direct mass bounds under short
Lipschitz sampling, sufficient for restricted pairings. -/
noncomputable section
open Set MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

theorem shortSlopeOperator_uniform (K : ℝ → ℂ) (hK : Integrable K)
    (u : (ℝ×ℝ) → ℝ) (f : (ℝ×ℝ) → ℂ) (C : ℝ) (hC : 0≤C)
    (hf : ∀ z, ‖f z‖≤C) (z : ℝ×ℝ) :
    ‖shortSlopeOperator K u f z‖≤C*(∫ t, ‖K t‖) := by
  have h := norm_integral_le_of_norm_le (hK.norm.const_mul C)
    (Filter.Eventually.of_forall (fun t => show
      ‖if |t|≤1/4 then K t*f (z.1-t,z.2-t*u z) else 0‖≤C*‖K t‖ from by
      by_cases ht : |t|≤1/4
      · rw [ite_eq_left ht,norm_mul,mul_comm C]
        exact mul_le_mul_of_nonneg_left (hf _) (norm_nonneg _)
      · rw [ite_eq_right ht,norm_zero]
        exact mul_nonneg hC (norm_nonneg _)))
  simpa only [shortSlopeOperator,integral_const_mul] using h

theorem shortSlopeOperator_l1 (K : ℝ → ℂ) (hKm : Measurable K) (hK : Integrable K)
    (u : (ℝ×ℝ) → ℝ) (hu : LipschitzWith 2 u)
    (f : (ℝ×ℝ) → ℂ) (hfm : Measurable f) (hf : Integrable f planeMeasure) :
    Integrable (shortSlopeOperator K u f) planeMeasure ∧
      (∫ z, ‖shortSlopeOperator K u f z‖ ∂planeMeasure)≤
        4*(∫ t, ‖K t‖)*(∫ z, ‖f z‖ ∂planeMeasure) := by
  let F := fun p : ℝ×(ℝ×ℝ) =>
    if |p.1|≤1/4 then f (p.2.1-p.1,p.2.2-p.1*u p.2) else 0
  have hum := hu.continuous.measurable
  have hs : MeasurableSet {p : ℝ×(ℝ×ℝ) | |p.1|≤1/4} := by
    exact (isClosed_le (by fun_prop) continuous_const).measurableSet
  have hFm : Measurable F := (hfm.comp (by fun_prop)).ite hs measurable_const
  have hslice (t : ℝ) : Integrable (fun z => ‖F (t,z)‖) planeMeasure ∧
      (∫ z, ‖F (t,z)‖ ∂planeMeasure)≤4*∫ z, ‖f z‖ ∂planeMeasure := by
    by_cases ht : |t|≤1/4
    · simpa only [F,ite_eq_left ht,Function.comp_def,verticalSampling,sub_zero] using
        planar_integral_comp_le_four (verticalSampling u t t 0)
          (verticalSampling_measurable u hum t t 0)
          (verticalSampling_antilipschitz u hu t t 0 ht) (fun z => ‖f z‖) hf.norm
          (fun _ => norm_nonneg _)
    · simp only [F,ite_eq_right ht,norm_zero,integral_zero]
      exact ⟨integrable_zero _ _ _,by positivity⟩
  let H := fun p : ℝ×(ℝ×ℝ) => K p.1*F p
  have hHm : Measurable H := (hKm.comp measurable_fst).mul hFm
  have hHi : Integrable H (volume.prod planeMeasure) := by
    apply (integrable_prod_iff hHm.aestronglyMeasurable).2
    constructor
    · exact Filter.Eventually.of_forall fun t =>
        ((hslice t).1.mono
          (hFm.comp (by fun_prop)).aestronglyMeasurable
          (Filter.Eventually.of_forall fun _ => by simp)).const_mul (K t)
    · apply (hK.norm.mul_const (4*∫ z, ‖f z‖ ∂planeMeasure)).mono'
        hHm.norm.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable
      filter_upwards [] with t
      change ‖∫ z, ‖K t*F (t,z)‖ ∂planeMeasure‖≤_
      simp only [norm_mul,integral_const_mul]
      rw [Real.norm_of_nonneg (norm_nonneg _),
        Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
      exact mul_le_mul_of_nonneg_left (hslice t).2 (norm_nonneg _)
  have heq (z : ℝ×ℝ) : (∫ t, H (t,z))=shortSlopeOperator K u f z := by
    apply integral_congr_ae
    filter_upwards [] with t
    dsimp only [H,F]
    split_ifs <;> simp
  have hbound (z : ℝ×ℝ) : ‖shortSlopeOperator K u f z‖≤∫ t, ‖H (t,z)‖ := by
    rw [←heq]
    exact norm_integral_le_integral_norm _
  refine ⟨?_,?_⟩
  · simpa only [heq] using hHi.integral_prod_right
  · calc
      _ ≤ ∫ z : ℝ×ℝ, (∫ t : ℝ, ‖H (t,z)‖) ∂planeMeasure :=
        integral_mono (by simpa only [heq] using hHi.integral_prod_right.norm)
          hHi.norm.integral_prod_right hbound
      _ = ∫ t, ∫ z, ‖H (t,z)‖ ∂planeMeasure :=
        integral_integral_swap (f:=fun (z : ℝ×ℝ) (t : ℝ) => ‖H (t,z)‖) hHi.norm.swap
      _ ≤ ∫ t, ‖K t‖*(4*∫ z, ‖f z‖ ∂planeMeasure) := by
        apply integral_mono hHi.norm.integral_prod_left (hK.norm.mul_const _)
        intro t
        simp only [H,norm_mul,integral_const_mul]
        exact mul_le_mul_of_nonneg_left (hslice t).2 (norm_nonneg _)
      _ = _ := by rw [integral_mul_const]; ring

end LipschitzHilbert.PacketRepresentation

end

end OAI
