import Mathlib
import OAI.Probability.GaussianInformation.Kernel.ReferenceBounds

namespace OAI
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace ReferenceGaussian
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
open GaussianTools

lemma integrable_energy_joint {p d : ℕ} (τ : Measure (Vec d)) [IsProbabilityMeasure τ]
    (s : Vec d) {R : ℝ} (hR : 0 ≤ R) (hs : ∀ᵐ u ∂τ,u ∈ closedBall s R)
    (e : Fin p → ℝ) :
    Integrable (fun t : Mat p d × Vec d => energy t.1 (s-t.2) e)
      ((Measure.pi (fun _ : Fin p => scalarRow d)).prod τ) := by
  have : IsProbabilityMeasure (scalarRow d) := by unfold scalarRow; infer_instance
  have hm : Measurable (fun t : Mat p d × Vec d => energy t.1 (s-t.2) e) := by
    unfold energy applyRows; fun_prop
  apply ((((integrable_matEnergy (p := p) (d := d)).comp_fst τ).const_mul (2*R^2)).add
    (integrable_const (2*∑ i,e i^2))).mono' hm.aestronglyMeasurable
  have hae : ∀ᵐ t : Mat p d × Vec d ∂(Measure.pi (fun _ : Fin p => scalarRow d)).prod τ,
      t.2 ∈ closedBall s R := measurePreserving_snd.quasiMeasurePreserving.ae hs
  filter_upwards [hae] with t ht
  rw [Real.norm_eq_abs,abs_of_nonneg (energy_nonneg _ _ _)]
  have ht' : ‖s-t.2‖ ≤ R := by simpa only [mem_closedBall,dist_eq_norm,norm_sub_rev] using ht
  have hb := energy_le t.1 (s-t.2) e
  have hsq : ‖s-t.2‖^2 ≤ R^2 := (sq_le_sq₀ (norm_nonneg _) hR).mpr ht'
  change energy t.1 (s-t.2) e ≤ 2*R^2*matEnergy t.1+2*∑ i,e i^2
  nlinarith [mul_le_mul_of_nonneg_left hsq (matEnergy_nonneg t.1)]

lemma energy_rows_local_le {p d : ℕ} (τ : Measure (Vec d)) [IsProbabilityMeasure τ]
    (s : Vec d) {R : ℝ} (hR : 0 ≤ R) (hs : ∀ᵐ u ∂τ,u ∈ closedBall s R)
    (e : Fin p → ℝ) :
    (∫ X : Mat p d,∫ u,energy X (s-u) e ∂τ ∂Measure.pi (fun _ : Fin p => scalarRow d)) ≤
      2*(p:ℝ)*R^2+2*∑ i,e i^2 := by
  have : IsProbabilityMeasure (scalarRow d) := by unfold scalarRow; infer_instance
  rw [integral_integral_swap (integrable_energy_joint τ s hR hs e)]
  have hi := (integrable_energy_joint τ s hR hs e).integral_prod_right
  calc
    _ ≤ ∫ _u,2*(p:ℝ)*R^2+2*∑ i,e i^2 ∂τ := by
      apply integral_mono_ae hi (integrable_const _)
      filter_upwards [hs] with u hu
      have hu' : ‖s-u‖ ≤ R := by simpa only [mem_closedBall,dist_eq_norm,norm_sub_rev] using hu
      have hsq : ‖s-u‖^2 ≤ R^2 := pow_le_pow_left₀ (norm_nonneg _) hu' 2
      exact (energy_rows_le (s-u) e).trans (by gcongr)
    _ = _ := by simp

lemma integrable_log_shift_rows {p d : ℕ} (τ : Measure (Vec d)) [IsProbabilityMeasure τ]
    (s : Vec d) {R : ℝ} (hR : 0 ≤ R) (hs : ∀ᵐ u ∂τ,u ∈ closedBall s R)
    {r : ℝ} (hr : 0 < r) (e : Fin p → ℝ) :
    Integrable (fun X : Mat p d => ∫ u,Real.log (atDensity r X (applyRows X s+e) u) ∂τ)
      (Measure.pi (fun _ : Fin p => scalarRow d)) := by
  have : IsProbabilityMeasure (scalarRow d) := by unfold scalarRow; infer_instance
  have hi := (integrable_energy_joint τ s hR hs e).integral_prod_left
  have he (X : Mat p d) :
      (∫ u,Real.log (atDensity r X (applyRows X s+e) u) ∂τ) =
      -(p:ℝ)*Real.log r-(p:ℝ)/2*Real.log (2*Real.pi)-(∫ u,energy X (s-u) e ∂τ)/(2*r^2) := by
    simp_rw [log_atDensity_shift hr]
    have hei : Integrable (fun u => energy X (s-u) e) τ := by
      apply continuous_integrable_on_support τ _ s R hs
      unfold energy applyRows; fun_prop
    rw [integral_sub (integrable_const _) (hei.div_const _),integral_div]
    simp
  simp_rw [he]
  exact (integrable_const _).sub (hi.div_const _)

lemma log_shift_rows_local_ge {p d : ℕ} (τ : Measure (Vec d)) [IsProbabilityMeasure τ]
    (s : Vec d) {R : ℝ} (hR : 0 ≤ R) (hs : ∀ᵐ u ∂τ,u ∈ closedBall s R)
    {r : ℝ} (hr : 0 < r) (e : Fin p → ℝ) :
    -(p:ℝ)*Real.log r-(p:ℝ)/2*Real.log (2*Real.pi)-
      ((p:ℝ)*R^2+∑ i,e i^2)/r^2 ≤
      (∫ X : Mat p d,∫ u,Real.log (atDensity r X (applyRows X s+e) u) ∂τ
        ∂Measure.pi (fun _ : Fin p => scalarRow d)) := by
  have : IsProbabilityMeasure (scalarRow d) := by unfold scalarRow; infer_instance
  simp_rw [log_atDensity_shift hr]
  have hi := integrable_energy_joint τ s hR hs e
  have he (X : Mat p d) :
      (∫ u,-(p:ℝ)*Real.log r-(p:ℝ)/2*Real.log (2*Real.pi)-energy X (s-u) e/(2*r^2) ∂τ) =
      -(p:ℝ)*Real.log r-(p:ℝ)/2*Real.log (2*Real.pi)-(∫ u,energy X (s-u) e ∂τ)/(2*r^2) := by
    have hei : Integrable (fun u => energy X (s-u) e) τ := by
      apply continuous_integrable_on_support τ _ s R hs
      unfold energy applyRows; fun_prop
    rw [integral_sub (integrable_const _) (hei.div_const _),integral_div]; simp
  simp_rw [he]
  rw [integral_sub (integrable_const _) (hi.integral_prod_left.div_const _),integral_div]
  simp only [integral_const,measureReal_def,measure_univ,ENNReal.toReal_one,one_smul]
  have hb := energy_rows_local_le τ s hR hs e
  have hrr : 0 < r^2 := sq_pos_of_pos hr
  have hdiv := (div_le_div_of_nonneg_right hb (by positivity : 0 ≤ 2*r^2))
  have heq : (2*(p:ℝ)*R^2+2*∑ i,e i^2)/(2*r^2)=((p:ℝ)*R^2+∑ i,e i^2)/r^2 := by ring
  rw [heq] at hdiv
  linarith

end ReferenceGaussian

end OAI
