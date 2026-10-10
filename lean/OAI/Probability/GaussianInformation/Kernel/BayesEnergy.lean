import Mathlib
import OAI.Probability.GaussianInformation.Kernel.EntropyComparison

namespace OAI
open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory
open scoped ENNReal
namespace KernelPotential.Bayes
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open Coercivity Sphere Reweight

lemma clippedJ_upper {d : ℕ} (hd : 16 ≤ d) (ν : Measure (Ambient d))
    [IsProbabilityMeasure ν] {H : ℝ} (hH : 0 < H)
    (hν : ν ≤ ENNReal.ofReal H • sphereProbability d) (s : Ambient d) :
    clippedJ ν s ≤ max ((1/2:ℝ)^(2*(d/16))) (H*(1+9*3^d*2^((d-1)+2*(d/16)+1))) := by
  apply max_le_max le_rfl
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top (bounded_J hd ν hH hν s)).trans_eq
    (ENNReal.toReal_ofReal (by positivity))

lemma referenceWeight_measurable {d : ℕ} (ν : Measure (Ambient d)) [IsFiniteMeasure ν]
    (r : Ambient d → ℝ) (hr : Measurable r) (hr0 : ∀ s,0 ≤ r s) (hr1 : ∀ s,r s ≤ 1)
    (ha : 0 < mass ν r) : Measurable (referenceWeight ν r) := by
  have := post_probability ν r hr hr0 hr1 ha
  exact hr.div (measurable_const.mul (clippedJ_measurable _))

lemma referenceWeight_bounds {d : ℕ} (hd : 16 ≤ d) (ν : Measure (Ambient d))
    [IsProbabilityMeasure ν] {H : ℝ} (hH : 0 < H)
    (hν : ν ≤ ENNReal.ofReal H • sphereProbability d)
    (r : Ambient d → ℝ) (hr : Measurable r) {ε : ℝ} (hε : 0 < ε)
    (hrε : ∀ s,ε ≤ r s) (hr1 : ∀ s,r s ≤ 1) :
    ∃ a b : ℝ,0 < a ∧ ∀ s,a ≤ referenceWeight ν r s ∧ referenceWeight ν r s ≤ b := by
  have ha := hε.trans_le (mass_bounds ν r hr hε hrε hr1).1
  have := post_probability ν r hr (fun s => hε.le.trans (hrε s)) hr1 ha
  have hp := post_bounded ν hH hν r hr1 ha
  let U := max ((1/2:ℝ)^(2*(d/16))) ((H/mass ν r)*(1+9*3^d*2^((d-1)+2*(d/16)+1)))
  have hU : 0 < U := lt_of_lt_of_le (by positivity) (le_max_left _ _)
  refine ⟨ε/(mass ν r*U),1/(mass ν r*((1/2:ℝ)^(2*(d/16)))),by positivity,?_⟩
  intro s
  have hj := clippedJ_pos (post ν r) s
  constructor
  · exact (div_le_div_of_nonneg_left hε.le (mul_pos ha hj)
      (mul_le_mul_of_nonneg_left (clippedJ_upper hd _ (div_pos hH ha) hp s) ha.le)).trans
      (div_le_div_of_nonneg_right (hrε s) (mul_nonneg ha.le hj.le))
  · exact (div_le_div_of_nonneg_right (hr1 s) (mul_nonneg ha.le hj.le)).trans
      (div_le_div_of_nonneg_left (by norm_num) (by positivity)
        (mul_le_mul_of_nonneg_left (le_max_left _ _) ha.le))

lemma rho_post_eq_weight {d : ℕ} (hd : 16 ≤ d) (ν : Measure (Ambient d))
    [IsProbabilityMeasure ν] {H : ℝ} (hH : 0 < H)
    (hν : ν ≤ ENNReal.ofReal H • sphereProbability d)
    (r : Ambient d → ℝ) (hr : Measurable r) (hr0 : ∀ s,0 ≤ r s) (hr1 : ∀ s,r s ≤ 1)
    (ha : 0 < mass ν r) :
    rho (post ν r)=ν.withDensity (fun s => ENNReal.ofReal (referenceWeight ν r s)) := by
  have := post_probability ν r hr hr0 hr1 ha
  have hp := post_bounded ν hH hν r hr1 ha
  have hA : Measurable (fun s => ENNReal.ofReal (r s/mass ν r)) := (hr.div_const _).ennreal_ofReal
  have hJ : Measurable (fun s => (J (post ν r) s)⁻¹) := (measurable_J _).inv
  change (ν.withDensity (fun s => ENNReal.ofReal (r s/mass ν r))).withDensity
    (fun s => (J (post ν r) s)⁻¹)=_
  rw [← withDensity_mul _ hA hJ]
  apply withDensity_congr_ae
  filter_upwards [(Measure.absolutelyContinuous_of_le_smul hν).ae_le (ae_unit_norm (by omega : 0 < d))] with s hs
  have hJfin : J (post ν r) s ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    (bounded_J hd _ (div_pos hH ha) hp s)
  have hJp : 0 < (J (post ν r) s).toReal := lt_of_lt_of_le (by positivity)
    (J_real_bounds hd _ (div_pos hH ha) hp s hs).1
  change ENNReal.ofReal (r s/mass ν r)*(J (post ν r) s)⁻¹=_
  rw [referenceWeight,clippedJ_eq hd _ (div_pos hH ha) hp s hs]
  rw [show r s/(mass ν r*(J (post ν r) s).toReal)=(r s/mass ν r)*((J (post ν r) s).toReal)⁻¹ by ring,
    ENNReal.ofReal_mul (div_nonneg (hr0 s) ha.le),ENNReal.ofReal_inv_of_pos hJp,ENNReal.ofReal_toReal hJfin]

lemma C_eq_projectedReference {d k : ℕ} (hd : 16 ≤ d) (ν : Measure (Ambient d))
    [IsProbabilityMeasure ν] {H : ℝ} (hH : 0 < H)
    (hν : ν ≤ ENNReal.ofReal H • sphereProbability d)
    (r : Ambient d → ℝ) (hr : Measurable r) (hr0 : ∀ s,0 ≤ r s) (hr1 : ∀ s,r s ≤ 1)
    (ha : 0 < mass ν r) (η : ℝ) (z : Noise.Observation k d) :
    (∫⁻ s,Noise.observationKernel η z s*ENNReal.ofReal (referenceWeight ν r s) ∂ν)=
      Noise.projectedReference (post ν r) η z.1.1 z.1.2 z.2.1 z.2.2 := by
  rw [Noise.projectedReference,rho_post_eq_weight hd ν hH hν r hr hr0 hr1 ha]
  have hK : Measurable (fun s => Noise.observationKernel η z s) := by
    have hKall := Noise.observationKernel_measurable (k := k) (d := d) η
    fun_prop
  change _=(∫⁻ s,Noise.observationKernel η z s ∂ν.withDensity (fun s => ENNReal.ofReal (referenceWeight ν r s)))
  rw [lintegral_withDensity_eq_lintegral_mul _
    (referenceWeight_measurable ν r hr hr0 hr1 ha).ennreal_ofReal hK]
  apply lintegral_congr
  intro s
  exact mul_comm _ _
end KernelPotential.Bayes

end OAI
