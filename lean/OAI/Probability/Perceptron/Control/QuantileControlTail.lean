import Mathlib
import OAI.Probability.Perceptron.Control.StepControlTail
import OAI.Probability.Perceptron.Control.QuantileControlContinuity
import OAI.Probability.Perceptron.Variational.QuantileUpperTail

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators
namespace SphericalPerceptronFreeEnergy

lemma sampledQuantile_tail_order (n : ℕ) {q r : Time→Time} (hq : Monotone q) (hr : Monotone r)
    (ht : ∀ t : Time, (∫ u in Ici t, (q u:ℝ) ∂timeLaw) ≤ ∫ u in Ici t, (r u:ℝ) ∂timeLaw)
    (k : ℕ) : 0 ≤ ∑ i : Fin (n+1), if k ≤ i.val then
      (1/(n+1:ℝ))*((uniformQuantileUpper n r i:ℝ)-uniformQuantileLower n q i) else 0 := by
  by_cases hk : k<n+1
  · let j : Fin (n+1) := ⟨k,hk⟩
    have h1 : (∫ u in Ici (uniformQuantileGrid n j.castSucc), (sampleQuantileLower n q u:ℝ) ∂timeLaw) ≤
        ∫ u in Ici (uniformQuantileGrid n j.castSucc), (sampleQuantileUpper n r u:ℝ) ∂timeLaw := by
      calc
        _ ≤ ∫ u in Ici (uniformQuantileGrid n j.castSucc), (q u:ℝ) ∂timeLaw := by
          apply integral_mono (unit_valued_integrable _ (sampleQuantileLower_mono n hq).measurable)
            (unit_valued_integrable _ hq.measurable)
          exact fun u => (sampleQuantile_bracket n hq u).1
        _ ≤ ∫ u in Ici (uniformQuantileGrid n j.castSucc), (r u:ℝ) ∂timeLaw := ht _
        _ ≤ _ := by
          apply integral_mono (unit_valued_integrable _ hr.measurable)
            (unit_valued_integrable _ (sampleQuantileUpper_mono n hr).measurable)
          exact fun u => (sampleQuantile_bracket n hr u).2
    change (∫ u in Ici (uniformQuantileGrid n j.castSucc),
      (uniformQuantileLower n q (uniformQuantileCell n u):ℝ) ∂timeLaw) ≤
      ∫ u in Ici (uniformQuantileGrid n j.castSucc),
        (uniformQuantileUpper n r (uniformQuantileCell n u):ℝ) ∂timeLaw at h1
    rw [uniformQuantileCell_tail_integral n (fun i => (uniformQuantileLower n q i:ℝ)) j,
      uniformQuantileCell_tail_integral n (fun i => (uniformQuantileUpper n r i:ℝ)) j] at h1
    have he : (∑ i : Fin (n+1), if k ≤ i.val then
        (1/(n+1:ℝ))*((uniformQuantileUpper n r i:ℝ)-uniformQuantileLower n q i) else 0)=
      (∑ i : Fin (n+1), if j ≤ i then (1/(n+1:ℝ))*(uniformQuantileUpper n r i:ℝ) else 0)-
      (∑ i : Fin (n+1), if j ≤ i then (1/(n+1:ℝ))*(uniformQuantileLower n q i:ℝ) else 0) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      change (if k ≤ i.val then _ else _)=(if k ≤ i.val then _ else _)-(if k ≤ i.val then _ else _)
      split_ifs <;> ring
    rw [he]
    exact sub_nonneg.mpr h1
  · have hz : ∀ i : Fin (n+1), ¬k ≤ i.val := fun i => by have := i.isLt; omega
    simp only [hz,ite_false,Finset.sum_const_zero,le_refl]

lemma sampleQuantile_control_error (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (g : Jet3) (q : Time→Time) (hq : Monotone q) (n : ℕ) :
    |controlValue P g.f (quantileTrial (sampleQuantileLower n q))-controlValue P g.f (quantileTrial q)| ≤
      (3/2:ℝ)*(‖g.d1‖₊:ℝ)^2*(1/(n+1:ℝ)) ∧
    |controlValue P g.f (quantileTrial (sampleQuantileUpper n q))-controlValue P g.f (quantileTrial q)| ≤
      (3/2:ℝ)*(‖g.d1‖₊:ℝ)^2*(1/(n+1:ℝ)) := by
  constructor
  · exact (controlValue_quantile_abs_sub_le P g _ _ (sampleQuantileLower_mono n hq).measurable hq.measurable).trans
      (mul_le_mul_of_nonneg_left (sampleQuantileLower_L1 n hq) (by positivity))
  · exact (controlValue_quantile_abs_sub_le P g _ _ (sampleQuantileUpper_mono n hq).measurable hq.measurable).trans
      (mul_le_mul_of_nonneg_left (sampleQuantileUpper_L1 n hq) (by positivity))

theorem sourceQuantile_control_tail_order (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (hB : IsBrownianReal brownianEval P) (g : Jet3) (q r : Time→Time)
    (hq : Monotone q) (hr : Monotone r)
    (ht : ∀ t : Time, (∫ u in Ici t, (q u:ℝ) ∂timeLaw) ≤ ∫ u in Ici t, (r u:ℝ) ∂timeLaw) :
    controlValue P g.f (quantileTrial r) ≤ controlValue P g.f (quantileTrial q) := by
  have hi (n : ℕ) : controlValue P g.f (quantileTrial (sampleQuantileUpper n r)) ≤
      controlValue P g.f (quantileTrial (sampleQuantileLower n q)) := by
    unfold sampleQuantileUpper sampleQuantileLower
    rw [sampleQuantile_trial,sampleQuantile_trial]
    exact sourceWeightedTrial_control_tail_order n _ _ _ (uniformQuantileWeights_nonneg n)
      (uniformQuantileWeights_sum n) (uniformQuantileLower_mono n hq) (uniformQuantileUpper_mono n hr)
      (sampledQuantile_tail_order n hq hr ht) g P hB
  have hz : Tendsto (fun n : ℕ => (3/2:ℝ)*(‖g.d1‖₊:ℝ)^2*(1/(n+1:ℝ))) atTop (𝓝 0) := by
    simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ)).const_mul ((3/2:ℝ)*(‖g.d1‖₊:ℝ)^2)
  have hl : Tendsto (fun n => controlValue P g.f (quantileTrial (sampleQuantileLower n q))) atTop
      (𝓝 (controlValue P g.f (quantileTrial q))) := by
    rw [tendsto_iff_dist_tendsto_zero]
    apply squeeze_zero (fun _ => dist_nonneg) (fun n => ?_) hz
    simpa only [Real.dist_eq] using (sampleQuantile_control_error P g q hq n).1
  have hu : Tendsto (fun n => controlValue P g.f (quantileTrial (sampleQuantileUpper n r))) atTop
      (𝓝 (controlValue P g.f (quantileTrial r))) := by
    rw [tendsto_iff_dist_tendsto_zero]
    apply squeeze_zero (fun _ => dist_nonneg) (fun n => ?_) hz
    simpa only [Real.dist_eq] using (sampleQuantile_control_error P g r hr n).2
  exact le_of_tendsto_of_tendsto hu hl (Eventually.of_forall hi)

end SphericalPerceptronFreeEnergy
end

end OAI
