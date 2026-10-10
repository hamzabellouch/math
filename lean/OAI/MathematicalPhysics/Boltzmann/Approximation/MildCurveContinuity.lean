import OAI.MathematicalPhysics.Boltzmann.Jets.TorusTransport
import OAI.MathematicalPhysics.Boltzmann.Branching.TimeSourceCumulative

namespace OAI

/-! # A strongly continuous Eulerian representative of an integrable mild curve -/

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace BoltzmannNonuniqueness.TorusFlight

def characteristicProfile (μ : Measure ℝ) (a : Density) (R : ℝ × Phase → ℝ)
    (t : ℝ) (p : Phase) : ℝ := a p+Published.timePrimitive μ R (t,p)

def eulerianProfile (μ : Measure ℝ) (a : Density) (R : ℝ × Phase → ℝ)
    (t : ℝ) (p : Phase) : ℝ := characteristicProfile μ a R t (flight (-t) p)

theorem timePrimitive_slice_integrable {μ : Measure ℝ} [IsFiniteMeasure μ]
    {R : ℝ × Phase → ℝ} (hRm : Measurable R) (hRi : Integrable R (μ.prod volume)) (t : ℝ) :
    Integrable (fun p => Published.timePrimitive μ R (t,p)) := by
  apply hRi.integral_norm_prod_right.mono'
    (((Published.timePrimitive_measurable μ hRm).comp
      (measurable_const.prodMk measurable_id)).aestronglyMeasurable)
  filter_upwards [hRi.prod_left_ae] with p hp
  apply norm_integral_le_of_norm_le hp.norm
  filter_upwards [] with s
  change ‖if s ≤ t then R (s,p) else 0‖ ≤ ‖R (s,p)‖
  split <;> simp

theorem characteristicProfile_integrable {μ : Measure ℝ} [IsFiniteMeasure μ]
    {a : Density} (hai : Integrable a) {R : ℝ × Phase → ℝ}
    (hRm : Measurable R) (hRi : Integrable R (μ.prod volume)) (t : ℝ) :
    Integrable (characteristicProfile μ a R t) :=
  hai.add (timePrimitive_slice_integrable hRm hRi t)

theorem eulerianProfile_L1_continuous {T : ℝ} (hT : 0 ≤ T)
    {a : Density} (hai : Integrable a) {R : ℝ × Phase → ℝ}
    (hRm : Measurable R) (hRi : Integrable R ((volume.restrict (Icc 0 T)).prod volume))
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    Tendsto (fun s => eLpNorm (fun p =>
      eulerianProfile (volume.restrict (Icc 0 T)) a R s p-
        eulerianProfile (volume.restrict (Icc 0 T)) a R t p) 1 volume)
      (𝓝[Icc 0 T] t) (𝓝 0) := by
  let μ : Measure ℝ := volume.restrict (Icc 0 T)
  let C := characteristicProfile μ a R
  have hCt := characteristicProfile_integrable hai hRm hRi t
  have hprim := Published.timePrimitive_L1_continuous hT hRm hRi ht
  have hneg : Tendsto (fun s : ℝ => -s) (𝓝[Icc 0 T] t) (𝓝 (-t)) :=
    continuous_neg.continuousAt.tendsto.mono_left inf_le_left
  have hfixed := (tendsto_flight_L1 hCt (-t)).comp hneg
  have hi (s : ℝ) : eLpNorm (fun p => C s (flight (-s) p)-C t (flight (-s) p)) 1 volume =
      eLpNorm (fun p => Published.timePrimitive μ R (s,p)-Published.timePrimitive μ R (t,p)) 1 volume := by
    have he : (fun p => C s p-C t p) =
        (fun p => Published.timePrimitive μ R (s,p)-Published.timePrimitive μ R (t,p)) := by
      funext p
      dsimp [C,characteristicProfile]
      ring
    have hms : Measurable (fun p : Phase => Published.timePrimitive μ R (s,p)) :=
      (Published.timePrimitive_measurable μ hRm).comp (measurable_const.prodMk measurable_id)
    have hmt : Measurable (fun p : Phase => Published.timePrimitive μ R (t,p)) :=
      (Published.timePrimitive_measurable μ hRm).comp (measurable_const.prodMk measurable_id)
    have hm : Measurable (fun p => C s p-C t p) := by
      rw [he]
      exact hms.sub hmt
    exact (eLpNorm_comp_measurePreserving hm.aestronglyMeasurable
      (flight_measurePreserving (-s)) (p := 1)).trans
        (congrArg (fun h => eLpNorm h 1 (volume : Measure Phase)) he)
  have hupper := hprim.add hfixed
  simp only [add_zero] at hupper
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
    (fun _ => zero_le) (fun s => ?_)
  have he : (fun p => eulerianProfile μ a R s p-eulerianProfile μ a R t p) =
      (fun p => C s (flight (-s) p)-C t (flight (-s) p))+
        (fun p => C t (flight (-s) p)-C t (flight (-t) p)) := by
    funext p
    dsimp [eulerianProfile,C]
    ring
  rw [he]
  exact (eLpNorm_add_le (by norm_num : (1 : ℝ≥0∞) ≤ 1)).trans_eq (by rw [hi]; rfl)

end BoltzmannNonuniqueness.TorusFlight

end

end OAI
