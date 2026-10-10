import OAI.MathematicalPhysics.Boltzmann.Branching.TimeSourceCumulative
import OAI.MathematicalPhysics.Boltzmann.Compactness.WeakTimeLocalization

namespace OAI

/-! # Integrable derivatives give every-time strong L1 traces -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace BoltzmannNonuniqueness.Published
variable {X : Type*} [MeasurableSpace X] {ν : Measure X} [SFinite ν]

theorem integrable_path_trace {T : ℝ} (hT : 0 ≤ T)
    {a : X → ℝ} {u : ℝ → X → ℝ} {r : ℝ × X → ℝ}
    (hai : Integrable a ν) (hri : Integrable r ((volume.restrict (Icc 0 T)).prod ν))
    (hu : ∀ᵐ p ∂ν, ∀ t ∈ Icc 0 T, u t p = a p+∫ s in 0..t, r (s,p)) :
    (∀ t ∈ Icc 0 T, Integrable (u t) ν) ∧
    ∀ t ∈ Icc 0 T, Tendsto (fun s => eLpNorm (fun p => u s p-u t p) 1 ν)
      (𝓝[Icc 0 T] t) (𝓝 0) := by
  let μ := volume.restrict (Icc 0 T)
  let r' := hri.aestronglyMeasurable.mk r
  have hrm : Measurable r' := hri.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have hr'i : Integrable r' (μ.prod ν) := hri.congr hri.aestronglyMeasurable.ae_eq_mk
  have hreq : ∀ᵐ p ∂ν, ∀ᵐ s ∂μ, r (s,p) = r' (s,p) :=
    Measure.ae_ae_of_ae_prod (Measure.measurePreserving_swap.quasiMeasurePreserving.ae
      hri.aestronglyMeasurable.ae_eq_mk)
  let v (t : ℝ) (p : X) := a p+timePrimitive μ r' (t,p)
  have he t (ht : t ∈ Icc 0 T) : u t =ᵐ[ν] v t := by
    filter_upwards [hu,hreq] with p hp hrp
    rw [hp t ht,← timePrimitive_eq_interval ht r p]
    congr 1
    apply integral_congr_ae
    filter_upwards [hrp] with s hs
    change (if s ≤ t then r (s,p) else 0) = (if s ≤ t then r' (s,p) else 0)
    rw [hs]
  have hvi t : Integrable (v t) ν := hai.add (timePrimitive_slice_integrable hrm hr'i t)
  refine ⟨fun t ht => (hvi t).congr (he t ht).symm,?_⟩
  intro t ht
  have hp := timePrimitive_L1_continuous hT hrm hr'i ht
  have hv : Tendsto (fun s => eLpNorm (fun p => v s p-v t p) 1 ν)
      (𝓝[Icc 0 T] t) (𝓝 0) := by
    have heq s : (fun p => v s p-v t p) =
        (fun p => timePrimitive μ r' (s,p)-timePrimitive μ r' (t,p)) := by
      funext p
      dsimp only [v]
      ring
    simpa only [heq] using hp
  apply hv.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  exact (eLpNorm_congr_ae ((he s hs).sub (he t ht))).symm

end BoltzmannNonuniqueness.Published

end

end OAI
