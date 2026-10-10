import Mathlib
import OAI.Geometry.WeakHessian.LocalBounds.HopfEnergyLower

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile88
noncomputable section
namespace WeakHessianTransport
open WeakHessian Set Filter MeasureTheory
open scoped Topology ENNReal NNReal BoundedContinuousFunction

variable {X : Type*} [MetricSpace X] [ProperSpace X] [MeasurableSpace X] [BorelSpace X]
variable {m : Measure X} [IsFiniteMeasure m]

lemma integral_hopf_initial_energy_lower (f : X →ᵇ ℝ) {L : ℝ≥0} (hf : LipschitzWith L f)
    {a : ℝ} (ha : 0 ≤ a) (hE : ENNReal.ofReal a < cheegerEnergy m f) :
    ∀ᶠ s in 𝓝[>] (0:ℝ),a ≤ (∫ x,f x-boundedHopfMap f s x ∂m)/s := by
  have hc := continuousOn_boundedHopfLp (m := m) hf 0 (by simp)
  have hzero : cheegerEnergy m (boundedHopfLp m f 0 : X → ℝ) = cheegerEnergy m f := by
    apply cheegerEnergy_congr_ae
    simpa only [boundedHopfLp,boundedHopfMap_zero] using BoundedContinuousFunction.coeFn_toLp 2 m ℝ f
  have he := hc ((lowerSemicontinuous_cheegerEnergy (m := m) (boundedHopfLp m f 0))
    (ENNReal.ofReal a) (by dsimp; rwa [hzero]))
  obtain ⟨ε,hε,hεe⟩ := Metric.mem_nhdsWithin_iff.mp he
  filter_upwards [self_mem_nhdsWithin,
    ((tendsto_id.mono_left nhdsWithin_le_nhds : Tendsto (fun s : ℝ => s) (𝓝[>] 0) (𝓝 0)).eventually_lt_const hε)] with s hs hsε
  have hbound := integral_hopf_falling (m := m) f hf hs (a := a) (fun t ht hts => by
    have H : ENNReal.ofReal a < cheegerEnergy m (boundedHopfLp m f t : X → ℝ) :=
      hεe ⟨by simpa only [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_pos ht] using hts.trans hsε,ht.le⟩
    have hb := boundedHopfLp_energy_bound (m := m) f ht
    have H' : a < (cheegerEnergy m (boundedHopfLp m f t : X → ℝ)).toReal := by
      exact (ENNReal.ofReal_lt_iff_lt_toReal ha hb.1.ne).mp H
    have hb' := H'.le.trans hb.2
    have hfun : (boundedHopfMap f t : X → ℝ) = hopfLax f t := funext (boundedHopfMap_apply_pos f ht)
    simpa only [hfun] using hb')
  rw [integral_sub (f.integrable (μ := m)) ((boundedHopfMap f s).integrable (μ := m))]
  exact (le_div_iff₀ hs).mpr (by linarith)
end WeakHessianTransport

end
end InlinedFile88

end OAI
