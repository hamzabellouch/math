import Mathlib
import OAI.Geometry.WeakHessian.Calculus.IntegralHopfInitial
import OAI.Geometry.WeakHessian.LocalBounds.HopfEnergyInitial

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile90
noncomputable section
namespace WeakHessianTransport
open WeakHessian Set Filter MeasureTheory
open scoped Topology ENNReal NNReal BoundedContinuousFunction

variable {X : Type*} [MetricSpace X] [ProperSpace X] [MeasurableSpace X] [BorelSpace X]
variable {m ν : Measure X} [IsFiniteMeasure ν]

lemma energy_le_of_hopf_integral_comparison
    (f F : X →ᵇ ℝ) {L M : ℝ≥0} (hf : LipschitzWith L f) (hF : LipschitzWith M F)
    {v : X → ℝ} (hv : Integrable v m) (hvn : ∀ᵐ x ∂m,0 ≤ v x)
    {C : ℝ} (hC : 0 < C)
    (hcomm : ∀ s : ℝ,0 < s →
      (∫ x,F x-boundedHopfMap F (s*C) x ∂ν) ≤ ∫ x,v x*(f x-boundedHopfMap f s x) ∂m) :
    cheegerEnergy ν F ≤ ENNReal.ofReal ((∫ x,v x*(localSlope f x).toReal^2 ∂m)/(2*C)) := by
  have hfin : cheegerEnergy ν F < ∞ :=
    (cheegerEnergy_le_integral_localSlope ν hF ((F.memLp_top (μ := ν)).mono_exponent le_top)).trans_lt ENNReal.ofReal_lt_top
  let E := (cheegerEnergy ν F).toReal
  let R := (∫ x,v x*(localSlope f x).toReal^2 ∂m)/2
  have hRn : 0 ≤ R := div_nonneg (integral_nonneg_of_ae (hvn.mono fun x hx => mul_nonneg hx (sq_nonneg _))) (by norm_num)
  have hEC : E ≤ R/C := by
    apply le_of_forall_lt_imp_le_of_dense
    intro a ha
    by_cases han : a ≤ 0
    · exact han.trans (div_nonneg hRn hC.le)
    have hap := lt_of_not_ge han
    have hea : ENNReal.ofReal a < cheegerEnergy ν F :=
      (ENNReal.ofReal_lt_iff_lt_toReal hap.le hfin.ne).mpr ha
    have hlow := integral_hopf_initial_energy_lower (m := ν) F hF hap.le hea
    have hid : Tendsto (fun s : ℝ => s) (𝓝[>] 0) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
    have hscale : Tendsto (fun s : ℝ => s*C) (𝓝[>] 0) (𝓝[>] 0) := by
      apply tendsto_nhdsWithin_iff.mpr
      refine ⟨by simpa using hid.mul_const C,?_⟩
      filter_upwards [self_mem_nhdsWithin] with s hs
      exact mul_pos hs hC
    have haC : a*C ≤ R := by
      apply le_of_forall_gt_imp_ge_of_dense
      intro b hb
      have hupp := integral_hopf_initial_eventually_lt f hf hv hvn hb
      obtain ⟨s,hs,hl,hu⟩ := ((show ∀ᶠ s : ℝ in 𝓝[>] 0,0 < s from self_mem_nhdsWithin).and (Filter.Eventually.and (hscale hlow) hupp)).exists
      have HH := div_le_div_of_nonneg_right (hcomm s hs) hs.le
      have he : a*C ≤ (∫ x,F x-boundedHopfMap F (s*C) x ∂ν)/s := by
        apply (le_div_iff₀ hs).mpr
        have H := (le_div_iff₀ (mul_pos hs hC)).mp hl
        nlinarith
      exact he.trans (HH.trans hu.le)
    exact (le_div_iff₀ hC).mpr haC
  rw [← ENNReal.ofReal_toReal hfin.ne]
  apply ENNReal.ofReal_le_ofReal
  convert hEC using 1
  dsimp only [E,R]
  ring
end WeakHessianTransport

end
end InlinedFile90

end OAI
