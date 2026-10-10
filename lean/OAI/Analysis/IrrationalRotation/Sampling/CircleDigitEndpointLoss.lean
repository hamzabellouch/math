import OAI.Analysis.IrrationalRotation.Rotation.CircleQuantizedMarginals
import OAI.Analysis.IrrationalRotation.Analysis.EndpointLoss
import OAI.Analysis.IrrationalRotation.Sampling.CircleDigitMarginalLaws

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology

namespace Invariant233.CircleCoupling

variable {θ : ℝ} {p : CircleParameterData}
  {hr : ∀ i, 0 < MixedRadix.radices p.q i}

namespace DigitMarginalLaws

lemma sqrt_integral_sq_le (hM : DigitMarginalLaws p hr)
    {H : Circle → ℝ} (hH : MemLp H 2 volume)
    (hbound : eLpNorm H 2 volume ≤ ENNReal.ofReal marginalBound) :
    Real.sqrt (∫ x, H x ^ 2) ≤ marginalBound := by
  rw [EndpointLoss.sqrt_integral_sq_eq_toReal_eLpNorm hH]
  have ht := ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound
  simpa only [ENNReal.toReal_ofReal hM.1.le] using ht

lemma hybrid_preimage_measureReal_le (hM : DigitMarginalLaws p hr)
    (hp : CircleParameterLaws θ p)
    (j : ℕ) (ε : ℕ → Bool) {s : Set Circle} (hs : MeasurableSet s) :
    (law p j).real (hybridPoint p hr ε ⁻¹' s) ≤
      marginalBound * Real.sqrt (volume.real s) := by
  obtain ⟨H, hH, hnonneg, _hmean, hbound, hlaw⟩ := hM.2 j ε
  have hmass := EndpointLoss.withDensity_measureReal_le_sqrt
    (volume : Measure Circle) hH hnonneg hs
  rw [← hlaw, map_measureReal_apply (measurable_hybridPoint hp hr ε) hs] at hmass
  exact hmass.trans (mul_le_mul_of_nonneg_right
    (hM.sqrt_integral_sq_le hH hbound) (Real.sqrt_nonneg _))

theorem tendsto_hybrid_sublevel_zero (hM : DigitMarginalLaws p hr)
    (hp : CircleParameterLaws θ p)
    (ε : ℕ → ℕ → Bool) {r : Circle → ℝ}
    (hrmeas : Measurable r) (hrpos : ∀ᵐ x ∂volume, 0 < r x) :
    Tendsto (fun j : ℕ => (law p j).real
      {ω | r (hybridPoint p hr (ε j) ω) < 1 / (j : ℝ)})
      atTop (𝓝 0) := by
  have hbase := EndpointLoss.tendsto_measureReal_one_div_sublevel_zero
    (volume : Measure Circle) hrmeas hrpos
  apply squeeze_zero (fun _ => measureReal_nonneg)
    (fun j => hM.hybrid_preimage_measureReal_le hp j (ε j)
      (measurableSet_lt hrmeas measurable_const))
  simpa only [Function.comp_apply, Real.sqrt_zero, mul_zero] using
    tendsto_const_nhds.mul (Real.continuous_sqrt.continuousAt.tendsto.comp hbase)

theorem tendsto_endpoint_bad_union_zero (hM : DigitMarginalLaws p hr)
    (hp : CircleParameterLaws θ p)
    {r : Circle → ℝ} (hrmeas : Measurable r)
    (hrinterior : ∀ᵐ x ∂volume, 0 < r x ∧ r x < 1) :
    Tendsto (fun j : ℕ => (law p j).real
      ({ω | r (point p hr false ω) < 1 / (j : ℝ)} ∪
       {ω | 1 - r (point p hr true ω) < 1 / (j : ℝ)}))
      atTop (𝓝 0) := by
  have hleft := hM.tendsto_hybrid_sublevel_zero hp (fun _ _ => false)
    hrmeas (hrinterior.mono fun _ hx => hx.1)
  have hright := hM.tendsto_hybrid_sublevel_zero hp (fun _ _ => true)
    (measurable_const.sub hrmeas)
    (hrinterior.mono fun _ hx => sub_pos.mpr hx.2)
  apply squeeze_zero (fun _ => measureReal_nonneg)
    (fun _ => measureReal_union_le _ _)
  simpa only [hybridPoint_const, Pi.sub_apply, zero_add] using hleft.add hright

end DigitMarginalLaws

theorem tendsto_endpoint_bad_union_zero_of_parameterLaws
    (hp : CircleParameterLaws θ p)
    (hr : ∀ i, 0 < MixedRadix.radices p.q i)
    {r : Circle → ℝ} (hrmeas : Measurable r)
    (hrinterior : ∀ᵐ x ∂volume, 0 < r x ∧ r x < 1) :
    Tendsto (fun j : ℕ => (law p j).real
      ({ω | r (point p hr false ω) < 1 / (j : ℝ)} ∪
       {ω | 1 - r (point p hr true ω) < 1 / (j : ℝ)}))
      atTop (𝓝 0) :=
  (digitMarginalLaws hp hr).tendsto_endpoint_bad_union_zero hp hrmeas hrinterior

end Invariant233.CircleCoupling

end

end OAI
