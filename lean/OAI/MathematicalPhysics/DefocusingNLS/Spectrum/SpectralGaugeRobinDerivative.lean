import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralGaugeRobin
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralPhysicalGaugePair
import Mathlib.Analysis.Calculus.Deriv.Mul

namespace OAI

/-! Parameter differentiation commutes with the fixed profile gauge. -/

namespace DefocusingNLS

noncomputable def spectralGaugeRobinSlope (q : ℂ) (M' : ℂ × ℂ →L[ℂ] ℂ × ℂ) :
    ℂ × ℂ →L[ℂ] ℂ × ℂ :=
  (spectralGaugeInverse q).comp (M'.comp (spectralGaugeColumns q))

theorem spectralGaugeRobin_hasDerivAt (q dq : ℂ)
    (M : ℂ → (ℂ × ℂ →L[ℂ] ℂ × ℂ)) (M' : ℂ × ℂ →L[ℂ] ℂ × ℂ) (z : ℂ)
    (hM : HasDerivAt M M' z) :
    HasDerivAt (fun t => spectralGaugeRobin q dq (M t)) (spectralGaugeRobinSlope q M') z := by
  have h := (hasDerivAt_const z (spectralGaugeInverse q)).clm_comp
    ((hM.clm_comp (hasDerivAt_const z (spectralGaugeColumns q))).sub_const (spectralGaugeColumns dq))
  simpa only [ContinuousLinearMap.comp_zero,ContinuousLinearMap.zero_comp,add_zero,zero_add,
    spectralGaugeRobin,spectralGaugeRobinSlope] using h

theorem spectralGaugeRobin_chain_condition (q dq : ℂ) (hq : q ≠ 0)
    (M M' : ℂ × ℂ →L[ℂ] ℂ × ℂ) (x₀ x₁ dx₁ : ℂ × ℂ)
    (h : dx₁ = spectralGaugeRobin q dq M x₁ + spectralGaugeRobinSlope q M' x₀) :
    spectralGaugeColumns q dx₁ + spectralGaugeColumns dq x₁ =
      M (spectralGaugeColumns q x₁) + M' (spectralGaugeColumns q x₀) := by
  rw [h,map_add]
  have hbase := (spectralGaugeRobin_condition q dq hq M x₁ (spectralGaugeRobin q dq M x₁)).mpr rfl
  have hslope : spectralGaugeColumns q (spectralGaugeRobinSlope q M' x₀) = M' (spectralGaugeColumns q x₀) :=
    spectralGaugeColumns_inverse q hq _
  rw [hslope]
  linear_combination hbase

theorem spectralPhysicalGaugePair_chain_robin (Q f g : ℝ → ℂ) (r : ℝ)
    (M M' : ℂ × ℂ →L[ℂ] ℂ × ℂ) (x₀ : ℂ × ℂ) (hq : Q r ≠ 0)
    (h : (deriv f r,deriv g r) = spectralGaugeRobin (Q r) (deriv Q r) M (f r,g r) +
      spectralGaugeRobinSlope (Q r) M' x₀) :
    spectralPhysicalDerivativeMap (spectralPhysicalGaugePair Q f g r) =
      M (spectralPhysicalValueMap (spectralPhysicalGaugePair Q f g r)) +
      M' (spectralGaugeColumns (Q r) x₀) := by
  rw [spectralPhysicalGaugePair_slope,spectralPhysicalGaugePair_value]
  exact spectralGaugeRobin_chain_condition _ _ hq M M' x₀ (f r,g r) (deriv f r,deriv g r) h

end DefocusingNLS

end OAI
