import OAI.Geometry.CylinderCovering.Rational.EnergyIntegral
import OAI.Geometry.CylinderCovering.Rational.CeilingIntegral

namespace OAI

open Filter
open scoped Topology

noncomputable section

namespace SlopeRational

theorem coefficientGap_tendsto :
    Tendsto (fun d => energyIntegral d-ceilingIntegral d)
      (𝓝[>] (0:ℝ)) (𝓝 (1/15360:ℝ)) := by
  have h := energyIntegral_tendsto.sub ceilingIntegral_tendsto_zero_right
  norm_num at h ⊢
  exact h

theorem coefficientGap_eventually_pos :
    ∀ᶠ d in 𝓝[>] (0:ℝ), ceilingIntegral d < energyIntegral d := by
  have h := coefficientGap_tendsto.eventually
    (Ioi_mem_nhds (by norm_num : (0:ℝ) < 1/15360))
  filter_upwards [h] with d hd
  exact sub_pos.mp hd

theorem exists_positive_coefficientGap :
    ∃ d : ℝ, 0 < d ∧ ceilingIntegral d < energyIntegral d := by
  have h : ∀ᶠ d in 𝓝[>] (0:ℝ), 0 < d ∧ ceilingIntegral d < energyIntegral d :=
    by
      filter_upwards [self_mem_nhdsWithin, coefficientGap_eventually_pos] with d hd hg
      exact ⟨hd,hg⟩
  exact h.exists

theorem exists_fixed_quadratic_padding :
    ∃ d η : ℝ, 0 < d ∧ 0 < η ∧ ceilingIntegral d + η/2 < energyIntegral d := by
  obtain ⟨d,hd,hgap⟩ := exists_positive_coefficientGap
  refine ⟨d, energyIntegral d-ceilingIntegral d, hd, sub_pos.mpr hgap, ?_⟩
  linarith

end SlopeRational

end

end OAI
