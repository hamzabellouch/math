import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialPotentialParameter
import Mathlib.Topology.MetricSpace.UniformConvergence

namespace OAI

/-! Uniform convergence of the nonsingular velocity ratio along the actual amplitudes. -/

open Set Filter Topology
namespace DefocusingNLS

theorem radialVelocityRatio_uniform_convergence (R : ℝ)
    (c : ℕ → ℝ) (c₀ : ℝ) (hc : ∀ n, c n ∈ Icc (599/100 : ℝ) 6)
    (hcT : Tendsto c atTop (𝓝 c₀))
    (H : ℕ → ℝ → ℝ) (A : ℝ → ℝ) (hH : ∀ n, Continuous (H n)) (hA : Continuous A)
    (hHI : ∀ n r, r ∈ Icc 0 R → H n r ∈ Icc (999/1000 : ℝ) 1)
    (hAI : ∀ r ∈ Icc 0 R, A r ∈ Icc (999/1000 : ℝ) 1)
    (hT : TendstoUniformlyOn H A atTop (Icc 0 R)) :
    TendstoUniformlyOn (fun n => radialVelocityRatio (c n) (H n))
      (radialVelocityRatio c₀ A) atTop (Icc 0 R) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hδ : 0 < ε/12 := by positivity
  have hHt := (Metric.tendstoUniformlyOn_iff.mp hT) (ε/12) hδ
  have hct : ∀ᶠ n in atTop, |c n-c₀| < ε/12 := by
    have h := (Metric.tendsto_nhds.mp hcT) (ε/12) hδ
    simpa only [Real.dist_eq] using h
  filter_upwards [hHt,hct] with n hn hcn r hr
  have h1 := radialVelocityRatio_difference (c n) R (ε/12) (hc n) hδ.le
    (H n) A (hH n) hA (hHI n) hAI (by
      intro t ht
      have h := hn t ht
      rw [Real.dist_eq,abs_sub_comm] at h
      exact h.le) r hr
  have h2 := radialVelocityRatio_parameter_difference (c n) c₀ R A hA hAI r hr
  rw [Real.dist_eq,abs_sub_comm]
  have htriangle := abs_sub_le (radialVelocityRatio (c n) (H n) r)
    (radialVelocityRatio (c n) A r) (radialVelocityRatio c₀ A r)
  linarith

end DefocusingNLS

end OAI
