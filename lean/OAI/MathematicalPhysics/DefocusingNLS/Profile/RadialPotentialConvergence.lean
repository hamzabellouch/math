import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialPotentialParameter
import Mathlib.Topology.MetricSpace.UniformConvergence

namespace OAI

/-! Joint uniform continuity of the actual potential along convergent inner amplitudes. -/

open Set Filter Topology
namespace DefocusingNLS

theorem radialAmplitudePotential_uniform_convergence (R : ℝ) (hR : R^2 ≤ 11)
    (c b : ℕ → ℝ) (c₀ b₀ : ℝ) (hc : ∀ n, c n ∈ Icc (599/100 : ℝ) 6)
    (hc₀ : c₀ ∈ Icc (599/100 : ℝ) 6)
    (hcT : Tendsto c atTop (𝓝 c₀)) (hbT : Tendsto b atTop (𝓝 b₀))
    (H : ℕ → ℝ → ℝ) (A : ℝ → ℝ) (hH : ∀ n, Continuous (H n)) (hA : Continuous A)
    (hHI : ∀ n r, r ∈ Icc 0 R → H n r ∈ Icc (999/1000 : ℝ) 1)
    (hAI : ∀ r ∈ Icc 0 R, A r ∈ Icc (999/1000 : ℝ) 1)
    (hT : TendstoUniformlyOn H A atTop (Icc 0 R)) :
    TendstoUniformlyOn (fun n => radialAmplitudePotential (c n) (b n) (H n))
      (radialAmplitudePotential c₀ b₀ A) atTop (Icc 0 R) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hδ : 0 < ε/12 := by positivity
  have hHt := (Metric.tendstoUniformlyOn_iff.mp hT) (ε/12) hδ
  have hct : ∀ᶠ n in atTop, |c n-c₀| < ε/12 := by
    have h := (Metric.tendsto_nhds.mp hcT) (ε/12) hδ
    simpa only [Real.dist_eq] using h
  have hbt : ∀ᶠ n in atTop, |b n-b₀| < ε/12 := by
    have h := (Metric.tendsto_nhds.mp hbT) (ε/12) hδ
    simpa only [Real.dist_eq] using h
  filter_upwards [hHt,hct,hbt] with n hn hcn hbn r hr
  have h1 := radialAmplitudePotential_difference (c n) (b n) R (ε/12) (hc n) hR hδ.le
    (H n) A (hH n) hA (hHI n) hAI (by
      intro t ht
      have h := hn t ht
      rw [Real.dist_eq,abs_sub_comm] at h
      exact h.le) r hr
  have h2 := radialAmplitudePotential_parameter_difference (c n) c₀ (b n) b₀ R
    (hc n) hc₀ hR A hA hAI r hr
  rw [Real.dist_eq,abs_sub_comm]
  have htriangle := abs_sub_le (radialAmplitudePotential (c n) (b n) (H n) r)
    (radialAmplitudePotential (c n) (b n) A r) (radialAmplitudePotential c₀ b₀ A r)
  linarith

end DefocusingNLS

end OAI
