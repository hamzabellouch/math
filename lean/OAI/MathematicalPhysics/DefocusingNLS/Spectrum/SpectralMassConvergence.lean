import Mathlib.Topology.UniformSpace.UniformConvergenceTopology
import Mathlib.Analysis.Complex.Basic

namespace OAI

/-! Uniform convergence of a profile gives uniform convergence of its mass weight. -/

open Set Filter Topology
namespace DefocusingNLS

theorem spectralMass_uniform (R : ℝ) (Q : ℕ → ℝ → ℂ) (Q₀ : ℝ → ℂ)
    (hQ₀ : ContinuousOn Q₀ (Icc 0 R))
    (hQ : TendstoUniformlyOn Q Q₀ atTop (Icc 0 R)) :
    TendstoUniformlyOn (fun n r => ‖Q n r‖^2) (fun r => ‖Q₀ r‖^2)
      atTop (Icc 0 R) := by
  have hn := uniformContinuous_norm.comp_tendstoUniformlyOn hQ
  have hc := hQ₀.norm
  have hp := (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact isCompact_Icc).mp
    (hn.tendstoLocallyUniformlyOn.mul₀ hn.tendstoLocallyUniformlyOn hc hc)
  convert hp using 1 <;> ext <;> simp [pow_two]

end DefocusingNLS

end OAI
