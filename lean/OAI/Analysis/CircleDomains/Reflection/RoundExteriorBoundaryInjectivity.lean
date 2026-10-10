import OAI.Analysis.CircleDomains.Reflection.RoundExteriorBoundaryChart

namespace OAI

/-! The explicit circular exterior chart is injective on its actual
small neighborhood, before any boundary continuation is performed. -/
open Set Function Metric Complex
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma unitExteriorBoundaryChart_injOn {p : ℂ} (hp : p≠0) :
    InjOn (unitExteriorBoundaryChart p) (ball 0 1) := by
  intro z hz w hw he
  have hz1 : ‖z‖<1 := mem_ball_zero_iff.mp hz
  have hw1 : ‖w‖<1 := mem_ball_zero_iff.mp hw
  change -p/halfPlaneDisk z = -p/halfPlaneDisk w at he
  have hcross := (div_eq_div_iff (cayley_ne_zero_of_norm_lt_one hz1)
    (cayley_ne_zero_of_norm_lt_one hw1)).mp he
  have heq := mul_left_cancel₀ (neg_ne_zero.mpr hp) hcross
  exact halfPlaneDisk_injOn_nonpole (cayley_den_ne_zero_of_norm_lt_one hz1)
    (cayley_den_ne_zero_of_norm_lt_one hw1) heq.symm

lemma roundExteriorBoundaryChart_injOn (c : ℂ) {r : ℝ} {p : ℂ}
    (hr : 0<r) (hp : p≠0) : InjOn (roundExteriorBoundaryChart c r p) (ball 0 1) := by
  intro z hz w hw he
  change c+(r:ℂ)*unitExteriorBoundaryChart p z=c+(r:ℂ)*unitExteriorBoundaryChart p w at he
  have hrc : (r:ℂ)≠0 := by exact_mod_cast hr.ne'
  exact unitExteriorBoundaryChart_injOn hp hz hw (mul_left_cancel₀ hrc (add_left_cancel he))

end CircleDomainRigidity

end

end OAI
