import OAI.Geometry.NodalSets.Charts.SphereSmoothGreenBound
import OAI.Geometry.NodalSets.Spectral.SphereWeakResolvent

namespace OAI

namespace Yau.Target
open MeasureTheory
noncomputable section
local instance sphereEnergyL2InjectiveMeasurable : MeasurableSpace Base := borel Base
local instance sphereEnergyL2InjectiveBorel : BorelSpace Base := ⟨rfl⟩

theorem sphere_completed_dirichlet_test_bound (d : SphereEnergyData) (v : SphereEnergySmooth d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : SphereEnergyHilbert d,
      |sphereCompletedDirichlet d z (sphereEnergyToCompletion d v)| ≤ C*‖sphereEnergyL2Map d z‖ := by
  obtain ⟨C,hC,hb⟩ := sphere_smooth_dirichlet_L2_bound d v
  refine ⟨C,hC,?_⟩
  intro z
  apply (sphereEnergyToCompletion_dense d).induction_on
    (p := fun z ↦ |sphereCompletedDirichlet d z (sphereEnergyToCompletion d v)| ≤ C*‖sphereEnergyL2Map d z‖) z
  · apply isClosed_le
    · exact ((continuous_id.inner continuous_const).sub
        ((sphereEnergyL2Map d).continuous.inner continuous_const)).abs
    · fun_prop
  · intro u
    rw [sphereCompletedDirichlet_coe,sphereEnergyL2Map_coe]
    exact hb u

theorem sphereEnergyL2Map_eq_zero_iff (d : SphereEnergyData) (z : SphereEnergyHilbert d) :
    sphereEnergyL2Map d z = 0 ↔ z = 0 := by
  constructor
  · intro hz
    apply (inner_self_eq_zero (𝕜 := ℝ)).mp
    apply (sphereEnergyToCompletion_dense d).induction_on (p := fun v ↦ inner ℝ z v = 0) z
    · exact isClosed_eq (by fun_prop) continuous_const
    · intro v
      obtain ⟨C,_,hC⟩ := sphere_completed_dirichlet_test_bound d v
      have h := hC z
      rw [hz,norm_zero,mul_zero] at h
      have hd := abs_eq_zero.mp (le_antisymm h (abs_nonneg _))
      simpa only [sphereCompletedDirichlet,hz,inner_zero_left,sub_zero] using hd
  · rintro rfl
    exact map_zero _

theorem sphereEnergyL2Map_injective (d : SphereEnergyData) : Function.Injective (sphereEnergyL2Map d) := by
  apply (LinearMap.ker_eq_bot).mp
  ext z
  exact sphereEnergyL2Map_eq_zero_iff d z

end
end Yau.Target

end OAI
