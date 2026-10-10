import OAI.Geometry.NodalSets.Charts.SphereNormalizedSimpleUniqueness

namespace OAI

namespace Yau.Target
open Manifold
open scoped ContDiff
noncomputable section

theorem sphere_positive_normalization (d : SphereEnergyData) (u : Base → ℝ)
    (hu : Continuous u) (hne : u ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ sphereWeightedPairing d.density (c • u) (c • u)=1 := by
  have hQ := sphereWeightedPairing_self_pos d.density u d.continuous d.positive hu hne
  let c := (Real.sqrt (sphereWeightedPairing d.density u u))⁻¹
  have hc : 0 < c := inv_pos.mpr (Real.sqrt_pos.mpr hQ)
  refine ⟨c,hc,?_⟩
  rw [sphereWeightedPairing_smul_self]
  dsimp [c]
  rw [inv_pow,Real.sq_sqrt hQ.le,inv_mul_cancel₀ hQ.ne']

end
end Yau.Target

end OAI
