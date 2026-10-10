import OAI.Geometry.CylinderCovering.Rational.UncenteredField
import OAI.Geometry.CylinderCovering.Rational.CostDictionary
import OAI.Geometry.RuledCovering.Main

namespace OAI

noncomputable section
namespace RationalDictionary

theorem uncenteredFirstSweep_eq_physicalRuled (d0 eta0 k : ℝ) :
    uncenteredFirstSweep d0 eta0 k =
      RuledApproximation.physicalRuled 1 (uncenteredDomain d0 eta0 k)
        (fun p => k • velocity d0 p) (2 * c0) := by
  ext z
  constructor <;> rintro ⟨p, hp, r, hr, rfl⟩ <;>
    refine ⟨p, hp, r, hr, ?_⟩ <;>
    ext i <;> fin_cases i <;>
    simp [vec3, RuledApproximation.vec3, lineMap, velocity, vec2] <;> ring

theorem finite_first_logarithmic {d0 k : ℝ} (hd : 0 < d0)
    (hk : 0 < k) (hkd : k < d0 / (1 + d0)) (eta0 : ℝ)
    {e : ℝ} (he : 0 < e) :
    RuledApproximation.HasFiniteCover RuledApproximation.Cylinder.openBounded
      (uncenteredFirstSweep d0 eta0 k) (uncenteredCost d0 eta0 k + e) := by
  rw [uncenteredFirstSweep_eq_physicalRuled]
  have h := RuledApproximation.logarithmic (2 * c0) k
    (uncenteredDomain d0 eta0 k) (velocity d0)
    (mul_pos (by norm_num) c0_pos) hk (uncenteredDomain_isCompact d0 eta0 k)
    (volume_frontier_uncenteredDomain d0 eta0 k) (velocity_openRectangleC2 hd eta0 k)
    (fun p hp => velocity_logarithmic_spectrum hd hk hkd hp.1) e he
  simpa only [uncenteredCost, uncenteredWeight_eq_norm] using h

end RationalDictionary

end

end OAI
