import OAI.Geometry.Relativity.CKS.HeatBase

namespace OAI

noncomputable section
namespace CKSSphericalHarmonics
noncomputable section
open MeasureTheory Set

theorem sphereArea_eq_four_pi : sphereArea = 4 * Real.pi := by
  rw [sphereArea, sphereIntegral_apply]
  simp only [ContinuousMap.one_apply, integral_const, smul_eq_mul, mul_one]
  rw [Measure.toSphere_real_apply_univ]
  simp only [Ambient, finrank_euclideanSpace, Fintype.card_fin, Nat.cast_ofNat,
    measureReal_def, EuclideanSpace.volume_ball_fin_three, ENNReal.ofReal_one, one_pow, one_mul]
  rw [ENNReal.toReal_ofReal (by positivity)]
  ring

end
end CKSSphericalHarmonics

end

end OAI
