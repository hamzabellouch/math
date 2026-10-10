import OAI.NumberTheory.CubicMoment.Theta.CubicThetaAveragedVoronoi

namespace OAI

/-! Exact frequency bookkeeping for the constructed transform. The common
cusp numerator `n` represents `n/lambda^4`; the published dual argument
represents `n/lambda`. The conversion is recorded without changing either
normalization or identifying the two transform arguments. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaFrequency_to_metaplectic (n : MetaplecticDualArgument) :
    traceLambda^3*cubicThetaFrequency n.val=metaplecticFrequency n := by
  unfold cubicThetaFrequency metaplecticFrequency
  field_simp [traceLambda_ne_zero]

lemma cubicTheta_metaplectic_normSq (n : MetaplecticDualArgument) :
    Complex.normSq (metaplecticFrequency n)=norm n.val/3 := by
  rw [metaplecticFrequency,Complex.normSq_div,traceLambda_normSq]
  rfl

lemma cubicThetaLevelScale_fourth {r : Eisenstein} (_hr : primary r) :
    cubicThetaLevelScale r^4=(norm r^2)⁻¹ := by
  have hs := Real.sq_sqrt (norm_nonneg r)
  unfold cubicThetaLevelScale
  rw [inv_pow]
  congr 1
  nlinarith [sq_nonneg (Real.sqrt (norm r))]

lemma cubicThetaVoronoi_dual_argument {r : Eisenstein} (hr : primary r)
    (n : MetaplecticDualArgument) (X : ℝ) :
    cubicThetaDualScale r (X/27)*‖cubicThetaFrequency n.val‖^2=
      (2*Real.pi)^4*Complex.normSq (metaplecticFrequency n)*X/(729*norm r^2) := by
  rw [cubicThetaDualScale,cubicThetaLevelScale_fourth hr,cubicThetaFrequency_sq,
    cubicTheta_metaplectic_normSq]
  ring

lemma cubicThetaVoronoi_dual_argument_ne_printed {r : Eisenstein} (hr : primary r)
    (n : MetaplecticDualArgument) {X : ℝ} (hX : 0<X) :
    cubicThetaDualScale r (X/27)*‖cubicThetaFrequency n.val‖^2 ≠
      (2*Real.pi)^4*Complex.normSq (metaplecticFrequency n)*X/norm r^2 := by
  rw [cubicThetaVoronoi_dual_argument hr]
  have hpos : 0<(2*Real.pi)^4*Complex.normSq (metaplecticFrequency n)*X/norm r^2 := by
    apply div_pos
    · exact mul_pos (mul_pos (pow_pos (by positivity) _)
        (Complex.normSq_pos.mpr (metaplecticFrequency_ne_zero n))) hX
    · exact sq_pos_of_pos (norm_pos_of_ne_zero (primary_ne_zero hr))
  have he : (2*Real.pi)^4*Complex.normSq (metaplecticFrequency n)*X/(729*norm r^2)=
      ((2*Real.pi)^4*Complex.normSq (metaplecticFrequency n)*X/norm r^2)/729 := by ring
  rw [he]
  linarith

end CubicFirstMoment

end

end OAI
