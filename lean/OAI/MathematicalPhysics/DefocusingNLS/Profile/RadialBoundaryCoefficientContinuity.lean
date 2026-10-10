import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialFreePhysicalNormalization
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialFreeParameterContinuity
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialFreeShootingData

namespace OAI

/-! Continuous physical normalization of the outgoing H solution. -/

namespace DefocusingNLS

theorem continuous_radialFreePhysical_unitCoefficient :
    Continuous (fun w : RadialShootingDisk =>
      radialFreePhysicalBoundaryCoefficient (radialShootingB w) 1) := by
  have hq : Continuous (fun w : RadialShootingDisk => -Complex.I*(radialShootingB w : ℂ)) := by
    unfold radialShootingB
    fun_prop
  have hH : Continuous (fun w : RadialShootingDisk =>
      normalizedSlowSolution (-Complex.I*(radialShootingB w : ℂ)) 6
        (radialFreeSlowArgument (Real.log innerBoundaryRadius))) := by
    apply continuous_iff_continuousAt.mpr
    intro w
    exact (continuousAt_normalizedSlowSolution_parameter _ 6 _ (by simp)
      (by rw [radialFreeSlowArgument_re]) (radialFreeSlowArgument_ne_zero _)).comp
        (f := fun w : RadialShootingDisk => -Complex.I*(radialShootingB w : ℂ))
        (x := w) hq.continuousAt
  have hn (w : RadialShootingDisk) :
      normalizedSlowSolution (-Complex.I*(radialShootingB w : ℂ)) 6
        (radialFreeSlowArgument (Real.log innerBoundaryRadius)) ≠ 0 := by
    intro he
    have hh := (radialFreePhysicalBoundaryCoefficient_spec w 1 (by norm_num)).2.1
    change Complex.exp _*radialFreeSlowValue (-Complex.I*(radialShootingB w : ℂ))
      (radialFreePhysicalBoundaryCoefficient (radialShootingB w) 1) _=(1 : ℂ) at hh
    simp only [radialFreeSlowValue,he,mul_zero] at hh
    exact zero_ne_one hh
  unfold radialFreePhysicalBoundaryCoefficient radialFreeBoundaryCoefficient
  exact (show Continuous (fun w : RadialShootingDisk =>
      Complex.exp (-(2*Complex.I*(radialShootingB w : ℂ)*(Real.log innerBoundaryRadius : ℂ)))) by
        unfold radialShootingB
        fun_prop).mul (continuous_const.div hH hn)

end DefocusingNLS

end OAI
