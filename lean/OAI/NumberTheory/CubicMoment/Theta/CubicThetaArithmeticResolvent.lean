import OAI.NumberTheory.CubicMoment.Theta.CubicThetaArithmeticGlobalWeak
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaWeakUniqueness

namespace OAI

/-! The continued global resolvent is the literal arithmetic Eisenstein
remainder on its initial half-plane of absolute convergence. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaArithmeticEnergy_eq_continued {s : ℂ} (hs : 3<s.re) :
    cubicThetaArithmeticEnergy s hs=cubicThetaContinuedEnergyLift
      (cubicThetaGlobalSpectralParameter s) (cubicThetaForcingL2 s) := by
  apply cubicThetaContinuedEnergyLift_unique
    (cubicThetaEnergyPencil_unit (cubicThetaGlobalSpectralParameter_regular
      (by linarith) (Or.inr (by linarith))))
  intro v
  have h := cubicThetaArithmetic_global_weak hs v
  have he : 1-cubicThetaGlobalSpectralParameter s=s*(s-2) := by
    unfold cubicThetaGlobalSpectralParameter
    ring
  rwa [he]

theorem cubicThetaArithmeticL2_eq_forcedResolvent {s : ℂ} (hs : 3<s.re) :
    cubicThetaArithmeticL2 s hs=cubicThetaForcedResolvent s := by
  have hu := cubicThetaEnergyPencil_unit (cubicThetaGlobalSpectralParameter_regular
    (show 1<s.re by linarith) (Or.inr (by linarith)))
  calc
    _ = cubicThetaGlobalInclusion (cubicThetaArithmeticEnergy s hs) := rfl
    _ = cubicThetaGlobalInclusion (cubicThetaContinuedEnergyLift
        (cubicThetaGlobalSpectralParameter s) (cubicThetaForcingL2 s)) :=
      congrArg cubicThetaGlobalInclusion (cubicThetaArithmeticEnergy_eq_continued hs)
    _ = cubicThetaForcedResolvent s := cubicThetaContinuedEnergyLift_value hu _

end CubicFirstMoment

end

end OAI
