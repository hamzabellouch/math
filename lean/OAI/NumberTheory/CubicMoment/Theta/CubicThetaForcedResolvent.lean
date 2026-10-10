import OAI.NumberTheory.CubicMoment.Theta.CubicThetaForcingL2
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaContinuedWeakEquation
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaGlobalAutomorphicRange
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaMeromorphicApply

namespace OAI

/-! The global resolvent applied to the literal incoming arithmetic
forcing. Identification with the Eisenstein remainder is a separate step. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaForcedResolvent (s : ℂ) : CubicThetaGlobalL2 :=
  cubicThetaGlobalSpectralResolvent s (cubicThetaForcingL2 s)

theorem cubicThetaForcedResolvent_meromorphic {s : ℂ} (hs : 1<s.re) :
    MeromorphicAt cubicThetaForcedResolvent s :=
  cubicThetaMeromorphic_apply (cubicThetaGlobalSpectralResolvent_meromorphic hs)
    (cubicThetaForcingL2_analytic s)

lemma cubicThetaForcedResolvent_automorphic {s : ℂ}
    (hu : IsUnit (cubicThetaEnergyPencil (cubicThetaGlobalSpectralParameter s))) :
    cubicThetaForcedResolvent s∈cubicThetaAutomorphicL2 := by
  rw [cubicThetaForcedResolvent,cubicThetaGlobalSpectralResolvent,
    ← cubicThetaContinuedEnergyLift_value hu]
  exact cubicThetaGlobalInclusion_mem _

theorem cubicThetaForcedResolvent_weak {s : ℂ}
    (hu : IsUnit (cubicThetaEnergyPencil (cubicThetaGlobalSpectralParameter s)))
    (v : cubicThetaGlobalEnergySpace) :
    inner ℂ (cubicThetaGlobalEnergyGradient v)
        (cubicThetaGlobalEnergyGradient (cubicThetaContinuedEnergyLift
          (cubicThetaGlobalSpectralParameter s) (cubicThetaForcingL2 s)))+
      (s*(s-2))*inner ℂ (cubicThetaGlobalInclusion v) (cubicThetaForcedResolvent s)=
      inner ℂ (cubicThetaGlobalInclusion v) (cubicThetaForcingL2 s) := by
  have h := cubicThetaContinuedEnergyLift_weak hu (cubicThetaForcingL2 s) v
  have he : 1-cubicThetaGlobalSpectralParameter s=s*(s-2) := by
    unfold cubicThetaGlobalSpectralParameter
    ring
  rw [he] at h
  exact h

end CubicFirstMoment

end

end OAI
