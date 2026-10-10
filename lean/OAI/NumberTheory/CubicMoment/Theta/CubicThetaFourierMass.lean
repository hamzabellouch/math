import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPositiveFourierSmooth
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaFourierProfileGram
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeMassOperator

namespace OAI

/-! Smooth compact Fourier sources in the genuine automorphic mass
closure, and the adjoint link to the completed energy space. -/
noncomputable section
open scoped ContDiff CompactlySupported
namespace CubicFirstMoment

def cubicThetaHighFourierMass (h : Eisenstein) (W : C_c(ℝ,ℂ))
    (hW : ∀ v≤(2:ℝ),W v=0) (hsm : ContDiff ℝ ∞ (W : ℝ → ℂ)) : cubicThetaAutomorphicL2 :=
  cubicThetaGlobalMassClosure (cubicThetaPositiveFourierProfileTest h W (by norm_num) hW hsm)

lemma cubicThetaHighFourierMass_val (h : Eisenstein) (W : C_c(ℝ,ℂ))
    (hW : ∀ v≤(2:ℝ),W v=0) (hsm : ContDiff ℝ ∞ (W : ℝ → ℂ)) :
    (cubicThetaHighFourierMass h W hW hsm).val=cubicThetaFourierProfileL2 h W hW := rfl

lemma cubicThetaHighFourierMass_pairing (h : Eisenstein) (W : C_c(ℝ,ℂ))
    (hW : ∀ v≤(2:ℝ),W v=0) (hsm : ContDiff ℝ ∞ (W : ℝ → ℂ))
    (u : cubicThetaGlobalEnergySpace) :
    inner ℂ (cubicThetaHighFourierMass h W hW hsm) (cubicThetaGlobalEnergyValueMap u)=
      inner ℂ (cubicThetaCuspFourierTest h W) (cubicThetaCuspRestriction u) := by
  change inner ℂ (cubicThetaFourierProfileL2 h W hW) (cubicThetaGlobalInclusion u)=_
  exact cubicThetaFourierProfilePairing_energy h W hW u

lemma cubicThetaHighFourierMass_orthogonal {h k : Eisenstein} (hhk : h≠k)
    (W V : C_c(ℝ,ℂ)) (hW : ∀ v≤(2:ℝ),W v=0) (hV : ∀ v≤(2:ℝ),V v=0)
    (hsmW : ContDiff ℝ ∞ (W : ℝ → ℂ)) (hsmV : ContDiff ℝ ∞ (V : ℝ → ℂ)) :
    inner ℂ (cubicThetaHighFourierMass h W hW hsmW) (cubicThetaHighFourierMass k V hV hsmV)=0 := by
  change inner ℂ (cubicThetaFourierProfileL2 h W hW) (cubicThetaFourierProfileL2 k V hV)=0
  exact cubicThetaFourierProfile_orthogonal hhk W V hW hV

lemma cubicThetaIntertwining_adjoint {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (I : E →L[ℂ] F) (T : E →L[ℂ] E) (U : F →L[ℂ] F)
    (hT : ∀ u v,inner ℂ u (T v)=inner ℂ (T u) v)
    (hU : ∀ u v,inner ℂ u (U v)=inner ℂ (U u) v)
    (hI : ∀ u,U (I u)=I (T u)) (f : F) : I.adjoint (U f)=T (I.adjoint f) := by
  apply ext_inner_right ℂ
  intro u
  rw [ContinuousLinearMap.adjoint_inner_left,←hU,hI,
    ←ContinuousLinearMap.adjoint_inner_left,hT]

lemma cubicThetaPrimeCubeMass_adjoint_energy {p : Eisenstein} (hp : primaryPrime p)
    (f : cubicThetaAutomorphicL2) :
    cubicThetaGlobalEnergyValueMap.adjoint (cubicThetaPrimeCubeHeckeMass hp f)=
      cubicThetaPrimeCubeHeckeEnergy hp (cubicThetaGlobalEnergyValueMap.adjoint f) := by
  exact cubicThetaIntertwining_adjoint cubicThetaGlobalEnergyValueMap
    (cubicThetaPrimeCubeHeckeEnergy hp) (cubicThetaPrimeCubeHeckeMass hp)
    (cubicThetaPrimeCubeHecke_symmetric hp) (cubicThetaPrimeCubeHeckeMass_symmetric hp)
    (cubicThetaPrimeCubeHeckeMass_energy hp) f

end CubicFirstMoment

end

end OAI
