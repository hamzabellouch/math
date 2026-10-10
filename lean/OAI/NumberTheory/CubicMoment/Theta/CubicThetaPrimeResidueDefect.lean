import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeResidueObservationMap

namespace OAI

/-! The two missing local-image conditions as bounded functionals of
the actual energy space. No vanishing assertion is assumed here. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaPrimeFirstDefect {p : Eisenstein} (hp : primaryPrime p) (h : Eisenstein) :
    cubicThetaGlobalEnergySpace →L[ℂ] ℂ :=
  (ContinuousLinearMap.proj (1 : Fin 3)).comp (cubicThetaPrimeResidueObservationMap hp h)-
    (cubicThetaPrimeAdditiveGauss p hp 2 h/(norm p:ℂ)) •
      (ContinuousLinearMap.proj (0 : Fin 3)).comp (cubicThetaPrimeResidueObservationMap hp h)

def cubicThetaPrimeSecondDefect {p : Eisenstein} (hp : primaryPrime p) (h : Eisenstein) :
    cubicThetaGlobalEnergySpace →L[ℂ] ℂ :=
  (ContinuousLinearMap.proj (2 : Fin 3)).comp (cubicThetaPrimeResidueObservationMap hp h)

def cubicThetaPrimeFirstDefectVector {p : Eisenstein} (hp : primaryPrime p) (h : Eisenstein) :
    cubicThetaGlobalEnergySpace := (cubicThetaPrimeFirstDefect hp h).adjoint 1

def cubicThetaPrimeSecondDefectVector {p : Eisenstein} (hp : primaryPrime p) (h : Eisenstein) :
    cubicThetaGlobalEnergySpace := (cubicThetaPrimeSecondDefect hp h).adjoint 1

lemma cubicThetaPrimeFirstDefectVector_pairing {p : Eisenstein} (hp : primaryPrime p)
    (h : Eisenstein) (u : cubicThetaGlobalEnergySpace) :
    inner ℂ (cubicThetaPrimeFirstDefectVector hp h) u=cubicThetaPrimeFirstDefect hp h u := by
  rw [cubicThetaPrimeFirstDefectVector,ContinuousLinearMap.adjoint_inner_left]
  simp

lemma cubicThetaPrimeSecondDefectVector_pairing {p : Eisenstein} (hp : primaryPrime p)
    (h : Eisenstein) (u : cubicThetaGlobalEnergySpace) :
    inner ℂ (cubicThetaPrimeSecondDefectVector hp h) u=cubicThetaPrimeSecondDefect hp h u := by
  rw [cubicThetaPrimeSecondDefectVector,ContinuousLinearMap.adjoint_inner_left]
  simp

theorem cubicThetaPrimeDefect_residue_iff {p : Eisenstein} (hp : primaryPrime p)
    (h : Eisenstein) (hh : ¬p∣h) :
    (cubicThetaPrimeFirstDefect hp h (cubicThetaArithmeticResidueEnergy (4/3))=0 ∧
      cubicThetaPrimeSecondDefect hp h (cubicThetaArithmeticResidueEnergy (4/3))=0) ↔
      (∃ v : Fin 3 → ℂ, (cubicThetaPrimeCriticalMatrix p hp h).mulVec v=
        cubicThetaPrimeResidueVector p h) := by
  have hh0 : h≠0 := fun hz => hh (hz ▸ dvd_zero p)
  have hc := cubicThetaPrimeResidueCommonFactor_ne_zero hp hh0
  rw [cubicThetaPrimeCriticalMatrix_range_iff hp h (hp.2.coprime_iff_not_dvd.mpr hh)]
  change ((cubicThetaPrimeResidueObservationMap hp h (cubicThetaArithmeticResidueEnergy (4/3)) 1-
      (cubicThetaPrimeAdditiveGauss p hp 2 h/(norm p:ℂ))*
        cubicThetaPrimeResidueObservationMap hp h (cubicThetaArithmeticResidueEnergy (4/3)) 0)=0 ∧
      cubicThetaPrimeResidueObservationMap hp h (cubicThetaArithmeticResidueEnergy (4/3)) 2=0) ↔ _
  rw [cubicThetaPrimeResidueObservationMap_residue hp hh0]
  simp only [Pi.smul_apply,smul_eq_mul]
  have he : cubicThetaPrimeResidueCommonFactor hp h*cubicThetaPrimeResidueVector p h 1-
      (cubicThetaPrimeAdditiveGauss p hp 2 h/(norm p:ℂ))*
        (cubicThetaPrimeResidueCommonFactor hp h*cubicThetaPrimeResidueVector p h 0)=
      cubicThetaPrimeResidueCommonFactor hp h*(cubicThetaPrimeResidueVector p h 1-
        (cubicThetaPrimeAdditiveGauss p hp 2 h/(norm p:ℂ))*cubicThetaPrimeResidueVector p h 0) := by ring
  rw [he]
  simp only [mul_eq_zero,hc,false_or,sub_eq_zero]

theorem cubicThetaPrimeDefectVector_residue_iff {p : Eisenstein} (hp : primaryPrime p)
    (h : Eisenstein) (hh : ¬p∣h) :
    (inner ℂ (cubicThetaPrimeFirstDefectVector hp h) (cubicThetaArithmeticResidueEnergy (4/3))=0 ∧
      inner ℂ (cubicThetaPrimeSecondDefectVector hp h) (cubicThetaArithmeticResidueEnergy (4/3))=0) ↔
      cubicThetaArithmeticFourierResidue (p^3*h) (4/3)=cubicThetaArithmeticFourierResidue h (4/3) ∧
        cubicThetaArithmeticFourierResidue (p^2*h) (4/3)=0 := by
  rw [cubicThetaPrimeFirstDefectVector_pairing,cubicThetaPrimeSecondDefectVector_pairing,
    cubicThetaPrimeDefect_residue_iff hp h hh,cubicThetaPrimeResidueImage_iff_identities hp h hh]

end CubicFirstMoment

end

end OAI
