import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeResiduePeriodicity
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeSquareResidueZero
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeResidueDefect

namespace OAI

/-! The actual arithmetic residue lies in the critical local Fourier
image; both required coefficient identities have been proved. -/
noncomputable section
namespace CubicFirstMoment

theorem cubicThetaArithmeticResidue_critical_image {p : Eisenstein} (hp : primaryPrime p)
    (h : Eisenstein) (hh : ¬p∣h) :
    ∃ v : Fin 3 → ℂ, (cubicThetaPrimeCriticalMatrix p hp h).mulVec v=
      cubicThetaPrimeResidueVector p h := by
  apply (cubicThetaPrimeResidueImage_iff_identities hp h hh).mpr
  exact ⟨cubicThetaArithmeticFourierResidue_cube hp h (fun he => hh (he ▸ dvd_zero p)),
    cubicThetaArithmeticFourierResidue_square_zero hp h hh⟩

theorem cubicThetaArithmeticResidue_prime_defects_zero {p : Eisenstein} (hp : primaryPrime p)
    (h : Eisenstein) (hh : ¬p∣h) :
    cubicThetaPrimeFirstDefect hp h (cubicThetaArithmeticResidueEnergy (4/3))=0 ∧
      cubicThetaPrimeSecondDefect hp h (cubicThetaArithmeticResidueEnergy (4/3))=0 :=
  (cubicThetaPrimeDefect_residue_iff hp h hh).mpr (cubicThetaArithmeticResidue_critical_image hp h hh)

end CubicFirstMoment

end

end OAI
