import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeLiftOrthogonality
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaNonzeroSpectralResidue
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaGlobalAutomorphicRange

namespace OAI

/-! The nonzero arithmetic spectral residue is lifted to the actual
prime cover. Its Atkin translate has equal norm and is orthogonal to it. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaArithmeticResidueL2 : cubicThetaAutomorphicL2 :=
  ⟨cubicThetaGlobalInclusion (cubicThetaArithmeticResidueEnergy (4/3)),
    cubicThetaGlobalInclusion_mem _⟩

lemma cubicThetaArithmeticResidueL2_ne_zero : cubicThetaArithmeticResidueL2≠0 := by
  intro he
  apply cubicThetaArithmeticResidueValue_ne_zero
  exact congrArg Subtype.val he

def cubicThetaPrimeArithmeticResidue {p : Eisenstein} (hp : primaryPrime p) :
    cubicThetaPrimeAutomorphicL2 hp := cubicThetaPrimeLiftL2 hp cubicThetaArithmeticResidueL2

lemma cubicThetaPrimeArithmeticResidue_ne_zero {p : Eisenstein} (hp : primaryPrime p) :
    cubicThetaPrimeArithmeticResidue hp≠0 := by
  intro he
  apply cubicThetaArithmeticResidueL2_ne_zero
  apply (cubicThetaPrimeLiftL2 hp).injective
  simpa only [cubicThetaPrimeArithmeticResidue,map_zero] using he

theorem cubicThetaPrimeArithmeticResidue_orthogonal {p : Eisenstein} (hp : primaryPrime p) :
    inner ℂ (cubicThetaPrimeArithmeticResidue hp)
      (cubicThetaPrimeAtkinL2 hp (cubicThetaPrimeArithmeticResidue hp))=0 :=
  cubicThetaPrimeLiftAtkin_orthogonal hp _ _

theorem cubicThetaPrimeArithmeticResidue_norm {p : Eisenstein} (hp : primaryPrime p) :
    ‖cubicThetaPrimeAtkinL2 hp (cubicThetaPrimeArithmeticResidue hp)‖=
      ‖cubicThetaGlobalInclusion (cubicThetaArithmeticResidueEnergy (4/3))‖ := by
  rw [(cubicThetaPrimeAtkinL2 hp).norm_map]
  exact (cubicThetaPrimeLiftL2 hp).norm_map _

end CubicFirstMoment

end

end OAI
