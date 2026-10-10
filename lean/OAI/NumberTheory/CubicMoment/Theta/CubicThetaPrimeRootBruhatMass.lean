import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeRootWeylMass

namespace OAI

/-! Each nonzero Bruhat branch acts by its actual cubic multiplier
on the completed global mass space. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaPrimeRootFinite_bruhat {p : Eisenstein} (hp : primaryPrime p)
    (r : Residues p) (hr : IsUnit r) (F : cubicThetaSmoothTests) :
    cubicThetaPrimeRootFiniteWeyl hp (cubicThetaPrimeRootFiniteResidue hp r
      (cubicThetaPrimeRootSmoothRestriction hp F))=
      (cubicSymbol p 3*cubicResidueChar p hp r) •
        cubicThetaPrimeRootFiniteResidue hp (-cubicThetaPrimeRootReciprocal p r)
          (cubicThetaPrimeRootSmoothRestriction hp (cubicThetaInversionSmooth F)) := by
  apply Subtype.ext
  exact cubicThetaPrimeRootWeyl_residue_branch hp r hr F.val

theorem cubicThetaPrimeRootWeyl_mass_bruhat {p : Eisenstein} (hp : primaryPrime p)
    (r : Residues p) (hr : IsUnit r) (u : cubicThetaAutomorphicL2) :
    cubicThetaPrimeRootWeylL2 hp
      (cubicThetaPrimeRootResidueL2 hp r (cubicThetaPrimeRootLiftL2 hp u))=
      (cubicSymbol p 3*cubicResidueChar p hp r) •
        cubicThetaPrimeRootResidueL2 hp (-cubicThetaPrimeRootReciprocal p r)
          (cubicThetaPrimeRootLiftL2 hp (cubicThetaInversionMass u)) := by
  let L := (cubicThetaPrimeRootWeylL2 hp).toContinuousLinearMap.comp
    ((cubicThetaPrimeRootResidueL2 hp r).toContinuousLinearMap.comp
      (cubicThetaPrimeRootLiftL2 hp).toContinuousLinearMap)
  let R := (cubicSymbol p 3*cubicResidueChar p hp r) •
    (cubicThetaPrimeRootResidueL2 hp (-cubicThetaPrimeRootReciprocal p r)).toContinuousLinearMap.comp
      ((cubicThetaPrimeRootLiftL2 hp).toContinuousLinearMap.comp cubicThetaInversionMass.toContinuousLinearMap)
  change L u=R u
  refine cubicThetaGlobalMassClosure_dense.induction_on u (isClosed_eq L.continuous R.continuous) ?_
  intro F
  change cubicThetaPrimeRootWeylL2 hp (cubicThetaPrimeRootResidueL2 hp r
    (cubicThetaPrimeRootLiftL2 hp (cubicThetaGlobalMassClosure F)))=
    (cubicSymbol p 3*cubicResidueChar p hp r) •
      cubicThetaPrimeRootResidueL2 hp (-cubicThetaPrimeRootReciprocal p r)
        (cubicThetaPrimeRootLiftL2 hp (cubicThetaInversionMass (cubicThetaGlobalMassClosure F)))
  simp only [cubicThetaInversionMass_smooth,cubicThetaPrimeRootLiftL2_smooth,
    cubicThetaPrimeRootNormalizedRestriction,LinearMap.smul_apply,LinearMap.comp_apply,
    map_smul,cubicThetaPrimeRootResidueL2_finite,cubicThetaPrimeRootWeylL2_finite]
  have he := congrArg (cubicThetaPrimeRootFiniteEmbedding hp)
    (cubicThetaPrimeRootFinite_bruhat hp r hr F)
  simp only [map_smul] at he
  rw [he]
  module

end CubicFirstMoment

end

end OAI
