import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeRootWeylGlobal
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaInversionMass

namespace OAI

/-! Exact unit-branch transport on the cubic-scale Hilbert completion.
There is no arithmetic-residue or Hecke-eigenvector hypothesis here. -/
noncomputable section
namespace CubicFirstMoment

lemma cubicThetaPrimeCubeRootWeyl_translated_global {p : Eisenstein} (hp : primaryPrime p)
    (x y : Eisenstein) (hxy : p^3∣9*x*y-1) (F : CubicThetaSection) :
    cubicThetaPrimeCubeRootWeylSection hp
      (cubicThetaPrimeCubeRootSectionTranslate hp y (cubicThetaPrimeRootSectionRestrict F))=
      cubicThetaPrimeCubeRootSectionTranslate hp (-x)
        (cubicThetaPrimeRootSectionRestrict (cubicThetaInversionSection F)) := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro z
  change F.val (cubicThetaPrimeCubeRootElement hp y • (cubicThetaPrimeCubeRootWeylElement hp • z))=
    (cubicThetaInversionSection F).val (cubicThetaPrimeCubeRootElement hp (-x) • z)
  have he := cubicThetaPrimeCubeRootBruhat_section_one hp x y hxy F
    (cubicThetaPrimeCubeRootElement hp (-x) • z)
  have hx : cubicThetaPrimeCubeRootElement hp x • (cubicThetaPrimeCubeRootElement hp (-x) • z)=z := by
    rw [←mul_smul,←cubicThetaPrimeCubeRootElement_add,add_neg_cancel,
      cubicThetaPrimeCubeRootElement_zero,one_smul]
  rw [hx] at he
  exact he

lemma cubicThetaPrimeCubeRootFinite_bruhat {p : Eisenstein} (hp : primaryPrime p)
    (x y : Eisenstein) (hxy : p^3∣9*x*y-1) (F : cubicThetaSmoothTests) :
    cubicThetaPrimeCubeRootFiniteWeyl hp (cubicThetaPrimeCubeRootFiniteTranslate hp y
      (cubicThetaPrimeCubeRootSmoothRestriction hp F))=
      cubicThetaPrimeCubeRootFiniteTranslate hp (-x)
        (cubicThetaPrimeCubeRootSmoothRestriction hp (cubicThetaInversionSmooth F)) := by
  apply Subtype.ext
  exact cubicThetaPrimeCubeRootWeyl_translated_global hp x y hxy F.val

theorem cubicThetaPrimeCubeRootWeyl_mass_bruhat {p : Eisenstein} (hp : primaryPrime p)
    (x y : Eisenstein) (hxy : p^3∣9*x*y-1) (u : cubicThetaAutomorphicL2) :
    cubicThetaPrimeCubeRootWeylL2 hp
      (cubicThetaPrimeCubeRootTranslateL2 hp y (cubicThetaPrimeCubeRootLiftL2 hp u))=
      cubicThetaPrimeCubeRootTranslateL2 hp (-x)
        (cubicThetaPrimeCubeRootLiftL2 hp (cubicThetaInversionMass u)) := by
  refine cubicThetaGlobalMassClosure_dense.induction_on u
    (isClosed_eq ((cubicThetaPrimeCubeRootWeylL2 hp).continuous.comp
      ((cubicThetaPrimeCubeRootTranslateL2 hp y).continuous.comp (cubicThetaPrimeCubeRootLiftL2 hp).continuous))
      ((cubicThetaPrimeCubeRootTranslateL2 hp (-x)).continuous.comp
        ((cubicThetaPrimeCubeRootLiftL2 hp).continuous.comp cubicThetaInversionMass.continuous))) ?_
  intro F
  simp only [cubicThetaInversionMass_smooth,cubicThetaPrimeCubeRootLiftL2_smooth,
    cubicThetaPrimeCubeRootNormalizedRestriction,LinearMap.smul_apply,LinearMap.comp_apply,
    map_smul,cubicThetaPrimeCubeRootTranslateL2_finite,cubicThetaPrimeCubeRootWeylL2_finite,
    cubicThetaPrimeCubeRootFinite_bruhat hp x y hxy]


theorem cubicThetaPrimeCubeRoot_unit_correlation {p : Eisenstein} (hp : primaryPrime p)
    (x y : Eisenstein) (hxy : p^3∣9*x*y-1) (u v : cubicThetaAutomorphicL2) :
    inner ℂ (cubicThetaPrimeCubeRootLiftL2 hp u)
      (cubicThetaPrimeCubeRootTranslateL2 hp y (cubicThetaPrimeCubeRootLiftL2 hp v))=
    inner ℂ (cubicThetaPrimeCubeRootWeylL2 hp (cubicThetaPrimeCubeRootLiftL2 hp u))
      (cubicThetaPrimeCubeRootLiftL2 hp (cubicThetaInversionMass v)) := by
  have hw := (cubicThetaPrimeCubeRootWeylL2 hp).inner_map_map
    (cubicThetaPrimeCubeRootLiftL2 hp u)
    (cubicThetaPrimeCubeRootTranslateL2 hp y (cubicThetaPrimeCubeRootLiftL2 hp v))
  rw [cubicThetaPrimeCubeRootWeyl_mass_bruhat hp x y hxy] at hw
  have ht := (cubicThetaPrimeCubeRootTranslateL2 hp x).inner_map_map
    (cubicThetaPrimeCubeRootWeylL2 hp (cubicThetaPrimeCubeRootLiftL2 hp u))
    (cubicThetaPrimeCubeRootTranslateL2 hp (-x)
      (cubicThetaPrimeCubeRootLiftL2 hp (cubicThetaInversionMass v)))
  rw [cubicThetaPrimeCubeRootWeyl_lift_translate,←cubicThetaPrimeCubeRootTranslateL2_add,
    add_neg_cancel,cubicThetaPrimeCubeRootTranslateL2_zero] at ht
  exact hw.symm.trans ht.symm

theorem cubicThetaPrimeCubeRoot_unit_residue_correlation {p : Eisenstein} (hp : primaryPrime p)
    (r : Residues (p^3)) (hr : IsUnit r) (u v : cubicThetaAutomorphicL2) :
    inner ℂ (cubicThetaPrimeCubeRootLiftL2 hp u)
      (cubicThetaPrimeCubeRootResidueL2 hp r (cubicThetaPrimeCubeRootLiftL2 hp v))=
    inner ℂ (cubicThetaPrimeCubeRootWeylL2 hp (cubicThetaPrimeCubeRootLiftL2 hp u))
      (cubicThetaPrimeCubeRootLiftL2 hp (cubicThetaInversionMass v)) :=
  cubicThetaPrimeCubeRoot_unit_correlation hp
    (residueRepresentative (p^3) (cubicThetaPrimeRootReciprocal (p^3) r))
    (residueRepresentative (p^3) r) (cubicThetaPrimeCubeRootReciprocal_pair hp r hr) u v

end CubicFirstMoment

end

end OAI
