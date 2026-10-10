import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeDoubleRootTranslationIntegral
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeRootFirstIntegral

namespace OAI

/-! Transport of intermediate root orthogonality to the cubic root cover. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaPrimeCubeRoot_le_double {p : Eisenstein} (hp : primaryPrime p) :
    cubicThetaPrimeCubeRootCoverGroup hp≤cubicThetaPrimeDoubleRootSubgroup p := by
  intro g hg
  constructor
  · exact (show (p^2)^2∣(p^3)^2 from ⟨p^2,by ring⟩).trans hg.1
  · exact (show p^2∣p^3 from ⟨p,by ring⟩).trans hg.2

lemma cubicThetaPrimeDoubleRoot_translate_pair_invariant {p : Eisenstein} (hp : primaryPrime p)
    (x : Eisenstein) (F G : CubicThetaSection)
    (g : cubicThetaPrimeDoubleRootSubgroup p) (z : CubicThetaPoint) :
    star (F.val (g • z))*G.val (cubicThetaPrimeDoubleRootElement hp x • (g • z))=
      star (F.val z)*G.val (cubicThetaPrimeDoubleRootElement hp x • z) :=
  cubicThetaPrimeDoubleRoot_pair_invariant hp (cubicThetaPrimeRootSectionRestrict F)
    (cubicThetaPrimeDoubleRootSectionTranslate hp x (cubicThetaPrimeRootSectionRestrict G)) g z

theorem cubicThetaPrimeCubeRoot_second_integral_zero {p : Eisenstein} (hp : primaryPrime p)
    (x : Eisenstein) (hx : ¬p∣x) (F G : CubicThetaSection) :
    (∫ z in cubicThetaPrimeCubeRootCoverDomain hp,star (F.val z)*
      G.val (cubicThetaPrimeDoubleRootElement hp x • z) ∂cubicThetaPointMeasure)=0 := by
  have he := cubicThetaFiniteCover_integral (cubicThetaDoubleRootCover hp)
    (cubicThetaPrimeCubeRootCoverGroup hp) (cubicThetaPrimeCubeRoot_le_double hp)
    (cubicThetaPrimeCubeRootCoverDomain hp)
    (cubicThetaPrimeCubeRootCoverDomain_isFundamentalDomain hp cubicThetaPointMeasure)
    (f:=fun z => star (F.val z)*G.val (cubicThetaPrimeDoubleRootElement hp x • z))
    (cubicThetaPrimeDoubleRoot_translate_pair_invariant hp x F G)
  change (∫ z in cubicThetaPrimeCubeRootCoverDomain hp,star (F.val z)*
    G.val (cubicThetaPrimeDoubleRootElement hp x • z) ∂cubicThetaPointMeasure)=_ at he
  rw [show (∫ z in (cubicThetaDoubleRootCover hp).domain,star (F.val z)*
      G.val (cubicThetaPrimeDoubleRootElement hp x • z) ∂cubicThetaPointMeasure)=0 from
        cubicThetaPrimeDoubleRoot_translation_integral_zero hp x hx F G,smul_zero] at he
  exact he

lemma cubicThetaPrimeCubeRootElement_single {p : Eisenstein} (hp : primaryPrime p)
    (x : Eisenstein) :
    cubicThetaPrimeCubeRootElement hp (p*x)=cubicThetaPrimeDoubleRootElement hp x := by
  rw [cubicThetaPrimeCubeRootElement_translation,cubicThetaPrimeDoubleRootElement_translation]
  congr 1
  have hpC : (p:ℂ)≠0 := fun he => hp.2.ne_zero (Subtype.ext he)
  push_cast
  field_simp [hpC]

theorem cubicThetaPrimeCubeRoot_single_integral_zero {p : Eisenstein} (hp : primaryPrime p)
    (x : Eisenstein) (hx : ¬p∣x) (F G : CubicThetaSection) :
    (∫ z in cubicThetaPrimeCubeRootCoverDomain hp,star (F.val z)*
      G.val (cubicThetaPrimeCubeRootElement hp (p*x) • z) ∂cubicThetaPointMeasure)=0 := by
  rw [cubicThetaPrimeCubeRootElement_single]
  exact cubicThetaPrimeCubeRoot_second_integral_zero hp x hx F G

end CubicFirstMoment

end

end OAI
