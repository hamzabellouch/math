import OAI.NumberTheory.CubicMoment.Theta.CubicThetaFiniteCoverIntegral
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeRootTranslationIntegral
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeRootPowerOrthogonal
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeRootTranslation

namespace OAI

/-! Transfer of the first root level to the actual cube-root domain.
In particular the nonzero p-squared residue branches have zero pairing. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

def cubicThetaFirstRootCover {p : Eisenstein} (hp : primaryPrime p) : CubicThetaArithmeticCover where
  group := cubicThetaPrimeRootCoverGroup hp
  domain := cubicThetaPrimeRootCoverDomain hp
  measurable := cubicThetaPrimeRootCoverDomain_measurable hp
  unique := cubicThetaPrimeRootCoverDomain_unique hp

lemma cubicThetaPrimeCubeRoot_le_first {p : Eisenstein} (hp : primaryPrime p) :
    cubicThetaPrimeCubeRootCoverGroup hp≤cubicThetaPrimeRootCoverGroup hp := by
  intro g hg
  refine ⟨(show p^2∣(p^3)^2 from ⟨p^4,by ring⟩).trans hg.1,?_⟩
  exact (dvd_pow_self p (by decide : 3≠0)).trans hg.2

lemma cubicThetaPrimeRoot_translate_pair_invariant {p : Eisenstein} (hp : primaryPrime p)
    (x : Eisenstein) (F G : CubicThetaSection)
    (g : cubicThetaPrimeRootCoverGroup hp) (z : CubicThetaPoint) :
    star (F.val (g • z))*G.val (cubicThetaPrimeRootElement hp x • (g • z))=
      star (F.val z)*G.val (cubicThetaPrimeRootElement hp x • z) := by
  have hG := cubicThetaPrimeRootSection_property hp
    (cubicThetaPrimeRootSectionTranslate hp x (cubicThetaPrimeRootSectionRestrict G)) g z
  change G.val (cubicThetaPrimeRootElement hp x • (g.val • z))=
    cubicThetaKubotaValue g.val*G.val (cubicThetaPrimeRootElement hp x • z) at hG
  change star (F.val (g.val • z))*G.val (cubicThetaPrimeRootElement hp x • (g.val • z))=_
  rw [F.property,hG,star_mul]
  have hk : star (cubicThetaKubotaValue g.val)*cubicThetaKubotaValue g.val=1 := by
    rw [mul_comm,Complex.star_def,Complex.mul_conj',cubicThetaKubotaValue_norm]
    norm_num
  calc
    _ = (star (cubicThetaKubotaValue g.val)*cubicThetaKubotaValue g.val)*
      (star (F.val z)*G.val (cubicThetaPrimeRootElement hp x • z)) := by ring
    _ = _ := by rw [hk,one_mul]

theorem cubicThetaPrimeCubeRoot_first_integral_zero {p : Eisenstein} (hp : primaryPrime p)
    (x : Eisenstein) (hx : ¬p∣x) (F G : cubicThetaSmoothTests) :
    (∫ z in cubicThetaPrimeCubeRootCoverDomain hp,star (F.val.val z)*
      G.val.val (cubicThetaPrimeRootElement hp x • z) ∂cubicThetaPointMeasure)=0 := by
  have he := cubicThetaFiniteCover_integral (cubicThetaFirstRootCover hp)
    (cubicThetaPrimeCubeRootCoverGroup hp) (cubicThetaPrimeCubeRoot_le_first hp)
    (cubicThetaPrimeCubeRootCoverDomain hp)
    (cubicThetaPrimeCubeRootCoverDomain_isFundamentalDomain hp cubicThetaPointMeasure)
    (f:=fun z => star (F.val.val z)*G.val.val (cubicThetaPrimeRootElement hp x • z))
    (cubicThetaPrimeRoot_translate_pair_invariant hp x F.val G.val)
  change (∫ z in cubicThetaPrimeCubeRootCoverDomain hp,star (F.val.val z)*
    G.val.val (cubicThetaPrimeRootElement hp x • z) ∂cubicThetaPointMeasure)=_
    at he
  rw [show (∫ z in (cubicThetaFirstRootCover hp).domain,star (F.val.val z)*
      G.val.val (cubicThetaPrimeRootElement hp x • z) ∂cubicThetaPointMeasure)=0 from
        cubicThetaPrimeRoot_translation_integral_zero hp x hx F G,smul_zero] at he
  exact he

lemma cubicThetaPrimeCubeRootElement_square {p : Eisenstein} (hp : primaryPrime p)
    (x : Eisenstein) :
    cubicThetaPrimeCubeRootElement hp (p^2*x)=cubicThetaPrimeRootElement hp x := by
  rw [cubicThetaPrimeCubeRootElement_translation,cubicThetaPrimeRootElement_translation]
  congr 1
  have hpC : (p:ℂ)≠0 := fun he => hp.2.ne_zero (Subtype.ext he)
  push_cast
  field_simp [hpC]

theorem cubicThetaPrimeCubeRoot_square_integral_zero {p : Eisenstein} (hp : primaryPrime p)
    (x : Eisenstein) (hx : ¬p∣x) (F G : cubicThetaSmoothTests) :
    (∫ z in cubicThetaPrimeCubeRootCoverDomain hp,star (F.val.val z)*
      G.val.val (cubicThetaPrimeCubeRootElement hp (p^2*x) • z) ∂cubicThetaPointMeasure)=0 := by
  rw [cubicThetaPrimeCubeRootElement_square]
  exact cubicThetaPrimeCubeRoot_first_integral_zero hp x hx F G

end CubicFirstMoment

end

end OAI
