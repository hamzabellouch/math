import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeRootFourierMass
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeRootWeylMeasure

namespace OAI

/-! The actual Hermitian pairing on the finite arithmetic root cover.
Both root translations and Weyl inversion preserve its integral. -/
noncomputable section
open MeasureTheory
namespace CubicFirstMoment

def cubicThetaPrimeRootSectionPairing {p : Eisenstein} (hp : primaryPrime p)
    (F G : cubicThetaPrimeRootSections p) : CubicThetaPrimeRootCover hp → ℂ :=
  Quotient.lift (fun x : CubicThetaPoint => star (F.val x)*G.val x) (by
    intro x y hxy
    obtain ⟨g,hg⟩ := hxy
    dsimp only at hg
    rw [←hg,cubicThetaPrimeRootSection_property hp F,cubicThetaPrimeRootSection_property hp G,
      star_mul]
    have hk : star (cubicThetaKubotaValue g.val)*cubicThetaKubotaValue g.val=1 := by
      rw [mul_comm,Complex.star_def,Complex.mul_conj',cubicThetaKubotaValue_norm]
      norm_num
    calc
      _ = (star (cubicThetaKubotaValue g.val)*cubicThetaKubotaValue g.val)*
          (star (F.val y)*G.val y) := by ring
      _ = _ := by rw [hk,one_mul])

lemma cubicThetaPrimeRootSectionPairing_apply {p : Eisenstein} (hp : primaryPrime p)
    (F G : cubicThetaPrimeRootSections p) (x : CubicThetaPoint) :
    cubicThetaPrimeRootSectionPairing hp F G (cubicThetaPrimeRootCoverMap hp x)=
      star (F.val x)*G.val x := rfl

lemma cubicThetaPrimeRootSectionPairing_continuous {p : Eisenstein} (hp : primaryPrime p)
    (F G : cubicThetaPrimeRootSections p) :
    Continuous (cubicThetaPrimeRootSectionPairing hp F G) := by
  apply (cubicThetaPrimeRootCoverMap_open hp).isQuotientMap.continuous_iff.mpr
  exact F.val.continuous.star.mul G.val.continuous

lemma cubicThetaPrimeRootSectionPairing_smul {p : Eisenstein} (hp : primaryPrime p)
    (F G : cubicThetaPrimeRootSections p) (a b : ℂ) (q : CubicThetaPrimeRootCover hp) :
    cubicThetaPrimeRootSectionPairing hp (a • F) (b • G) q=
      (star a*b)*cubicThetaPrimeRootSectionPairing hp F G q := by
  induction q using Quotient.inductionOn with
  | h y =>
    change star (a*F.val y)*(b*G.val y)=(star a*b)*(star (F.val y)*G.val y)
    rw [star_mul]
    ring

lemma cubicThetaPrimeRootSectionPairing_translate {p : Eisenstein} (hp : primaryPrime p)
    (F G : cubicThetaPrimeRootSections p) (r : Residues p) (q : CubicThetaPrimeRootCover hp) :
    cubicThetaPrimeRootSectionPairing hp (cubicThetaPrimeRootResidueOperator hp r F)
      (cubicThetaPrimeRootResidueOperator hp r G) q=
      cubicThetaPrimeRootSectionPairing hp F G
        (cubicThetaPrimeRootCoverTranslate hp (residueRepresentative p r) q) := by
  induction q using Quotient.inductionOn with
  | h y => rfl

theorem cubicThetaPrimeRootSectionPairing_translation_integral {p : Eisenstein}
    (hp : primaryPrime p) (F G : cubicThetaPrimeRootSections p) (r : Residues p) :
    (∫ q, cubicThetaPrimeRootSectionPairing hp (cubicThetaPrimeRootResidueOperator hp r F)
      (cubicThetaPrimeRootResidueOperator hp r G) q ∂cubicThetaPrimeRootCoverMeasure hp)=
      ∫ q, cubicThetaPrimeRootSectionPairing hp F G q ∂cubicThetaPrimeRootCoverMeasure hp := by
  simp_rw [cubicThetaPrimeRootSectionPairing_translate]
  exact (cubicThetaPrimeRootCoverTranslate_measurePreserving hp (residueRepresentative p r)).integral_comp
    (cubicThetaPrimeRootCoverHomeomorph hp (residueRepresentative p r)).measurableEmbedding _

theorem cubicThetaPrimeRootSectionPairing_weyl_integral {p : Eisenstein}
    (hp : primaryPrime p) (F G : cubicThetaPrimeRootSections p) :
    (∫ q, cubicThetaPrimeRootSectionPairing hp (cubicThetaPrimeRootWeylSection hp F)
      (cubicThetaPrimeRootWeylSection hp G) q ∂cubicThetaPrimeRootCoverMeasure hp)=
      ∫ q, cubicThetaPrimeRootSectionPairing hp F G q ∂cubicThetaPrimeRootCoverMeasure hp := by
  have he (q : CubicThetaPrimeRootCover hp) :
      cubicThetaPrimeRootSectionPairing hp (cubicThetaPrimeRootWeylSection hp F)
        (cubicThetaPrimeRootWeylSection hp G) q=
      cubicThetaPrimeRootSectionPairing hp F G (cubicThetaPrimeRootCoverWeyl hp q) := by
    induction q using Quotient.inductionOn with
    | h y => rfl
  simp_rw [he]
  exact (cubicThetaPrimeRootCoverWeyl_measurePreserving hp).integral_comp
    (cubicThetaPrimeRootCoverWeylHomeomorph hp).measurableEmbedding _

end CubicFirstMoment

end

end OAI
