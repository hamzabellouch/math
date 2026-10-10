import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeRootWeylAverage

namespace OAI

/-! The once-dilated global section is an actual root-cover section.
It lies in the zero root-frequency space and intertwines the two Weyl actions. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaPrimeRootDilationSection {p : Eisenstein} (hp : primaryPrime p)
    (F : CubicThetaSection) : cubicThetaPrimeRootSections p :=
  ⟨⟨fun y => F.val (cubicThetaPrimeDilation hp.2.ne_zero • y),
    F.val.continuous.comp (continuous_const_smul _)⟩,by
    intro g y
    have hD : cubicThetaPrimeDilation hp.2.ne_zero*cubicThetaPrincipalComplex g.val=
        cubicThetaPrincipalComplex (cubicThetaPrimeRootDilationIwahori hp g).val*
          cubicThetaPrimeDilation hp.2.ne_zero :=
      cubicThetaPrimeDilation_intertwines hp.1 (cubicThetaPrimeRootIwahori g)
    change F.val (cubicThetaPrimeDilation hp.2.ne_zero • (cubicThetaPrincipalComplex g.val • y))=_
    rw [←mul_smul,hD,mul_smul]
    change F.val ((cubicThetaPrimeRootDilationIwahori hp g).val •
      (cubicThetaPrimeDilation hp.2.ne_zero • y))=_
    rw [F.property,cubicThetaPrimeRootDilation_kubota]
    rfl⟩

lemma cubicThetaPrimeRootDilationSection_translate {p : Eisenstein} (hp : primaryPrime p)
    (x : Eisenstein) (F : CubicThetaSection) :
    cubicThetaPrimeRootSectionTranslate hp x (cubicThetaPrimeRootDilationSection hp F)=
      cubicThetaPrimeRootDilationSection hp F := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro y
  change F.val (cubicThetaPrimeDilation hp.2.ne_zero • (cubicThetaPrimeRootElement hp x • y))=
    F.val (cubicThetaPrimeDilation hp.2.ne_zero • y)
  have he : cubicThetaPrimeDilation hp.2.ne_zero*cubicThetaPrimeRootElement hp x=
      cubicThetaPrincipalComplex (cubicThetaPrincipalTranslation x)*cubicThetaPrimeDilation hp.2.ne_zero := by
    rw [cubicThetaPrimeRootElement]
    group
  rw [←mul_smul,he,mul_smul]
  change F.val (cubicThetaPrincipalTranslation x • (cubicThetaPrimeDilation hp.2.ne_zero • y))=_
  rw [F.property,cubicThetaPrincipalTranslation_value,one_mul]

theorem cubicThetaPrimeRootDilationSection_average {p : Eisenstein} (hp : primaryPrime p)
    (F : CubicThetaSection) :
    cubicThetaPrimeRootAverage hp (cubicThetaPrimeRootDilationSection hp F)=
      cubicThetaPrimeRootDilationSection hp F := by
  apply cubicThetaPrimeRootAverage_fixed
  intro r
  exact cubicThetaPrimeRootDilationSection_translate hp (residueRepresentative p r) F

end CubicFirstMoment

end

end OAI
