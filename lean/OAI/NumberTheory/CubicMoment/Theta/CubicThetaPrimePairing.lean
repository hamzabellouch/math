import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeKernelNormaliser
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeSectionNorm

namespace OAI

/-! Orthogonality of an original section and a prime Atkin translate.
The cancellation is an actual integral on the common finite cover. -/
noncomputable section
open MeasureTheory Set
namespace CubicFirstMoment

lemma cubicThetaPrimeSectionPair_invariant {p : Eisenstein} (hp : primaryPrime p)
    (F G : cubicThetaPrimeSections hp) (g : cubicThetaPrimeCoverGroup hp)
    (x : CubicThetaPoint) :
    star (F.val (g • x))*G.val (g • x)=star (F.val x)*G.val x := by
  rw [cubicThetaPrimeSection_property hp F,cubicThetaPrimeSection_property hp G,star_mul]
  have hk : star (cubicThetaKubotaValue g.val)*cubicThetaKubotaValue g.val=1 := by
    rw [mul_comm,Complex.star_def,Complex.mul_conj',cubicThetaKubotaValue_norm]
    norm_num
  calc
    _ = (star (cubicThetaKubotaValue g.val)*cubicThetaKubotaValue g.val)*
        (star (F.val x)*G.val x) := by ring
    _ = _ := by rw [hk,one_mul]

lemma cubicThetaPrimeAtkinConjugate_kubota {p : Eisenstein} (hp : primaryPrime p)
    (g : cubicThetaPrimeIwahori p) :
    cubicThetaKubotaValue g.val=cubicThetaPrimeIwahoriCharacter p hp g*
      cubicThetaKubotaValue (cubicThetaPrimeAtkinConjugate hp g).val := by
  rw [cubicThetaPrimeConjugate_kubota hp g]
  congr 1
  exact (cubicThetaInversionConjugate_character (cubicThetaPrimeConjugate hp.1 g)).symm

lemma cubicThetaPrimeOriginalAtkinPair_translate {p : Eisenstein} (hp : primaryPrime p)
    (F G : CubicThetaSection) (g : cubicThetaPrimeIwahori p) (x : CubicThetaPoint) :
    star (F.val (g.val • x))*G.val (cubicThetaPrimeAtkinMatrix hp • (g.val • x))=
      star (cubicThetaPrimeIwahoriCharacter p hp g)*
        (star (F.val x)*G.val (cubicThetaPrimeAtkinMatrix hp • x)) := by
  have ht : cubicThetaPrimeAtkinMatrix hp • (g.val • x)=
      (cubicThetaPrimeAtkinConjugate hp g).val • (cubicThetaPrimeAtkinMatrix hp • x) := by
    change cubicThetaPrimeAtkinMatrix hp • (cubicThetaPrincipalComplex g.val • x)=
      cubicThetaPrincipalComplex (cubicThetaPrimeAtkinConjugate hp g).val •
        (cubicThetaPrimeAtkinMatrix hp • x)
    rw [←mul_smul,←mul_smul,cubicThetaPrimeAtkinMatrix_intertwines]
  rw [ht,F.property,G.property,cubicThetaPrimeAtkinConjugate_kubota hp g,star_mul]
  simp only [star_mul]
  have hk : star (cubicThetaKubotaValue (cubicThetaPrimeAtkinConjugate hp g).val)*
      cubicThetaKubotaValue (cubicThetaPrimeAtkinConjugate hp g).val=1 := by
    rw [mul_comm,Complex.star_def,Complex.mul_conj',cubicThetaKubotaValue_norm]
    norm_num
  calc
    _ = (star (cubicThetaKubotaValue (cubicThetaPrimeAtkinConjugate hp g).val)*
        cubicThetaKubotaValue (cubicThetaPrimeAtkinConjugate hp g).val)*
      (star (cubicThetaPrimeIwahoriCharacter p hp g)*
        (star (F.val x)*G.val (cubicThetaPrimeAtkinMatrix hp • x))) := by ring
    _ = _ := by rw [hk,one_mul]

theorem cubicThetaPrimeOriginalAtkinPair_integral_zero {p : Eisenstein} (hp : primaryPrime p)
    (F G : CubicThetaSection) :
    (∫ x in cubicThetaPrimeCoverDomain hp,
      star (F.val x)*G.val (cubicThetaPrimeAtkinMatrix hp • x) ∂cubicThetaPointMeasure)=0 := by
  let f : CubicThetaPoint → ℂ := fun x =>
    star (F.val x)*G.val (cubicThetaPrimeAtkinMatrix hp • x)
  obtain ⟨g,hg⟩ := cubicThetaPrimeIwahoriCharacter_nontrivial hp
  have hs : star (cubicThetaPrimeIwahoriCharacter p hp g)≠1 := by
    intro he
    apply hg
    simpa only [star_star,star_one] using congrArg star he
  have hinv (h : cubicThetaPrimeCoverGroup hp) (x : CubicThetaPoint) : f (h • x)=f x :=
    cubicThetaPrimeSectionPair_invariant hp (cubicThetaPrimeSectionRestrict hp F)
      (cubicThetaPrimeAtkinSection hp (cubicThetaPrimeSectionRestrict hp G)) h x
  have hi := (cubicThetaPrimeCoverDomain_isFundamentalDomain hp cubicThetaPointMeasure).setIntegral_eq
    (cubicThetaPrimeIntegralImage_fundamental hp g) hinv
  have hc := (measurePreserving_smul g.val cubicThetaPointMeasure).setIntegral_image_emb
    (measurableEmbedding_const_smul g.val) f (cubicThetaPrimeCoverDomain hp)
  have he : (∫ x in cubicThetaPrimeCoverDomain hp, f x ∂cubicThetaPointMeasure)=
      ∫ x in cubicThetaPrimeCoverDomain hp, f (g.val • x) ∂cubicThetaPointMeasure := hi.trans hc
  have hfun : (fun x => f (g.val • x))=fun x =>
      star (cubicThetaPrimeIwahoriCharacter p hp g)*f x :=
    funext (cubicThetaPrimeOriginalAtkinPair_translate hp F G g)
  rw [hfun,integral_const_mul] at he
  exact eq_zero_of_mul_eq_self_left hs he.symm

end CubicFirstMoment

end

end OAI
