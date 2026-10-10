import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeDoubleRootPairing
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeDoubleRootGlobal
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeRootPowerOrthogonal

namespace OAI

/-! The twice-squared dilation has a nontrivial diagonal character.
Its actual integral pairing with global sections vanishes. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

def cubicThetaPrimeDoubleSquareConjugate {p : Eisenstein} (hp : primaryPrime p)
    (g : cubicThetaPrimeIwahori ((p^2)^2)) : cubicThetaPrimeIwahori (p^2) :=
  ⟨cubicThetaPrimeConjugate (cubicThetaPrimeDouble_primary hp) (cubicThetaPrimeSquareIwahori g),by
    change p^2∣g.val.val 1 0/p^2
    obtain ⟨b,hb⟩ := g.property
    rw [hb,show (p^2)^2*b=p^2*(p^2*b) by ring,
      mul_div_cancel_left₀ _ (pow_ne_zero 2 hp.2.ne_zero)]
    exact dvd_mul_right (p^2) b⟩

lemma cubicThetaPrimeDoubleSquareConjugate_kubota {p : Eisenstein} (hp : primaryPrime p)
    (g : cubicThetaPrimeIwahori ((p^2)^2)) :
    cubicThetaKubotaValue (cubicThetaPrimeConjugate (cubicThetaPrimeDouble_primary hp)
      (cubicThetaPrimeDoubleSquareConjugate hp g))=
    star ((cubicSymbol p (g.val.val 0 0))^4)*cubicThetaKubotaValue g.val := by
  have h1 := cubicThetaPrimePowerConjugate_kubota_star hp 2 (cubicThetaPrimeSquareIwahori g)
  have h2 := cubicThetaPrimePowerConjugate_kubota_star hp 2 (cubicThetaPrimeDoubleSquareConjugate hp g)
  change cubicThetaKubotaValue (cubicThetaPrimeConjugate (cubicThetaPrimeDouble_primary hp)
    (cubicThetaPrimeSquareIwahori g))=
    star ((cubicSymbol p (g.val.val 0 0))^2)*cubicThetaKubotaValue g.val at h1
  change cubicThetaKubotaValue (cubicThetaPrimeConjugate (cubicThetaPrimeDouble_primary hp)
    (cubicThetaPrimeDoubleSquareConjugate hp g))=
    star ((cubicSymbol p (g.val.val 0 0))^2)*cubicThetaKubotaValue
      (cubicThetaPrimeConjugate (cubicThetaPrimeDouble_primary hp) (cubicThetaPrimeSquareIwahori g)) at h2
  rw [h2,h1,show (cubicSymbol p (g.val.val 0 0))^4=
    (cubicSymbol p (g.val.val 0 0))^2*(cubicSymbol p (g.val.val 0 0))^2 by ring,star_mul]
  ring

lemma cubicThetaPrimeDoubleRootWeyl_global_transform {p : Eisenstein} (hp : primaryPrime p)
    (g : cubicThetaPrimeIwahori ((p^2)^2)) (F : CubicThetaSection) (x : CubicThetaPoint) :
    (cubicThetaPrimeDoubleRootWeylSection hp (cubicThetaPrimeRootSectionRestrict F)).val (g.val • x)=
      star ((cubicSymbol p (g.val.val 0 0))^4)*cubicThetaKubotaValue g.val*
        (cubicThetaPrimeDoubleRootWeylSection hp (cubicThetaPrimeRootSectionRestrict F)).val x := by
  let D := cubicThetaPrimeDilation (pow_ne_zero 2 hp.2.ne_zero)
  have h1 := cubicThetaPrimeDilation_intertwines (cubicThetaPrimeDouble_primary hp)
    (cubicThetaPrimeSquareIwahori g)
  have h2 := cubicThetaPrimeDilation_intertwines (cubicThetaPrimeDouble_primary hp)
    (cubicThetaPrimeDoubleSquareConjugate hp g)
  change D*cubicThetaPrincipalComplex g.val=
    cubicThetaPrincipalComplex (cubicThetaPrimeConjugate (cubicThetaPrimeDouble_primary hp)
      (cubicThetaPrimeSquareIwahori g))*D at h1
  change D*cubicThetaPrincipalComplex (cubicThetaPrimeConjugate (cubicThetaPrimeDouble_primary hp)
    (cubicThetaPrimeSquareIwahori g))=
    cubicThetaPrincipalComplex (cubicThetaPrimeConjugate (cubicThetaPrimeDouble_primary hp)
      (cubicThetaPrimeDoubleSquareConjugate hp g))*D at h2
  have he : D*(D*cubicThetaPrincipalComplex g.val)=
      cubicThetaPrincipalComplex (cubicThetaPrimeConjugate (cubicThetaPrimeDouble_primary hp)
        (cubicThetaPrimeDoubleSquareConjugate hp g))*(D*D) := by
    rw [h1,←mul_assoc,h2,mul_assoc]
  rw [cubicThetaPrimeDoubleRootWeyl_global_zero,cubicThetaPrimeDoubleRootWeyl_global_zero]
  change (cubicThetaInversionSection F).val (D • (D • (cubicThetaPrincipalComplex g.val • x)))=_
  rw [←mul_smul,←mul_smul,mul_assoc,he,mul_smul,mul_smul]
  change (cubicThetaInversionSection F).val
    (cubicThetaPrimeConjugate (cubicThetaPrimeDouble_primary hp)
      (cubicThetaPrimeDoubleSquareConjugate hp g) • (D • (D • x)))=_
  rw [(cubicThetaInversionSection F).property,cubicThetaPrimeDoubleSquareConjugate_kubota]

lemma cubicThetaPrimeDoubleRootWeyl_pair_zero {p : Eisenstein} (hp : primaryPrime p)
    (F G : CubicThetaSection) :
    (∫ x in cubicThetaPrimeDoubleRootDomain hp,star (F.val x)*
      (cubicThetaPrimeDoubleRootWeylSection hp (cubicThetaPrimeRootSectionRestrict G)).val x
        ∂cubicThetaPointMeasure)=0 := by
  let H := cubicThetaPrimeDoubleRootWeylSection hp (cubicThetaPrimeRootSectionRestrict G)
  let f : CubicThetaPoint → ℂ := fun x => star (F.val x)*H.val x
  obtain ⟨g,hg⟩ := cubicThetaPrimeSixthCharacter_nontrivial hp
  let j : cubicThetaPrimeIwahori ((p^2)^2) := ⟨g.val,by
    change (p^2)^2∣g.val.val 1 0
    have hd : p^4∣g.val.val 1 0 := (pow_dvd_pow p (by decide : 4≤6)).trans g.property
    simpa only [←pow_mul] using hd⟩
  let c : ℂ := star ((cubicSymbol p (g.val.val 0 0))^4)
  have hc : c≠1 := by
    have h3 : (cubicSymbol p (g.val.val 0 0))^3=1 :=
      cubicThetaPrimeIwahoriCharacter_cube hp (cubicThetaPrimeSixthIwahori g)
    intro he
    have he' : (cubicSymbol p (g.val.val 0 0))^4=1 := by
      simpa only [c,star_star,star_one] using congrArg star he
    rw [show (cubicSymbol p (g.val.val 0 0))^4=(cubicSymbol p (g.val.val 0 0))^3*
      cubicSymbol p (g.val.val 0 0) by ring,h3,one_mul] at he'
    exact hg he'
  have hi := (cubicThetaPrimeDoubleRootDomain_fundamental hp).setIntegral_eq (f:=f)
    (cubicThetaPrimeDoubleRootIwahoriImage_fundamental hp (cubicThetaPrimeSixthPowerIwahori 2 (by decide) g))
    (cubicThetaPrimeDoubleRoot_pair_invariant hp (cubicThetaPrimeRootSectionRestrict F) H)
  have hm := (measurePreserving_smul g.val cubicThetaPointMeasure).setIntegral_image_emb
    (measurableEmbedding_const_smul g.val) f (cubicThetaPrimeDoubleRootDomain hp)
  have he : (∫ x in cubicThetaPrimeDoubleRootDomain hp,f x ∂cubicThetaPointMeasure)=
      ∫ x in cubicThetaPrimeDoubleRootDomain hp,f (g.val • x) ∂cubicThetaPointMeasure := hi.trans hm
  have hfun : (fun x => f (g.val • x))=fun x => c*f x := by
    funext x
    have hG := cubicThetaPrimeDoubleRootWeyl_global_transform hp j G x
    change H.val (g.val • x)=c*cubicThetaKubotaValue g.val*H.val x at hG
    dsimp only [f]
    rw [F.property,hG,star_mul]
    have hk : star (cubicThetaKubotaValue g.val)*cubicThetaKubotaValue g.val=1 := by
      rw [mul_comm,Complex.star_def,Complex.mul_conj',cubicThetaKubotaValue_norm]
      norm_num
    calc
      _ = (star (cubicThetaKubotaValue g.val)*cubicThetaKubotaValue g.val)*
        (c*(star (F.val x)*H.val x)) := by ring
      _ = _ := by rw [hk,one_mul]
  rw [hfun,integral_const_mul] at he
  exact eq_zero_of_mul_eq_self_left hc he.symm

end CubicFirstMoment

end

end OAI
