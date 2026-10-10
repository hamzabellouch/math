import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeRootSquareCharacter

namespace OAI

/-! The original and twice-dilated sections have distinct cubic
characters on an actual arithmetic subgroup, so their integral pairing vanishes. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaPrimeRootWeyl_global_square {p : Eisenstein} (hp : primaryPrime p)
    (g : cubicThetaPrimeIwahori (p^2)) (F : CubicThetaSection) (x : CubicThetaPoint) :
    (cubicThetaPrimeRootWeylSection hp (cubicThetaPrimeRootSectionRestrict F)).val (g.val • x)=
      cubicThetaPrimeIwahoriCharacter p hp (cubicThetaPrimeSquareIwahori g)*
        cubicThetaKubotaValue g.val*
          (cubicThetaPrimeRootWeylSection hp (cubicThetaPrimeRootSectionRestrict F)).val x := by
  let D := cubicThetaPrimeDilation hp.2.ne_zero
  have h1 := cubicThetaPrimeDilation_intertwines hp.1 (cubicThetaPrimeSquareIwahori g)
  have h2 := cubicThetaPrimeDilation_intertwines hp.1 (cubicThetaPrimeSquareConjugate hp g)
  change D*cubicThetaPrincipalComplex g.val=
    cubicThetaPrincipalComplex (cubicThetaPrimeConjugate hp.1 (cubicThetaPrimeSquareIwahori g))*D at h1
  change D*cubicThetaPrincipalComplex (cubicThetaPrimeConjugate hp.1 (cubicThetaPrimeSquareIwahori g))=
    cubicThetaPrincipalComplex (cubicThetaPrimeConjugate hp.1 (cubicThetaPrimeSquareConjugate hp g))*D at h2
  have he : D*(D*cubicThetaPrincipalComplex g.val)=
      cubicThetaPrincipalComplex (cubicThetaPrimeConjugate hp.1 (cubicThetaPrimeSquareConjugate hp g))*(D*D) := by
    rw [h1,←mul_assoc,h2,mul_assoc]
  rw [cubicThetaPrimeRootWeyl_global_zero,cubicThetaPrimeRootWeyl_global_zero]
  change (cubicThetaInversionSection F).val (D • (D • (cubicThetaPrincipalComplex g.val • x)))=_
  rw [←mul_smul,←mul_smul,mul_assoc,he,mul_smul,mul_smul]
  change (cubicThetaInversionSection F).val
    (cubicThetaPrimeConjugate hp.1 (cubicThetaPrimeSquareConjugate hp g) • (D • (D • x)))=_
  rw [(cubicThetaInversionSection F).property,cubicThetaPrimeSquareConjugate_kubota]

theorem cubicThetaPrimeRootSquare_pair_integral_zero {p : Eisenstein} (hp : primaryPrime p)
    (F G : CubicThetaSection) :
    (∫ x in cubicThetaPrimeRootCoverDomain hp,star (F.val x)*
      (cubicThetaPrimeRootWeylSection hp (cubicThetaPrimeRootSectionRestrict G)).val x
        ∂cubicThetaPointMeasure)=0 := by
  let H := cubicThetaPrimeRootWeylSection hp (cubicThetaPrimeRootSectionRestrict G)
  let f : CubicThetaPoint → ℂ := fun x => star (F.val x)*H.val x
  obtain ⟨g,hg⟩ := cubicThetaPrimeSquareCharacter_nontrivial hp
  let c := cubicThetaPrimeIwahoriCharacter p hp (cubicThetaPrimeSquareIwahori g)
  have hinv (h : cubicThetaPrimeRootCoverGroup hp) (x : CubicThetaPoint) : f (h • x)=f x := by
    change star (F.val (h.val • x))*H.val (h.val • x)=_
    have hH : H.val (h.val • x)=cubicThetaKubotaValue h.val*H.val x := H.property h x
    rw [F.property,hH,star_mul]
    have hk : star (cubicThetaKubotaValue h.val)*cubicThetaKubotaValue h.val=1 := by
      rw [mul_comm,Complex.star_def,Complex.mul_conj',cubicThetaKubotaValue_norm]
      norm_num
    calc
      _ = (star (cubicThetaKubotaValue h.val)*cubicThetaKubotaValue h.val)*f x := by dsimp [f]; ring
      _ = f x := by rw [hk,one_mul]
  have hi := (cubicThetaPrimeRootCoverDomain_isFundamentalDomain hp cubicThetaPointMeasure).setIntegral_eq
    (cubicThetaPrimeRootIwahoriImage_fundamental hp (cubicThetaPrimeSquareIwahori g)) hinv
  have hc := (measurePreserving_smul g.val cubicThetaPointMeasure).setIntegral_image_emb
    (measurableEmbedding_const_smul g.val) f (cubicThetaPrimeRootCoverDomain hp)
  have he : (∫ x in cubicThetaPrimeRootCoverDomain hp,f x ∂cubicThetaPointMeasure)=
      ∫ x in cubicThetaPrimeRootCoverDomain hp,f (g.val • x) ∂cubicThetaPointMeasure := hi.trans hc
  have hfun : (fun x => f (g.val • x))=fun x => c*f x := by
    funext x
    dsimp only [f,H,c]
    rw [F.property,cubicThetaPrimeRootWeyl_global_square,star_mul]
    have hk : star (cubicThetaKubotaValue g.val)*cubicThetaKubotaValue g.val=1 := by
      rw [mul_comm,Complex.star_def,Complex.mul_conj',cubicThetaKubotaValue_norm]
      norm_num
    calc
      _ = (star (cubicThetaKubotaValue g.val)*cubicThetaKubotaValue g.val)*
        (cubicThetaPrimeIwahoriCharacter p hp (cubicThetaPrimeSquareIwahori g)*
          (star (F.val x)*(cubicThetaPrimeRootWeylSection hp (cubicThetaPrimeRootSectionRestrict G)).val x)) := by ring
      _ = _ := by rw [hk,one_mul]
  rw [hfun,integral_const_mul] at he
  exact eq_zero_of_mul_eq_self_left hg he.symm

end CubicFirstMoment

end

end OAI
