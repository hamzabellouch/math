import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeRootDilationWeyl
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeRootIwahoriDomain
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeRootPairing
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeDiagonal

namespace OAI

/-! The original and once-dilated global subspaces are orthogonal in
the actual root-cover pairing, by their distinct cubic diagonal characters. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaPrimeRootDilationSection_iwahori {p : Eisenstein} (hp : primaryPrime p)
    (g : cubicThetaPrimeIwahori p) (F : CubicThetaSection) (x : CubicThetaPoint) :
    (cubicThetaPrimeRootDilationSection hp F).val (g.val • x)=
      star (cubicThetaPrimeIwahoriCharacter p hp g)*cubicThetaKubotaValue g.val*
        (cubicThetaPrimeRootDilationSection hp F).val x := by
  have hc : star (cubicThetaPrimeIwahoriCharacter p hp g)*
      cubicThetaPrimeIwahoriCharacter p hp g=1 := by
    rw [mul_comm,Complex.star_def,Complex.mul_conj',cubicThetaPrimeIwahoriCharacter_norm hp g]
    norm_num
  have hk : star (cubicThetaPrimeIwahoriCharacter p hp g)*cubicThetaKubotaValue g.val=
      cubicThetaKubotaValue (cubicThetaPrimeConjugate hp.1 g) := by
    rw [cubicThetaPrimeConjugate_kubota hp g,←mul_assoc,hc,one_mul]
  change F.val (cubicThetaPrimeDilation hp.2.ne_zero • (cubicThetaPrincipalComplex g.val • x))=_
  have hD := cubicThetaPrimeDilation_intertwines hp.1 g
  rw [←mul_smul,hD,mul_smul]
  change F.val (cubicThetaPrimeConjugate hp.1 g • (cubicThetaPrimeDilation hp.2.ne_zero • x))=_
  rw [F.property,←hk]
  rfl

lemma cubicThetaPrimeRootSectionPairing_unfold {p : Eisenstein} (hp : primaryPrime p)
    (F G : cubicThetaPrimeRootSections p) :
    (∫ q, cubicThetaPrimeRootSectionPairing hp F G q ∂cubicThetaPrimeRootCoverMeasure hp)=
      ∫ x in cubicThetaPrimeRootCoverDomain hp,star (F.val x)*G.val x ∂cubicThetaPointMeasure := by
  rw [cubicThetaPrimeRootCoverMeasure]
  exact integral_map_of_stronglyMeasurable
    (cubicThetaPrimeRootCoverMap_open hp).continuous.measurable
    (cubicThetaPrimeRootSectionPairing_continuous hp F G).stronglyMeasurable

theorem cubicThetaPrimeRootDilation_pair_integral_zero {p : Eisenstein} (hp : primaryPrime p)
    (F G : CubicThetaSection) :
    (∫ x in cubicThetaPrimeRootCoverDomain hp,star (F.val x)*
      (cubicThetaPrimeRootDilationSection hp G).val x ∂cubicThetaPointMeasure)=0 := by
  let f : CubicThetaPoint → ℂ := fun x => star (F.val x)*
    (cubicThetaPrimeRootDilationSection hp G).val x
  obtain ⟨g,hg⟩ := cubicThetaPrimeIwahoriCharacter_nontrivial hp
  have hs : star (cubicThetaPrimeIwahoriCharacter p hp g)≠1 := by
    intro he
    apply hg
    simpa only [star_star,star_one] using congrArg star he
  have hinv (h : cubicThetaPrimeRootCoverGroup hp) (x : CubicThetaPoint) : f (h • x)=f x := by
    change star (F.val (h.val • x))*
      (cubicThetaPrimeRootDilationSection hp G).val (h.val • x)=_
    have hD : (cubicThetaPrimeRootDilationSection hp G).val (h.val • x)=
        cubicThetaKubotaValue h.val*(cubicThetaPrimeRootDilationSection hp G).val x :=
      (cubicThetaPrimeRootDilationSection hp G).property h x
    rw [F.property,hD,star_mul]
    have hk : star (cubicThetaKubotaValue h.val)*cubicThetaKubotaValue h.val=1 := by
      rw [mul_comm,Complex.star_def,Complex.mul_conj',cubicThetaKubotaValue_norm]
      norm_num
    calc
      _ = (star (cubicThetaKubotaValue h.val)*cubicThetaKubotaValue h.val)*f x := by dsimp [f]; ring
      _ = f x := by rw [hk,one_mul]
  have hi := (cubicThetaPrimeRootCoverDomain_isFundamentalDomain hp cubicThetaPointMeasure).setIntegral_eq
    (cubicThetaPrimeRootIwahoriImage_fundamental hp g) hinv
  have hc := (measurePreserving_smul g.val cubicThetaPointMeasure).setIntegral_image_emb
    (measurableEmbedding_const_smul g.val) f (cubicThetaPrimeRootCoverDomain hp)
  have he : (∫ x in cubicThetaPrimeRootCoverDomain hp,f x ∂cubicThetaPointMeasure)=
      ∫ x in cubicThetaPrimeRootCoverDomain hp,f (g.val • x) ∂cubicThetaPointMeasure := hi.trans hc
  have hfun : (fun x => f (g.val • x))=fun x =>
      star (cubicThetaPrimeIwahoriCharacter p hp g)*f x := by
    funext x
    dsimp [f]
    rw [F.property,cubicThetaPrimeRootDilationSection_iwahori]
    change star (cubicThetaKubotaValue g.val*F.val x)*
      (star (cubicThetaPrimeIwahoriCharacter p hp g)*cubicThetaKubotaValue g.val*
        (cubicThetaPrimeRootDilationSection hp G).val x)=
      star (cubicThetaPrimeIwahoriCharacter p hp g)*
        (star (F.val x)*(cubicThetaPrimeRootDilationSection hp G).val x)
    rw [star_mul]
    have hk : star (cubicThetaKubotaValue g.val)*cubicThetaKubotaValue g.val=1 := by
      rw [mul_comm,Complex.star_def,Complex.mul_conj',cubicThetaKubotaValue_norm]
      norm_num
    calc
      _ = (star (cubicThetaKubotaValue g.val)*cubicThetaKubotaValue g.val)*
        (star (cubicThetaPrimeIwahoriCharacter p hp g)*(star (F.val x)*
          (cubicThetaPrimeRootDilationSection hp G).val x)) := by ring
      _ = _ := by rw [hk,one_mul]
  rw [hfun,integral_const_mul] at he
  exact eq_zero_of_mul_eq_self_left hs he.symm

theorem cubicThetaPrimeRootDilation_pairing_zero {p : Eisenstein} (hp : primaryPrime p)
    (F G : CubicThetaSection) :
    (∫ q, cubicThetaPrimeRootSectionPairing hp (cubicThetaPrimeRootSectionRestrict F)
      (cubicThetaPrimeRootDilationSection hp G) q ∂cubicThetaPrimeRootCoverMeasure hp)=0 := by
  rw [cubicThetaPrimeRootSectionPairing_unfold]
  exact cubicThetaPrimeRootDilation_pair_integral_zero hp F G

end CubicFirstMoment

end

end OAI
