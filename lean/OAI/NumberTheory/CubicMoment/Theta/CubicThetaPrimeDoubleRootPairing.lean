import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeDoubleRootDomain

namespace OAI

/-! Literal Hermitian integral transport on the intermediate root cover. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaPrimeDoubleRoot_pair_invariant {p : Eisenstein} (_hp : primaryPrime p)
    (F G : cubicThetaPrimeDoubleRootSections p) (g : cubicThetaPrimeDoubleRootSubgroup p)
    (z : CubicThetaPoint) :
    star (F.val (g • z))*G.val (g • z)=star (F.val z)*G.val z := by
  change star (F.val (g.val • z))*G.val (g.val • z)=_
  rw [F.property,G.property,star_mul]
  have hk : star (cubicThetaKubotaValue g.val)*cubicThetaKubotaValue g.val=1 := by
    rw [mul_comm,Complex.star_def,Complex.mul_conj',cubicThetaKubotaValue_norm]
    norm_num
  calc
    _ = (star (cubicThetaKubotaValue g.val)*cubicThetaKubotaValue g.val)*
      (star (F.val z)*G.val z) := by ring
    _ = _ := by rw [hk,one_mul]

lemma cubicThetaPrimeDoubleRoot_pair_translation {p : Eisenstein} (hp : primaryPrime p)
    (x : Eisenstein) (F G : cubicThetaPrimeDoubleRootSections p) :
    (∫ z in cubicThetaPrimeDoubleRootDomain hp,
      star (F.val (cubicThetaPrimeDoubleRootElement hp x • z))*
        G.val (cubicThetaPrimeDoubleRootElement hp x • z) ∂cubicThetaPointMeasure)=
      ∫ z in cubicThetaPrimeDoubleRootDomain hp,star (F.val z)*G.val z ∂cubicThetaPointMeasure := by
  have he := (cubicThetaPrimeDoubleRootDomain_fundamental hp).setIntegral_eq
    (f:=fun z => star (F.val z)*G.val z) (cubicThetaPrimeDoubleRootImage_fundamental hp x)
    (cubicThetaPrimeDoubleRoot_pair_invariant hp F G)
  have hm := (measurePreserving_smul (cubicThetaPrimeDoubleRootElement hp x)
    cubicThetaPointMeasure).setIntegral_image_emb
    (measurableEmbedding_const_smul (cubicThetaPrimeDoubleRootElement hp x))
    (fun z => star (F.val z)*G.val z) (cubicThetaPrimeDoubleRootDomain hp)
  exact (he.trans hm).symm

lemma cubicThetaPrimeDoubleRoot_pair_weyl {p : Eisenstein} (hp : primaryPrime p)
    (F G : cubicThetaPrimeDoubleRootSections p) :
    (∫ z in cubicThetaPrimeDoubleRootDomain hp,
      star (F.val (cubicThetaPrimeDoubleRootWeylElement hp • z))*
        G.val (cubicThetaPrimeDoubleRootWeylElement hp • z) ∂cubicThetaPointMeasure)=
      ∫ z in cubicThetaPrimeDoubleRootDomain hp,star (F.val z)*G.val z ∂cubicThetaPointMeasure := by
  have he := (cubicThetaPrimeDoubleRootDomain_fundamental hp).setIntegral_eq
    (f:=fun z => star (F.val z)*G.val z) (cubicThetaPrimeDoubleRootWeylImage_fundamental hp)
    (cubicThetaPrimeDoubleRoot_pair_invariant hp F G)
  have hm := (measurePreserving_smul (cubicThetaPrimeDoubleRootWeylElement hp)
    cubicThetaPointMeasure).setIntegral_image_emb
    (measurableEmbedding_const_smul (cubicThetaPrimeDoubleRootWeylElement hp))
    (fun z => star (F.val z)*G.val z) (cubicThetaPrimeDoubleRootDomain hp)
  exact (he.trans hm).symm

end CubicFirstMoment

end

end OAI
