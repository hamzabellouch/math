import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeComplexIntegration

namespace OAI

/-! The cubed-prime Atkin involution is self-adjoint for the actual
cover integral. No spectral or residue identity is assumed. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaPrimeCubeAtkinMatrix_eq {p : Eisenstein} (hp : primaryPrime p) :
    cubicThetaPrimeCubeAtkinMatrix hp=
      cubicThetaInversionMatrix (cubicThetaPrimeSquareRoot (p^3))
        (cubicThetaPrimeSquareRoot_ne_zero (pow_ne_zero 3 hp.2.ne_zero)) := by
  rw [cubicThetaPrimeCubeAtkinMatrix,cubicThetaFullInversion_complex]
  apply Subtype.ext
  change (cubicThetaInversionMatrix 1 one_ne_zero : Matrix (Fin 2) (Fin 2) ℂ)*
      (cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero) : Matrix (Fin 2) (Fin 2) ℂ)=_
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [cubicThetaInversionMatrix,cubicThetaPrimeDilation,Matrix.mul_apply,Fin.sum_univ_two]

lemma cubicThetaPrimeCubeAtkinPoint_involutive {p : Eisenstein} (hp : primaryPrime p)
    (x : CubicThetaPoint) :
    cubicThetaPrimeCubeAtkinMatrix hp • (cubicThetaPrimeCubeAtkinMatrix hp • x)=x := by
  apply Subtype.ext
  change cubicThetaMobius (cubicThetaPrimeCubeAtkinMatrix hp)
    (cubicThetaMobius (cubicThetaPrimeCubeAtkinMatrix hp) x.val)=x.val
  rw [cubicThetaPrimeCubeAtkinMatrix_eq,
    cubicThetaMobius_inversion _ (cubicThetaMobius_height_pos _ x.property),
    cubicThetaMobius_inversion _ x.property]
  exact cubicThetaInversion_involutive (cubicThetaPrimeSquareRoot_ne_zero (pow_ne_zero 3 hp.2.ne_zero)) x.property

lemma cubicThetaPrimeCubePair_invariant {p : Eisenstein}
    (F G : cubicThetaPrimeCubeSections p) (g : cubicThetaPrimeIwahori (p^3))
    (x : CubicThetaPoint) :
    star (F.val (g • x))*G.val (g • x)=star (F.val x)*G.val x := by
  change star (F.val (g.val • x))*G.val (g.val • x)=_
  rw [F.property,G.property,star_mul]
  have hk : star (cubicThetaKubotaValue g.val)*cubicThetaKubotaValue g.val=1 := by
    rw [mul_comm,Complex.star_def,Complex.mul_conj',cubicThetaKubotaValue_norm]
    norm_num
  calc
    _ = (star (cubicThetaKubotaValue g.val)*cubicThetaKubotaValue g.val)*
      (star (F.val x)*G.val x) := by ring
    _ = _ := by rw [hk,one_mul]

lemma cubicThetaPrimeCubeComplexAtkin_integral {p : Eisenstein} (hp : primaryPrime p)
    {f : CubicThetaPoint → ℂ}
    (hi : ∀ (g : cubicThetaPrimeIwahori (p^3)) x,f (g • x)=f x) :
    (∫ x in cubicThetaPrimeCubeCoverDomain p,f (cubicThetaPrimeCubeAtkinMatrix hp • x)
      ∂cubicThetaPointMeasure)=∫ x in cubicThetaPrimeCubeCoverDomain p,f x ∂cubicThetaPointMeasure := by
  have he := (cubicThetaPrimeCubeCoverDomain_isFundamentalDomain hp cubicThetaPointMeasure).setIntegral_eq
    (cubicThetaPrimeCubeAtkinImage_fundamental hp) hi
  have hc := (measurePreserving_smul (cubicThetaPrimeCubeAtkinMatrix hp) cubicThetaPointMeasure).setIntegral_image_emb
    (measurableEmbedding_const_smul (cubicThetaPrimeCubeAtkinMatrix hp)) f (cubicThetaPrimeCubeCoverDomain p)
  exact (he.trans hc).symm

theorem cubicThetaPrimeCubeAtkin_pairing {p : Eisenstein} (hp : primaryPrime p)
    (F G : cubicThetaPrimeCubeSections p) :
    (∫ x in cubicThetaPrimeCubeCoverDomain p,
      star (G.val x)*F.val (cubicThetaPrimeCubeAtkinMatrix hp • x) ∂cubicThetaPointMeasure)=
    ∫ x in cubicThetaPrimeCubeCoverDomain p,
      star (G.val (cubicThetaPrimeCubeAtkinMatrix hp • x))*F.val x ∂cubicThetaPointMeasure := by
  have he := cubicThetaPrimeCubeComplexAtkin_integral hp
    (f:=fun x => star ((cubicThetaPrimeCubeAtkinSection hp G).val x)*F.val x)
    (cubicThetaPrimeCubePair_invariant (cubicThetaPrimeCubeAtkinSection hp G) F)
  change (∫ x in cubicThetaPrimeCubeCoverDomain p,
    star (G.val (cubicThetaPrimeCubeAtkinMatrix hp • (cubicThetaPrimeCubeAtkinMatrix hp • x)))*
      F.val (cubicThetaPrimeCubeAtkinMatrix hp • x) ∂cubicThetaPointMeasure)=
    ∫ x in cubicThetaPrimeCubeCoverDomain p,
      star (G.val (cubicThetaPrimeCubeAtkinMatrix hp • x))*F.val x ∂cubicThetaPointMeasure at he
  simpa only [cubicThetaPrimeCubeAtkinPoint_involutive] using he

end CubicFirstMoment

end

end OAI
