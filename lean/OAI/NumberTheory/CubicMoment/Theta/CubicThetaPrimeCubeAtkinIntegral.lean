import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeCoverDomain

namespace OAI

/-! The cubed-prime Atkin involution preserves the actual integral norm
on its finite arithmetic covering, before passing to a completion. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

instance cubicThetaPrimeCubePointMeasure_invariant (p : Eisenstein) :
    SMulInvariantMeasure (cubicThetaPrimeIwahori (p^3)) CubicThetaPoint cubicThetaPointMeasure where
  measure_preimage_smul g _S hS :=
    SMulInvariantMeasure.measure_preimage_smul (g.val : cubicThetaPrincipalGroup) hS

def cubicThetaPrimeCubeAtkinEquiv {p : Eisenstein} (hp : primaryPrime p) :
    cubicThetaPrimeIwahori (p^3) ≃ cubicThetaPrimeIwahori (p^3) :=
  (cubicThetaPrimeCubeAtkinConjugate_involutive hp).toPerm

lemma cubicThetaPrimeCubeAtkinPoint_intertwines {p : Eisenstein} (hp : primaryPrime p)
    (g : cubicThetaPrimeIwahori (p^3)) (x : CubicThetaPoint) :
    cubicThetaPrimeCubeAtkinMatrix hp • (g • x)=
      cubicThetaPrimeCubeAtkinEquiv hp g • (cubicThetaPrimeCubeAtkinMatrix hp • x) := by
  change cubicThetaPrimeCubeAtkinMatrix hp • (cubicThetaPrincipalComplex g.val • x)=
    cubicThetaPrincipalComplex (cubicThetaPrimeCubeAtkinConjugate hp g).val •
      (cubicThetaPrimeCubeAtkinMatrix hp • x)
  rw [←mul_smul,←mul_smul,cubicThetaPrimeCubeAtkinMatrix_intertwines]

lemma cubicThetaPrimeCubeAtkinImage_fundamental {p : Eisenstein} (hp : primaryPrime p) :
    IsFundamentalDomain (cubicThetaPrimeIwahori (p^3))
      ((fun x : CubicThetaPoint => cubicThetaPrimeCubeAtkinMatrix hp • x) ''
        cubicThetaPrimeCubeCoverDomain p) cubicThetaPointMeasure := by
  apply (cubicThetaPrimeCubeCoverDomain_isFundamentalDomain hp cubicThetaPointMeasure).image_of_equiv
    (Homeomorph.smul (cubicThetaPrimeCubeAtkinMatrix hp)).toEquiv
    (measurePreserving_smul (cubicThetaPrimeCubeAtkinMatrix hp)⁻¹
      cubicThetaPointMeasure).quasiMeasurePreserving
    (cubicThetaPrimeCubeAtkinEquiv hp)
  intro g x
  change cubicThetaPrimeCubeAtkinMatrix hp • (cubicThetaPrimeCubeAtkinEquiv hp g • x)=
    g • (cubicThetaPrimeCubeAtkinMatrix hp • x)
  rw [cubicThetaPrimeCubeAtkinPoint_intertwines]
  exact congrArg (fun h : cubicThetaPrimeIwahori (p^3) =>
    h • (cubicThetaPrimeCubeAtkinMatrix hp • x))
      (cubicThetaPrimeCubeAtkinConjugate_involutive hp g)

lemma cubicThetaPrimeCubeSection_norm_invariant (p : Eisenstein)
    (F : cubicThetaPrimeCubeSections p) (g : cubicThetaPrimeIwahori (p^3)) (x : CubicThetaPoint) :
    ‖F.val (g • x)‖^2=‖F.val x‖^2 := by
  change ‖F.val (g.val • x)‖^2=‖F.val x‖^2
  rw [F.property,norm_mul,cubicThetaKubotaValue_norm,one_mul]

theorem cubicThetaPrimeCubeAtkin_integral_norm {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPrimeCubeSections p) :
    (∫ x in cubicThetaPrimeCubeCoverDomain p,
      ‖F.val (cubicThetaPrimeCubeAtkinMatrix hp • x)‖^2 ∂cubicThetaPointMeasure)=
    ∫ x in cubicThetaPrimeCubeCoverDomain p,‖F.val x‖^2 ∂cubicThetaPointMeasure := by
  let f : CubicThetaPoint → ℝ := fun x => ‖F.val x‖^2
  have hinv (g : cubicThetaPrimeIwahori (p^3)) (x : CubicThetaPoint) : f (g • x)=f x :=
    cubicThetaPrimeCubeSection_norm_invariant p F g x
  have he := (cubicThetaPrimeCubeCoverDomain_isFundamentalDomain hp cubicThetaPointMeasure).setIntegral_eq
    (cubicThetaPrimeCubeAtkinImage_fundamental hp) hinv
  have hc := (measurePreserving_smul (cubicThetaPrimeCubeAtkinMatrix hp) cubicThetaPointMeasure).setIntegral_image_emb
    (measurableEmbedding_const_smul (cubicThetaPrimeCubeAtkinMatrix hp)) f (cubicThetaPrimeCubeCoverDomain p)
  exact (he.trans hc).symm

end CubicFirstMoment

end

end OAI
