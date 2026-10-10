import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeSheetIntegral
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeSectionAtkin

namespace OAI

/-! Scalar integration for the actual dilation. This is used for the
invariant derivative energy as well as the mass density. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaPrimeCubeDilation_inversion_atkin {p : Eisenstein} (hp : primaryPrime p)
    (x : CubicThetaPoint) :
    cubicThetaFullInversion • (cubicThetaPrimeCubeAtkinMatrix hp • x)=
      cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero) • x := by
  rw [cubicThetaPrimeCubeAtkinMatrix,mul_smul]
  change cubicThetaFullInversion • (cubicThetaFullInversion •
    (cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero) • x))=_
  rw [cubicThetaFullInversion_involutive]

lemma cubicThetaPrimeCubeScalarAtkin_integrable {p : Eisenstein} (hp : primaryPrime p)
    {f : CubicThetaPoint → ℝ}
    (hf : IntegrableOn f (cubicThetaPrimeCubeCoverDomain p) cubicThetaPointMeasure)
    (hi : ∀ (g : cubicThetaPrimeIwahori (p^3)) x,f (g • x)=f x) :
    IntegrableOn (fun x => f (cubicThetaPrimeCubeAtkinMatrix hp • x))
      (cubicThetaPrimeCubeCoverDomain p) cubicThetaPointMeasure := by
  have hImage := ((cubicThetaPrimeCubeCoverDomain_isFundamentalDomain hp cubicThetaPointMeasure).integrableOn_iff
    (cubicThetaPrimeCubeAtkinImage_fundamental hp) hi).mp hf
  exact ((measurePreserving_smul (cubicThetaPrimeCubeAtkinMatrix hp) cubicThetaPointMeasure).integrableOn_image
    (measurableEmbedding_const_smul (cubicThetaPrimeCubeAtkinMatrix hp))).mp hImage

lemma cubicThetaPrimeCubeScalarAtkin_integral {p : Eisenstein} (hp : primaryPrime p)
    {f : CubicThetaPoint → ℝ}
    (hi : ∀ (g : cubicThetaPrimeIwahori (p^3)) x,f (g • x)=f x) :
    (∫ x in cubicThetaPrimeCubeCoverDomain p,f (cubicThetaPrimeCubeAtkinMatrix hp • x)
      ∂cubicThetaPointMeasure)=∫ x in cubicThetaPrimeCubeCoverDomain p,f x ∂cubicThetaPointMeasure := by
  have he := (cubicThetaPrimeCubeCoverDomain_isFundamentalDomain hp cubicThetaPointMeasure).setIntegral_eq
    (cubicThetaPrimeCubeAtkinImage_fundamental hp) hi
  have hc := (measurePreserving_smul (cubicThetaPrimeCubeAtkinMatrix hp) cubicThetaPointMeasure).setIntegral_image_emb
    (measurableEmbedding_const_smul (cubicThetaPrimeCubeAtkinMatrix hp)) f (cubicThetaPrimeCubeCoverDomain p)
  exact (he.trans hc).symm

lemma cubicThetaScalarInversion_invariant {f : CubicThetaPoint → ℝ}
    (hi : ∀ (g : cubicThetaPrincipalGroup) x,f (g • x)=f x)
    (g : cubicThetaPrincipalGroup) (x : CubicThetaPoint) :
    f (cubicThetaFullInversion • (g • x))=f (cubicThetaFullInversion • x) := by
  rw [cubicThetaInversion_intertwine,hi]

lemma cubicThetaScalarInversion_integrable {f : CubicThetaPoint → ℝ}
    (hf : IntegrableOn f cubicThetaFundamentalDomain cubicThetaPointMeasure)
    (hi : ∀ (g : cubicThetaPrincipalGroup) x,f (g • x)=f x) :
    IntegrableOn (fun x => f (cubicThetaFullInversion • x)) cubicThetaFundamentalDomain cubicThetaPointMeasure := by
  have hImage := ((cubicThetaFundamentalDomain_isFundamentalDomain cubicThetaPointMeasure).integrableOn_iff
    (cubicThetaIntegralImage_fundamental cubicThetaFullInversion) hi).mp hf
  exact ((measurePreserving_smul cubicThetaFullInversion cubicThetaPointMeasure).integrableOn_image
    (measurableEmbedding_const_smul cubicThetaFullInversion)).mp hImage

lemma cubicThetaScalarInversion_integral {f : CubicThetaPoint → ℝ}
    (hi : ∀ (g : cubicThetaPrincipalGroup) x,f (g • x)=f x) :
    (∫ x in cubicThetaFundamentalDomain,f (cubicThetaFullInversion • x) ∂cubicThetaPointMeasure)=
      ∫ x in cubicThetaFundamentalDomain,f x ∂cubicThetaPointMeasure := by
  have he := (cubicThetaFundamentalDomain_isFundamentalDomain cubicThetaPointMeasure).setIntegral_eq
    (cubicThetaIntegralImage_fundamental cubicThetaFullInversion) hi
  have hc := (measurePreserving_smul cubicThetaFullInversion cubicThetaPointMeasure).setIntegral_image_emb
    (measurableEmbedding_const_smul cubicThetaFullInversion) f cubicThetaFundamentalDomain
  exact (he.trans hc).symm

theorem cubicThetaPrimeCubeScalarDilation_integrable {p : Eisenstein} (hp : primaryPrime p)
    {f : CubicThetaPoint → ℝ}
    (hf : IntegrableOn f cubicThetaFundamentalDomain cubicThetaPointMeasure)
    (hi : ∀ (g : cubicThetaPrincipalGroup) x,f (g • x)=f x) :
    IntegrableOn (fun x => f (cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero) • x))
      (cubicThetaPrimeCubeCoverDomain p) cubicThetaPointMeasure := by
  have hI := cubicThetaPrimeCubeInvariant_integrable hp (cubicThetaScalarInversion_integrable hf hi)
    (cubicThetaScalarInversion_invariant hi)
  have hA := cubicThetaPrimeCubeScalarAtkin_integrable hp hI
    (fun g x => cubicThetaScalarInversion_invariant hi g.val x)
  simpa only [cubicThetaPrimeCubeDilation_inversion_atkin] using hA

theorem cubicThetaPrimeCubeScalarDilation_integral {p : Eisenstein} (hp : primaryPrime p)
    {f : CubicThetaPoint → ℝ}
    (hf : IntegrableOn f cubicThetaFundamentalDomain cubicThetaPointMeasure)
    (hi : ∀ (g : cubicThetaPrincipalGroup) x,f (g • x)=f x) :
    (∫ x in cubicThetaPrimeCubeCoverDomain p,f (cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero) • x)
      ∂cubicThetaPointMeasure)=((cubicThetaPrimeIwahori (p^3)).index:ℝ)*
        ∫ x in cubicThetaFundamentalDomain,f x ∂cubicThetaPointMeasure := by
  have hA := cubicThetaPrimeCubeScalarAtkin_integral hp
    (f:=fun x => f (cubicThetaFullInversion • x))
    (fun g x => cubicThetaScalarInversion_invariant hi g.val x)
  simp only [cubicThetaPrimeCubeDilation_inversion_atkin] at hA
  rw [hA,cubicThetaPrimeCubeInvariant_integral hp (cubicThetaScalarInversion_integrable hf hi)
    (cubicThetaScalarInversion_invariant hi),cubicThetaScalarInversion_integral hi,
    cubicThetaPrimeCubeIwahori_index hp]
  norm_cast

end CubicFirstMoment

end

end OAI
