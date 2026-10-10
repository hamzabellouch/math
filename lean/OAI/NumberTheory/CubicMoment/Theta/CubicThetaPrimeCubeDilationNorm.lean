import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeTraceNorm
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeSectionAtkin

namespace OAI

/-! The cubed-prime dilation has exactly the finite-cover mass factor.
Consequently the literal Hecke operator is bounded on the original L2
sections, with no analytic assumption. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaPrimeCubeAtkin_integrable {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPrimeCubeSections p)
    (hF : IntegrableOn (fun x => ‖F.val x‖^2) (cubicThetaPrimeCubeCoverDomain p) cubicThetaPointMeasure) :
    IntegrableOn (fun x => ‖(cubicThetaPrimeCubeAtkinSection hp F).val x‖^2)
      (cubicThetaPrimeCubeCoverDomain p) cubicThetaPointMeasure := by
  have hi := (cubicThetaPrimeCubeCoverDomain_isFundamentalDomain hp cubicThetaPointMeasure).integrableOn_iff
    (cubicThetaPrimeCubeAtkinImage_fundamental hp) (f:=fun x : CubicThetaPoint => ‖F.val x‖^2)
      (cubicThetaPrimeCubeSection_norm_invariant p F)
  have hImage := hi.mp hF
  exact ((measurePreserving_smul (cubicThetaPrimeCubeAtkinMatrix hp) cubicThetaPointMeasure).integrableOn_image
    (measurableEmbedding_const_smul (cubicThetaPrimeCubeAtkinMatrix hp))).mp hImage

lemma cubicThetaOriginal_norm_invariant (F : CubicThetaSection)
    (g : cubicThetaPrincipalGroup) (x : CubicThetaPoint) :
    ‖F.val (g • x)‖^2=‖F.val x‖^2 := by
  rw [F.property,norm_mul,cubicThetaKubotaValue_norm,one_mul]

lemma cubicThetaInversion_domain_integrable (F : CubicThetaSection)
    (hF : IntegrableOn (fun x => ‖F.val x‖^2) cubicThetaFundamentalDomain cubicThetaPointMeasure) :
    IntegrableOn (fun x => ‖(cubicThetaInversionSection F).val x‖^2)
      cubicThetaFundamentalDomain cubicThetaPointMeasure := by
  have hImage := ((cubicThetaFundamentalDomain_isFundamentalDomain cubicThetaPointMeasure).integrableOn_iff
    (cubicThetaIntegralImage_fundamental cubicThetaFullInversion) (cubicThetaOriginal_norm_invariant F)).mp hF
  exact ((measurePreserving_smul cubicThetaFullInversion cubicThetaPointMeasure).integrableOn_image
    (measurableEmbedding_const_smul cubicThetaFullInversion)).mp hImage

lemma cubicThetaInversion_domain_integral (F : CubicThetaSection) :
    (∫ x in cubicThetaFundamentalDomain,‖(cubicThetaInversionSection F).val x‖^2 ∂cubicThetaPointMeasure)=
    ∫ x in cubicThetaFundamentalDomain,‖F.val x‖^2 ∂cubicThetaPointMeasure := by
  have he := (cubicThetaFundamentalDomain_isFundamentalDomain cubicThetaPointMeasure).setIntegral_eq
    (cubicThetaIntegralImage_fundamental cubicThetaFullInversion) (f:=fun x : CubicThetaPoint => ‖F.val x‖^2)
      (cubicThetaOriginal_norm_invariant F)
  have hc := (measurePreserving_smul cubicThetaFullInversion cubicThetaPointMeasure).setIntegral_image_emb
    (measurableEmbedding_const_smul cubicThetaFullInversion) (fun x => ‖F.val x‖^2) cubicThetaFundamentalDomain
  exact (he.trans hc).symm

lemma cubicThetaPrimeCubeDilation_integrable {p : Eisenstein} (hp : primaryPrime p)
    (F : CubicThetaSection)
    (hF : IntegrableOn (fun x => ‖F.val x‖^2) cubicThetaFundamentalDomain cubicThetaPointMeasure) :
    IntegrableOn (fun x => ‖(cubicThetaPrimeCubeDilationSection hp F).val x‖^2)
      (cubicThetaPrimeCubeCoverDomain p) cubicThetaPointMeasure := by
  rw [cubicThetaPrimeCubeDilation_eq_atkin]
  apply cubicThetaPrimeCubeAtkin_integrable hp
  exact cubicThetaPrimeCubeInvariant_integrable hp (cubicThetaInversion_domain_integrable F hF)
    (cubicThetaOriginal_norm_invariant (cubicThetaInversionSection F))

theorem cubicThetaPrimeCubeDilation_integral_norm {p : Eisenstein} (hp : primaryPrime p)
    (F : CubicThetaSection)
    (hF : IntegrableOn (fun x => ‖F.val x‖^2) cubicThetaFundamentalDomain cubicThetaPointMeasure) :
    (∫ x in cubicThetaPrimeCubeCoverDomain p,‖(cubicThetaPrimeCubeDilationSection hp F).val x‖^2
      ∂cubicThetaPointMeasure)=((cubicThetaPrimeIwahori (p^3)).index:ℝ)*
        ∫ x in cubicThetaFundamentalDomain,‖F.val x‖^2 ∂cubicThetaPointMeasure := by
  rw [cubicThetaPrimeCubeDilation_eq_atkin]
  change (∫ x in cubicThetaPrimeCubeCoverDomain p,
    ‖(cubicThetaPrimeCubeSectionRestrict (p:=p) (cubicThetaInversionSection F)).val
      (cubicThetaPrimeCubeAtkinMatrix hp • x)‖^2 ∂cubicThetaPointMeasure)=_
  rw [cubicThetaPrimeCubeAtkin_integral_norm hp]
  change (∫ x in cubicThetaPrimeCubeCoverDomain p,‖(cubicThetaInversionSection F).val x‖^2
    ∂cubicThetaPointMeasure)=_
  rw [cubicThetaPrimeCubeInvariant_integral hp (cubicThetaInversion_domain_integrable F hF)
    (cubicThetaOriginal_norm_invariant (cubicThetaInversionSection F)),
    cubicThetaInversion_domain_integral,cubicThetaPrimeCubeIwahori_index hp]
  norm_cast

theorem cubicThetaPrimeCubeHecke_integral_bound {p : Eisenstein} (hp : primaryPrime p)
    (F : CubicThetaSection)
    (hF : IntegrableOn (fun x => ‖F.val x‖^2) cubicThetaFundamentalDomain cubicThetaPointMeasure) :
    (∫ x in cubicThetaFundamentalDomain,‖(cubicThetaPrimeCubeHecke hp F).val x‖^2
      ∂cubicThetaPointMeasure)≤((cubicThetaPrimeIwahori (p^3)).index:ℝ)^2*
        ∫ x in cubicThetaFundamentalDomain,‖F.val x‖^2 ∂cubicThetaPointMeasure := by
  have he := cubicThetaPrimeCubeTrace_mass_integral_le hp (cubicThetaPrimeCubeDilationSection hp F)
    (cubicThetaPrimeCubeDilation_integrable hp F hF)
  rw [cubicThetaPrimeCubeDilation_integral_norm hp F hF] at he
  simpa only [cubicThetaPrimeCubeHecke,pow_two,mul_assoc] using he

end CubicFirstMoment

end

end OAI
