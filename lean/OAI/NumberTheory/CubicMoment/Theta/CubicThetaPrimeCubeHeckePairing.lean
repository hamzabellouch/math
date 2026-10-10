import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeTracePairing

namespace OAI

/-! The mass adjoint of the literal cubed-prime correspondence. All
integrals use the constructed arithmetic domains. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaComplexPair_flip (f g : CubicThetaPoint → ℂ) (S : Set CubicThetaPoint) :
    star (∫ x in S,star (f x)*g x ∂cubicThetaPointMeasure)=
      ∫ x in S,star (g x)*f x ∂cubicThetaPointMeasure := by
  have he := (integral_conj (f:=fun x => star (f x)*g x)
    (μ:=cubicThetaPointMeasure.restrict S)).symm
  change star (∫ x in S,star (f x)*g x ∂cubicThetaPointMeasure)=
    ∫ x in S,star (star (f x)*g x) ∂cubicThetaPointMeasure at he
  rw [he]
  apply integral_congr_ae
  filter_upwards with x
  rw [star_mul,star_star,mul_comm]

lemma cubicThetaPrimeCubeTrace_pairing_left {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPrimeCubeSections p) (G : CubicThetaSection)
    (hF : IntegrableOn (fun x => ‖F.val x‖^2) (cubicThetaPrimeCubeCoverDomain p) cubicThetaPointMeasure)
    (hG : IntegrableOn (fun x => ‖G.val x‖^2) cubicThetaFundamentalDomain cubicThetaPointMeasure) :
    (∫ x in cubicThetaFundamentalDomain,
      star ((cubicThetaPrimeCubeTraceSection hp F).val x)*G.val x ∂cubicThetaPointMeasure)=
    ∫ x in cubicThetaPrimeCubeCoverDomain p,star (F.val x)*G.val x ∂cubicThetaPointMeasure := by
  have he := congrArg star (cubicThetaPrimeCubeTrace_pairing hp F G hF hG)
  rwa [cubicThetaComplexPair_flip,cubicThetaComplexPair_flip] at he

lemma cubicThetaComplexInversion_integral {f : CubicThetaPoint → ℂ}
    (hi : ∀ (g : cubicThetaPrincipalGroup) x,f (g • x)=f x) :
    (∫ x in cubicThetaFundamentalDomain,f (cubicThetaFullInversion • x) ∂cubicThetaPointMeasure)=
      ∫ x in cubicThetaFundamentalDomain,f x ∂cubicThetaPointMeasure := by
  have he := (cubicThetaFundamentalDomain_isFundamentalDomain cubicThetaPointMeasure).setIntegral_eq
    (cubicThetaIntegralImage_fundamental cubicThetaFullInversion) hi
  have hc := (measurePreserving_smul cubicThetaFullInversion cubicThetaPointMeasure).setIntegral_image_emb
    (measurableEmbedding_const_smul cubicThetaFullInversion) f cubicThetaFundamentalDomain
  exact (he.trans hc).symm

lemma cubicThetaInversion_pair_domain (F G : CubicThetaSection) :
    (∫ x in cubicThetaFundamentalDomain,
      star (G.val x)*(cubicThetaInversionSection F).val x ∂cubicThetaPointMeasure)=
    ∫ x in cubicThetaFundamentalDomain,
      star ((cubicThetaInversionSection G).val x)*F.val x ∂cubicThetaPointMeasure := by
  have hi (g : cubicThetaPrincipalGroup) (x : CubicThetaPoint) :
      star ((cubicThetaInversionSection G).val (g • x))*F.val (g • x)=
        star ((cubicThetaInversionSection G).val x)*F.val x := by
    simpa only [RCLike.inner_apply',Complex.star_def] using
      cubicThetaSectionPairing_invariant (cubicThetaInversionSection G) F g x
  have he := cubicThetaComplexInversion_integral
    (f:=fun x => star ((cubicThetaInversionSection G).val x)*F.val x) hi
  change (∫ x in cubicThetaFundamentalDomain,
    star (G.val (cubicThetaFullInversion • (cubicThetaFullInversion • x)))*
      F.val (cubicThetaFullInversion • x) ∂cubicThetaPointMeasure)=
    ∫ x in cubicThetaFundamentalDomain,star (G.val (cubicThetaFullInversion • x))*
      F.val x ∂cubicThetaPointMeasure at he
  change (∫ x in cubicThetaFundamentalDomain,
    star (G.val x)*F.val (cubicThetaFullInversion • x) ∂cubicThetaPointMeasure)=
    ∫ x in cubicThetaFundamentalDomain,star (G.val (cubicThetaFullInversion • x))*
      F.val x ∂cubicThetaPointMeasure
  simpa only [cubicThetaFullInversion_involutive] using he

lemma cubicThetaPrimeCubeAtkin_restrict_eq {p : Eisenstein} (hp : primaryPrime p)
    (G : CubicThetaSection) :
    cubicThetaPrimeCubeAtkinSection hp (cubicThetaPrimeCubeSectionRestrict G)=
      cubicThetaPrimeCubeDilationSection hp (cubicThetaInversionSection G) := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro x
  change G.val (cubicThetaPrimeCubeAtkinMatrix hp • x)=
    G.val (cubicThetaFullInversion • (cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero) • x))
  exact congrArg G.val (mul_smul (β:=CubicThetaPoint) _ _ x)

theorem cubicThetaPrimeCubeHecke_mass_adjoint {p : Eisenstein} (hp : primaryPrime p)
    (F G : CubicThetaSection)
    (hF : IntegrableOn (fun x => ‖F.val x‖^2) cubicThetaFundamentalDomain cubicThetaPointMeasure)
    (hG : IntegrableOn (fun x => ‖G.val x‖^2) cubicThetaFundamentalDomain cubicThetaPointMeasure) :
    (∫ x in cubicThetaFundamentalDomain,
      star (G.val x)*(cubicThetaPrimeCubeHecke hp F).val x ∂cubicThetaPointMeasure)=
    ∫ x in cubicThetaFundamentalDomain,
      star ((cubicThetaInversionSection (cubicThetaPrimeCubeHecke hp
        (cubicThetaInversionSection G))).val x)*F.val x ∂cubicThetaPointMeasure := by
  let X := cubicThetaPrimeCubeAtkinSection hp (cubicThetaPrimeCubeSectionRestrict G)
  have hX : IntegrableOn (fun x => ‖X.val x‖^2)
      (cubicThetaPrimeCubeCoverDomain p) cubicThetaPointMeasure :=
    cubicThetaPrimeCubeAtkin_integrable hp _
      (cubicThetaPrimeCubeInvariant_integrable hp hG (cubicThetaOriginal_norm_invariant G))
  calc
    _ = ∫ x in cubicThetaPrimeCubeCoverDomain p,
        star (G.val x)*(cubicThetaPrimeCubeDilationSection hp F).val x ∂cubicThetaPointMeasure :=
      cubicThetaPrimeCubeTrace_pairing hp _ G (cubicThetaPrimeCubeDilation_integrable hp F hF) hG
    _ = ∫ x in cubicThetaPrimeCubeCoverDomain p,
        star (X.val x)*(cubicThetaInversionSection F).val x ∂cubicThetaPointMeasure := by
      rw [cubicThetaPrimeCubeDilation_eq_atkin]
      exact cubicThetaPrimeCubeAtkin_pairing hp
        (cubicThetaPrimeCubeSectionRestrict (cubicThetaInversionSection F))
        (cubicThetaPrimeCubeSectionRestrict G)
    _ = ∫ x in cubicThetaFundamentalDomain,
        star ((cubicThetaPrimeCubeTraceSection hp X).val x)*
          (cubicThetaInversionSection F).val x ∂cubicThetaPointMeasure :=
      (cubicThetaPrimeCubeTrace_pairing_left hp X (cubicThetaInversionSection F) hX
        (cubicThetaInversion_domain_integrable F hF)).symm
    _ = ∫ x in cubicThetaFundamentalDomain,
        star ((cubicThetaInversionSection (cubicThetaPrimeCubeTraceSection hp X)).val x)*
          F.val x ∂cubicThetaPointMeasure :=
      cubicThetaInversion_pair_domain F (cubicThetaPrimeCubeTraceSection hp X)
    _ = _ := by rw [show X=cubicThetaPrimeCubeDilationSection hp (cubicThetaInversionSection G) from
      cubicThetaPrimeCubeAtkin_restrict_eq hp G]; rfl

end CubicFirstMoment

end

end OAI
