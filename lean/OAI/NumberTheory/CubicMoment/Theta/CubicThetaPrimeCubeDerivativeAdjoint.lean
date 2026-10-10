import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPointC1Hecke

namespace OAI

/-! The derivative adjoint of the literal cubed-prime correspondence.
It uses the same inversion conjugate as the mass adjoint. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaPointC1_trace_atkin_section {p : Eisenstein} (hp : primaryPrime p)
    (G : CubicThetaSection)
    (hG : ContDiffOn ℝ 1 (cubicThetaSectionFunction G) {y : ℂ × ℝ | 0<y.2}) :
    cubicThetaPointC1Trace hp (cubicThetaPointC1Pullback (cubicThetaPrimeCubeAtkinMatrix hp)
      (cubicThetaSectionPointC1 G hG))=
    cubicThetaSectionPointC1 (cubicThetaPrimeCubeHecke hp (cubicThetaInversionSection G))
      (cubicThetaPrimeCubeHecke_c1 hp _ (cubicThetaInversionSection_c1 G hG)) := by
  rw [cubicThetaPointC1_atkin_dilation,←cubicThetaInversionPointC1]
  exact cubicThetaPointC1Hecke_section hp _ _

theorem cubicThetaPrimeCubeHecke_gradient_adjoint {p : Eisenstein} (hp : primaryPrime p)
    (F G : cubicThetaFiniteEnergySections) :
    (∫ x in cubicThetaFundamentalDomain,
      inner ℂ (cubicThetaSectionGradient G.val x)
        (cubicThetaSectionGradient (cubicThetaPrimeCubeHecke hp F.val) x) ∂cubicThetaPointMeasure)=
    ∫ x in cubicThetaFundamentalDomain,
      inner ℂ (cubicThetaSectionGradient (cubicThetaInversionSection
        (cubicThetaPrimeCubeHecke hp (cubicThetaInversionSection G.val))) x)
        (cubicThetaSectionGradient F.val x) ∂cubicThetaPointMeasure := by
  let F₀ := cubicThetaSectionPointC1 F.val F.property.1
  let G₀ := cubicThetaSectionPointC1 G.val G.property.1
  let S := cubicThetaFullComplex cubicThetaFullInversion
  let W := cubicThetaPrimeCubeAtkinMatrix hp
  let D := cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero)
  let X := cubicThetaPointC1Pullback W G₀
  have hSF : cubicThetaPointC1Pullback S F₀=
      cubicThetaSectionPointC1 (cubicThetaInversionFinite F).val (cubicThetaInversionFinite F).property.1 :=
    (cubicThetaInversionPointC1 F.val F.property.1).symm
  have hTrX := cubicThetaPointC1_trace_atkin_section hp G.val G.property.1
  have hFG (g : cubicThetaPrincipalGroup) (x : CubicThetaPoint) :
      F₀.val (g • x)=cubicThetaKubotaValue g*F₀.val x := F.val.property g x
  have hGG (g : cubicThetaPrincipalGroup) (x : CubicThetaPoint) :
      G₀.val (g • x)=cubicThetaKubotaValue g*G₀.val x := G.val.property g x
  have hSFG (g : cubicThetaPrincipalGroup) (x : CubicThetaPoint) :
      (cubicThetaPointC1Pullback S F₀).val (g • x)=
        cubicThetaKubotaValue g*(cubicThetaPointC1Pullback S F₀).val x :=
    cubicThetaPointC1Inversion_covariance F₀ hFG g x
  have hTX (g : cubicThetaPrincipalGroup) (x : CubicThetaPoint) :
      (cubicThetaPointC1Trace hp X).val (g • x)=
        cubicThetaKubotaValue g*(cubicThetaPointC1Trace hp X).val x := by
    change (cubicThetaPointC1Trace hp (cubicThetaPointC1Pullback W G₀)).val (g • x)=_
    rw [hTrX]
    exact (cubicThetaPrimeCubeHecke hp (cubicThetaInversionSection G.val)).property g x
  have hXint := cubicThetaPointC1_atkin_integrable hp G
  have hSFint : IntegrableOn (fun x => ‖cubicThetaPointC1Gradient x (cubicThetaPointC1Pullback S F₀)‖^2)
      (cubicThetaPrimeCubeCoverDomain p) cubicThetaPointMeasure := by
    rw [hSF]
    exact cubicThetaPointC1_section_cover_integrable hp (cubicThetaInversionFinite F)
  have he :
      (∫ x in cubicThetaFundamentalDomain,
        inner ℂ (cubicThetaPointC1Gradient x G₀)
          (cubicThetaPointC1Gradient x (cubicThetaPointC1Hecke hp F₀)) ∂cubicThetaPointMeasure)=
      ∫ x in cubicThetaFundamentalDomain,
        inner ℂ (cubicThetaPointC1Gradient x (cubicThetaPointC1Pullback S (cubicThetaPointC1Trace hp X)))
          (cubicThetaPointC1Gradient x F₀) ∂cubicThetaPointMeasure := by
    calc
      _ = ∫ x in cubicThetaPrimeCubeCoverDomain p,
          inner ℂ (cubicThetaPointC1Gradient x G₀)
            (cubicThetaPointC1Gradient x (cubicThetaPointC1Pullback D F₀)) ∂cubicThetaPointMeasure :=
        cubicThetaPointC1Trace_gradient_integral hp _ G₀
          (fun g => cubicThetaPointC1_covariance G₀ g (hGG g))
          (cubicThetaPointC1_dilation_integrable hp F) (cubicThetaPointC1_section_cover_integrable hp G)
      _ = ∫ x in cubicThetaPrimeCubeCoverDomain p,
          inner ℂ (cubicThetaPointC1Gradient x X)
            (cubicThetaPointC1Gradient x (cubicThetaPointC1Pullback S F₀)) ∂cubicThetaPointMeasure := by
        change (∫ x in cubicThetaPrimeCubeCoverDomain p,
          inner ℂ (cubicThetaPointC1Gradient x G₀) (cubicThetaPointC1Gradient x
            (cubicThetaPointC1Pullback (cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero)) F₀))
          ∂cubicThetaPointMeasure)=_
        rw [cubicThetaPointC1_dilation_atkin]
        exact cubicThetaPointC1Atkin_gradient_pairing hp _ G₀
          (fun g => hSFG g.val) (fun g => hGG g.val)
      _ = ∫ x in cubicThetaFundamentalDomain,
          inner ℂ (cubicThetaPointC1Gradient x (cubicThetaPointC1Trace hp X))
            (cubicThetaPointC1Gradient x (cubicThetaPointC1Pullback S F₀)) ∂cubicThetaPointMeasure :=
        (cubicThetaPointC1Trace_gradient_integral_left hp X _
          (fun g => cubicThetaPointC1_covariance _ g (hSFG g)) hXint hSFint).symm
      _ = _ := cubicThetaPointC1Inversion_gradient_pairing F₀ _ hFG hTX
  dsimp [F₀,G₀,X] at he
  rw [cubicThetaPointC1Hecke_section,hTrX,←cubicThetaInversionPointC1] at he
  simpa only [cubicThetaSectionPointC1_gradient] using he

end CubicFirstMoment

end

end OAI
