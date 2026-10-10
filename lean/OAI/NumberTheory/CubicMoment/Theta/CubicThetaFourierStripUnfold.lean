import OAI.NumberTheory.CubicMoment.Theta.CubicThetaFourierStripSupport

namespace OAI

/-! Full arithmetic unfolding of the compact Fourier profile. The positive
cutoff can lie below the injective cusp, since the group sum is unfolded first. -/
noncomputable section
open Set MeasureTheory
open scoped CompactlySupported
namespace CubicFirstMoment

lemma cubicThetaFourierStripSeed_group_sum (h : Eisenstein) (W : C_c(ℝ,ℂ))
    {ε : ℝ} (hε : 0<ε) (hW : ∀ v≤ε,W v=0) (F : CubicThetaSection)
    (p : CubicThetaPoint) :
    (∑' g : cubicThetaPrincipalGroup,
      star (cubicThetaFourierStripSeed h W (g • p))*F.val (g • p))=
      star (cubicThetaFourierProfileSeries h p.val W)*F.val p := by
  let f : cubicThetaPrincipalGroup → ℂ := fun g =>
    star (cubicThetaFourierStripSeed h W (g • p))*F.val (g • p)
  let e : (CubicThetaBottomRow × Eisenstein) ≃ cubicThetaPrincipalGroup :=
    (Equiv.prodComm _ _).trans cubicThetaRowTranslationEquiv
  have hs : Summable (fun rw => f (e rw)) :=
    e.summable_iff.mpr (cubicThetaFourierStripSeed_pair_summable h W hε hW F p)
  calc
    _ = ∑' rw : CubicThetaBottomRow × Eisenstein,f (e rw) := (e.tsum_eq f).symm
    _ = ∑' r : CubicThetaBottomRow,∑' w : Eisenstein,f (e (r,w)) := hs.tsum_prod
    _ = ∑' r : CubicThetaBottomRow,star (cubicThetaFourierProfileTerm h r p.val W)*F.val p := by
      apply tsum_congr
      intro r
      change (∑' w : Eisenstein,star (cubicThetaFourierStripSeed h W
        ((cubicThetaPrincipalTranslation w*r.completion) • p))*
          F.val ((cubicThetaPrincipalTranslation w*r.completion) • p))=_
      simp_rw [mul_smul]
      rw [cubicThetaFourierStripSeed_pair_translation_sum]
      have hh : (r.completion • p).val.2=r.height p.val := by
        change (cubicThetaBottomRow r.completion).height p.val=_
        rw [r.completion_row]
      have hf := F.property r.completion p
      change F.val (r.completion • p)=cubicThetaKubotaValue r.completion*F.val p at hf
      rw [hh,hf]
      simp only [cubicThetaFourierProfileTerm,cubicThetaRadialProfileTerm,star_mul,star_star]
      rw [cubicThetaKubotaValue_bottomRow,r.completion_row]
      change star (cubicThetaHorizontalCharacter h
        (cubicThetaMobius (cubicThetaPrincipalComplex r.completion) p.val).1)*
          star (W (r.height p.val))*(r.phase*F.val p)=_
      ring
    _ = _ := by rw [tsum_mul_right,←tsum_star]; rfl

theorem cubicThetaPositiveFourierProfile_pairing_integral (h : Eisenstein) (W : C_c(ℝ,ℂ))
    {ε : ℝ} (hε : 0<ε) (hW : ∀ v≤ε,W v=0) (F : CubicThetaSection) :
    (∫ q,cubicThetaSectionPairing (cubicThetaPositiveFourierProfileSection h W hε hW) F q
      ∂cubicThetaQuotientMeasure)=
      ∫ p,star (cubicThetaFourierStripSeed h W p)*F.val p ∂cubicThetaPointMeasure := by
  rw [cubicThetaQuotientMeasure,
    integral_map_of_stronglyMeasurable cubicThetaQuotientMap_open.continuous.measurable
      (cubicThetaSectionPairing_continuous _ _).stronglyMeasurable]
  have he (p : CubicThetaPoint) :
      cubicThetaSectionPairing (cubicThetaPositiveFourierProfileSection h W hε hW) F
        (cubicThetaQuotientMap p)=
      ∑' g : cubicThetaPrincipalGroup,
        star (cubicThetaFourierStripSeed h W (g • p))*F.val (g • p) := by
    rw [cubicThetaFourierStripSeed_group_sum h W hε hW F p,cubicThetaSectionPairing_apply]
    change inner ℂ (cubicThetaFourierProfileSeries h p.val W) (F.val p)=_
    simp only [RCLike.inner_apply',starRingEnd_apply]
  simp_rw [he]
  exact cubicThetaFundamental_integral_tsum (cubicThetaFourierStripSeed_pair_integrable h W hε hW F)

end CubicFirstMoment

end

end OAI
