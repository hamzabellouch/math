import OAI.Geometry.CylinderCovering.Radial.SectorArea

namespace OAI

open Set MeasureTheory

noncomputable section

namespace AngularCaps

theorem radialBandParameters_eq_image {l r ρ : ℝ} {R : ℝ → ℝ} :
    radialBandParameters l r ρ R =
      (fun p : ℝ × ℝ => (p.1, p.2 + ρ)) ''
        radialParameterSet l r (fun q => R q - ρ) := by
  ext p
  constructor
  · rintro ⟨hq, hs⟩
    refine ⟨(p.1, p.2 - ρ), ⟨hq, by dsimp; constructor <;> linarith [hs.1, hs.2]⟩, ?_⟩
    apply Prod.ext <;> simp
  · rintro ⟨p, hp, rfl⟩
    refine ⟨hp.1, ?_, ?_⟩ <;> dsimp <;> linarith [hp.2.1, hp.2.2]

theorem isCompact_radialBandParameters {l r ρ : ℝ} {R : ℝ → ℝ}
    (hRcont : ContinuousOn R (Icc l r)) (hR : ∀ q ∈ Icc l r, ρ ≤ R q) :
    IsCompact (radialBandParameters l r ρ R) := by
  rw [radialBandParameters_eq_image]
  apply (isCompact_radialParameterSet (hRcont.sub continuousOn_const)
    (fun q hq => sub_nonneg.mpr (hR q hq))).image
  fun_prop

theorem isCompact_radialBand {l r ρ : ℝ} {R : ℝ → ℝ}
    (hRcont : ContinuousOn R (Icc l r)) (hR : ∀ q ∈ Icc l r, ρ ≤ R q) :
    IsCompact (radialBand l r ρ R) :=
  (isCompact_radialBandParameters hRcont hR).image continuous_radialMap

theorem radialBand_integral_change {l r ρ : ℝ} {R F : ℝ → ℝ}
    (hρ : 0 < ρ) (hRcont : ContinuousOn R (Icc l r))
    (hR : ∀ q ∈ Icc l r, ρ ≤ R q) :
    (∫ p in radialBand l r ρ R, F (p.1 / p.2)) =
      ∫ p in radialBandParameters l r ρ R, p.2 * F p.1 := by
  have hD := (isCompact_radialBandParameters hRcont hR).measurableSet
  have hinj : InjOn radialMap (radialBandParameters l r ρ R) :=
    radialMap_injOn_positive.mono (fun p hp => lt_of_lt_of_le hρ hp.2.1)
  rw [radialBand, integral_image_eq_integral_abs_det_fderiv_smul volume hD
    (fun p _ => (radialMap_hasFDerivAt p).hasFDerivWithinAt) hinj]
  apply setIntegral_congr_fun hD
  intro p hp
  have hp0 : 0 < p.2 := lt_of_lt_of_le hρ hp.2.1
  change |(radialDerivative p : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ)).det| *
    F ((radialMap p).1 / (radialMap p).2) = p.2 * F p.1
  rw [radialDerivative_det, abs_of_pos hp0]
  simp [radialMap, mul_div_cancel_right₀ _ (ne_of_gt hp0)]

theorem weighted_radialBandParameters_integral {l r ρ : ℝ} {R F : ℝ → ℝ}
    (hRcont : ContinuousOn R (Icc l r)) (hR : ∀ q ∈ Icc l r, ρ ≤ R q)
    (hFcont : ContinuousOn F (Icc l r)) :
    (∫ p in radialBandParameters l r ρ R, p.2 * F p.1) =
      ∫ q in Icc l r, ((R q) ^ 2 - ρ ^ 2) / 2 * F q := by
  let D := radialBandParameters l r ρ R
  have hcompact : IsCompact D := isCompact_radialBandParameters hRcont hR
  have hD : MeasurableSet D := hcompact.measurableSet
  have hf : IntegrableOn (fun p : ℝ × ℝ => p.2 * F p.1) D := by
    apply ContinuousOn.integrableOn_compact hcompact
    exact continuous_snd.continuousOn.mul
      (hFcont.comp continuous_fst.continuousOn (fun p hp => hp.1))
  have hfind : Integrable (D.indicator (fun p : ℝ × ℝ => p.2 * F p.1)) volume :=
    (integrable_indicator_iff hD).2 hf
  rw [← integral_indicator hD, Measure.volume_eq_prod]
  rw [integral_prod _ (by simpa only [Measure.volume_eq_prod] using hfind)]
  rw [← integral_indicator measurableSet_Icc]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro q
  change (∫ s : ℝ, D.indicator (fun p : ℝ × ℝ => p.2 * F p.1) (q, s)) = _
  by_cases hq : q ∈ Icc l r
  · have heq : (fun s : ℝ => D.indicator (fun p : ℝ × ℝ => p.2 * F p.1) (q, s)) =
        (Icc ρ (R q)).indicator (fun s : ℝ => s * F q) := by
      funext s
      simp only [D, radialBandParameters, Set.indicator_apply, Set.mem_ofPred_eq,
        hq, true_and]
    rw [heq, integral_indicator measurableSet_Icc, integral_mul_const,
      integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (hR q hq), integral_id]
    simp [hq]
  · have heq : (fun s : ℝ => D.indicator (fun p : ℝ × ℝ => p.2 * F p.1) (q, s)) = 0 := by
      funext s
      apply Set.indicator_of_notMem
      exact fun hp => hq hp.1
    rw [heq]
    change (∫ s : ℝ, (0 : ℝ)) = _
    simp [hq]

theorem radialBand_weighted_integral {l r ρ : ℝ} {R F : ℝ → ℝ}
    (hlr : l ≤ r) (hρ : 0 < ρ) (hRcont : ContinuousOn R (Icc l r))
    (hR : ∀ q ∈ Icc l r, ρ ≤ R q) (hFcont : ContinuousOn F (Icc l r)) :
    (∫ p in radialBand l r ρ R, F (p.1 / p.2)) =
      ∫ q in l..r, ((R q) ^ 2 - ρ ^ 2) / 2 * F q := by
  rw [radialBand_integral_change hρ hRcont hR,
    weighted_radialBandParameters_integral hRcont hR hFcont,
    integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le hlr]

theorem radialBand_weighted_le_full {l r ρ : ℝ} {R F : ℝ → ℝ}
    (hlr : l ≤ r) (hρ : 0 < ρ) (hRcont : ContinuousOn R (Icc l r))
    (hR : ∀ q ∈ Icc l r, ρ ≤ R q) (hFcont : ContinuousOn F (Icc l r))
    (hF : ∀ q ∈ Icc l r, 0 ≤ F q) :
    (∫ p in radialBand l r ρ R, F (p.1 / p.2)) ≤
      ∫ q in l..r, (R q) ^ 2 / 2 * F q := by
  rw [radialBand_weighted_integral hlr hρ hRcont hR hFcont]
  have hleft : ContinuousOn (fun q => ((R q) ^ 2 - ρ ^ 2) / 2 * F q) (Icc l r) :=
    (((hRcont.pow 2).sub continuousOn_const).div_const 2).mul hFcont
  have hright : ContinuousOn (fun q => (R q) ^ 2 / 2 * F q) (Icc l r) :=
    ((hRcont.pow 2).div_const 2).mul hFcont
  apply intervalIntegral.integral_mono_on hlr
    (hleft.intervalIntegrable_of_Icc hlr) (hright.intervalIntegrable_of_Icc hlr)
  intro q hq
  exact mul_le_mul_of_nonneg_right (by nlinarith [sq_nonneg ρ]) (hF q hq)

end AngularCaps

end

end OAI
