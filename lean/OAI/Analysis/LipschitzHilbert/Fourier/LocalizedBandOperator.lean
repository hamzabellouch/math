import OAI.Analysis.LipschitzHilbert.Fourier.LocalizedBandStrong

namespace OAI

/-! The localized positive-band Hilbert operator has a uniform L2 norm,
independent of its sharp inner endpoint and vertical frequency width. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace LipschitzHilbert.PacketRepresentation

def localizedSharpBandOperator (epsilon R : ℝ) (he : 0<epsilon) (hR : 0<R)
    (field : Plane → ℝ) (hfield : LipschitzWith 1 field) (p : SchwartzMap ℝ ℂ) (w l r : ℝ) :
    Lp ℂ 2 planeMeasure →L[ℂ] Lp ℂ 2 planeMeasure :=
  (stripL2Cutoff l r).comp
    ((bandL2Operator (sharpTimeKernel epsilon R) (sharpTimeKernel_measurable epsilon R)
      (sharpTimeKernel_integrable epsilon R he hR) (fun z => field (planeCoordinates z))
      (by simpa only [mul_one] using product_slope_lipschitz field hfield) p w).comp (stripL2Cutoff l r))

theorem localizedSharpBandPairing_eq_inner (epsilon R : ℝ) (he : 0<epsilon) (hR : 0<R)
    (field : Plane → ℝ) (hfield : LipschitzWith 1 field) (p : SchwartzMap ℝ ℂ) (w l r : ℝ)
    (f g : Lp ℂ 2 planeMeasure) :
    localizedSharpBandPairing epsilon R he hR field hfield p w l r f g=
      inner ℂ g (localizedSharpBandOperator epsilon R he hR field hfield p w l r f) := by
  exact l2Indicator_inner planeMeasure (horizontalStrip l r) (horizontalStrip_measurable l r)
    g ((bandL2Operator (sharpTimeKernel epsilon R) (sharpTimeKernel_measurable epsilon R)
      (sharpTimeKernel_integrable epsilon R he hR) (fun z => field (planeCoordinates z))
      (by simpa only [mul_one] using product_slope_lipschitz field hfield) p w) (stripL2Cutoff l r f))

theorem localized_sharp_band_operator_norm (hVariation : LepingleInput) (hLL : LaceyLiInput)
    (hH : HorizontalHilbertInput) (p : SchwartzMap ℝ ℂ) (hp : ∀ s, p s≠0 → 1≤s ∧ s≤2) :
    ∃ C : ℝ, 0<C ∧ ∀ epsilon R w : ℝ, (he : 0<epsilon) → (heR : epsilon≤R) → R≤1/4 → 0<w →
    ∀ (field : Plane → ℝ) (hfield : LipschitzWith 1 field), (∀ z, |field z|≤1/4) →
    ∀ l r : ℝ, 1200*(r-l)≤1 →
      ‖localizedSharpBandOperator epsilon R he (he.trans_le heR) field hfield p w l r‖≤C := by
  obtain ⟨C,hC,hbound⟩ := localized_sharp_band_strong hVariation hLL hH p hp
  refine ⟨C,hC,?_⟩
  intro epsilon R w he heR hR hw field hfield hfb l r hwidth
  apply ContinuousLinearMap.opNorm_le_bound _ hC.le
  intro f
  let T := localizedSharpBandOperator epsilon R he (he.trans_le heR) field hfield p w l r
  have h := hbound epsilon R w he heR hR hw field hfield hfb l r hwidth f (T f)
  rw [localizedSharpBandPairing_eq_inner] at h
  change ‖inner ℂ (T f) (T f)‖≤C*‖f‖*‖T f‖ at h
  rw [inner_self_eq_norm_sq_to_K] at h
  simp only [norm_pow,RCLike.norm_ofReal,abs_of_nonneg (norm_nonneg (T f))] at h
  by_cases hz : ‖T f‖=0
  · rw [show ‖localizedSharpBandOperator epsilon R he (he.trans_le heR) field hfield p w l r f‖=0 from hz]
    exact mul_nonneg hC.le (norm_nonneg f)
  · have ht : 0<‖T f‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    apply (mul_le_mul_iff_right₀ ht).mp
    simpa only [pow_two,mul_comm] using h

end LipschitzHilbert.PacketRepresentation

end

end OAI
