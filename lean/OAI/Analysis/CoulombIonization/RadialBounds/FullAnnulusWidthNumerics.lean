import Mathlib
import OAI.Analysis.CoulombIonization.RadialBounds.InverseNumericalStatementsBarrier

namespace OAI

open MeasureTheory Filter Set Metric
open scoped Topology ContDiff
noncomputable section
namespace CoulombAtom
open CoulombAnalysis CoulombBarrier CoulombObservation

theorem fresh_threshold_response_tendsto_of_width {ι : Type*} {l : Filter ι}
    {a r₀ s R H : ι → ℝ} {y : ι → Space} {c₁ c₂ n sign h : ℝ}
    (hc : 0 < c₁) (hcL : c₁ < (10*(100000:ℝ))⁻¹) (hc₂ : 0 < c₂) (hn : 2 ≤ n)
    (ha : ∀ᶠ i in l, 0 < a i) (ha0 : Tendsto a l (𝓝 0))
    (hr : ∀ᶠ i in l, 0 < r₀ i) (hs : ∀ᶠ i in l, 0 < s i)
    (hs0 : Tendsto s l (𝓝 0))
    (hR : ∀ᶠ i in l, a i ≤ R i)
    (hw : ∀ᶠ i in l, c₂*(a i)^(1+masterExponent) ≤ masterWidth c₁ (r₀ i) (s i) (y i))
    (hw0 : Tendsto (fun i => masterWidth c₁ (r₀ i) (s i) (y i)/a i) l (𝓝 0))
    (hH : Tendsto (fun i => (a i)^4*H i) l (𝓝 h)) :
    Tendsto (fun i => (a i)^6*(
      localTFResponse (H i+sign*(tfPatchOscillationConstant/R i*
        (n*masterWidth c₁ (r₀ i) (s i) (y i)))*(R i)⁻¹^4)*
        (∫ x, masterCenteredKernel c₁ (r₀ i) (s i) canonicalRealPacket (y i) x ∂ballMeasure (R i))+
      sign*Real.sqrt ((16*(n*masterWidth c₁ (r₀ i) (s i) (y i))^3*
        ((masterTestConstant canonicalRealPacket_smooth canonicalRealPacket_support:ℝ)*
        (masterWidth c₁ (r₀ i) (s i) (y i))⁻¹^4)^2)*(a i)^(-7+(1/100:ℝ)))))
      l (𝓝 (localTFResponse h)) := by
  let t := fun i => masterWidth c₁ (r₀ i) (s i) (y i)
  have ht : ∀ᶠ i in l, 0 < t i := by
    filter_upwards [hr,hs] with i hri hsi
    exact masterWidth_pos hc hri hsi (y i)
  have hosc := inverse_oscillation_tendsto tfPatchOscillationConstant_pos.le
    (by linarith : 0 ≤ n) ha hR (ht.mono fun _ hi => hi.le) hw0
  have hinner := hH.add (hosc.const_mul sign)
  simp only [mul_zero,add_zero] at hinner
  have hresp := localTFResponse_continuous.continuousAt.tendsto.comp hinner
  have hfit : ∀ᶠ i in l, 2*t i < R i := by
    filter_upwards [ha,hR,hw0.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1/2))]
      with i hai hRi hi
    have hh : t i < (1/2:ℝ)*a i := (div_lt_iff₀ hai).mp hi
    linarith
  have hmass := masterCenteredKernel_mass_tendsto canonicalRealPacket_smooth
    canonicalRealPacket_support canonicalRealPacket_normalized hc hcL hr hs hs0 hfit
  have herr := inverse_duality_tendsto (L := (masterTestConstant canonicalRealPacket_smooth canonicalRealPacket_support:ℝ))
    hc₂ (by linarith : 0 ≤ n) ha ha0 hw
  have hh := (hresp.mul hmass).add (herr.const_mul sign)
  simp only [mul_one,mul_zero,add_zero] at hh
  apply hh.congr'
  filter_upwards [ha] with i hai
  simp only [Function.comp_apply]
  rw [show (a i)^4*H i+sign*((a i)^4*(tfPatchOscillationConstant/R i*(n*t i))*(R i)⁻¹^4) =
      (a i)^4*(H i+sign*(tfPatchOscillationConstant/R i*(n*t i))*(R i)⁻¹^4) by ring,
    ←localTFResponse_rescale hai]
  dsimp only [t]
  ring

lemma freshLowThreshold_tendsto_of_width {ι : Type*} {l : Filter ι}
    {a r₀ s R H : ι → ℝ} {y : ι → Space} {c₁ c₂ h : ℝ}
    (hc : 0 < c₁) (hcL : c₁ < (10*(100000:ℝ))⁻¹) (hc₂ : 0 < c₂)
    (ha : ∀ᶠ i in l, 0 < a i) (ha0 : Tendsto a l (𝓝 0))
    (hr : ∀ᶠ i in l, 0 < r₀ i) (hs : ∀ᶠ i in l, 0 < s i) (hs0 : Tendsto s l (𝓝 0))
    (hR : ∀ᶠ i in l, a i ≤ R i)
    (hw : ∀ᶠ i in l, c₂*(a i)^(1+masterExponent) ≤ masterWidth c₁ (r₀ i) (s i) (y i))
    (hw0 : Tendsto (fun i => masterWidth c₁ (r₀ i) (s i) (y i)/a i) l (𝓝 0))
    (hH : Tendsto (fun i => (a i)^4*H i) l (𝓝 h)) :
    Tendsto (fun i => (a i)^6*freshLowThreshold (y i) (R i) (H i)
      ((a i)^(-7+(1/100:ℝ))) c₁ (r₀ i) (s i)) l (𝓝 (localTFResponse h)) := by
  simpa only [freshLowThreshold,localTFResponse,neg_one_mul,neg_mul,one_mul,sub_eq_add_neg] using
    (fresh_threshold_response_tendsto_of_width (sign := -1) hc hcL hc₂ (by norm_num : (2:ℝ) ≤ 2)
      ha ha0 hr hs hs0 hR hw hw0 hH)

lemma freshHighThreshold_tendsto_of_width {ι : Type*} {l : Filter ι}
    {a r₀ s R H : ι → ℝ} {y : ι → Space} {c₁ c₂ h : ℝ}
    (hc : 0 < c₁) (hcL : c₁ < (10*(100000:ℝ))⁻¹) (hc₂ : 0 < c₂)
    (ha : ∀ᶠ i in l, 0 < a i) (ha0 : Tendsto a l (𝓝 0))
    (hr : ∀ᶠ i in l, 0 < r₀ i) (hs : ∀ᶠ i in l, 0 < s i) (hs0 : Tendsto s l (𝓝 0))
    (hR : ∀ᶠ i in l, a i ≤ R i)
    (hw : ∀ᶠ i in l, c₂*(a i)^(1+masterExponent) ≤ masterWidth c₁ (r₀ i) (s i) (y i))
    (hw0 : Tendsto (fun i => masterWidth c₁ (r₀ i) (s i) (y i)/a i) l (𝓝 0))
    (hH : Tendsto (fun i => (a i)^4*H i) l (𝓝 h)) :
    Tendsto (fun i => (a i)^6*freshHighThreshold (y i) (R i) (H i)
      ((a i)^(-7+(1/100:ℝ))) c₁ (r₀ i) (s i)) l (𝓝 (localTFResponse h)) := by
  simpa only [freshHighThreshold,localTFResponse,one_mul] using
    (fresh_threshold_response_tendsto_of_width (sign := 1) hc hcL hc₂ (by norm_num : (2:ℝ) ≤ 3)
      ha ha0 hr hs hs0 hR hw hw0 hH)

lemma inverse_density_error_tendsto_of_width {ι : Type*} {l : Filter ι}
    {r₀ s ell : ι → ℝ} {y : ι → Space} {c₁ c₂ E C : ℝ}
    (hc₂ : 0 < c₂) (hE : 0 ≤ E)
    (hy : ∀ᶠ i in l, y i ≠ 0)
    (ha0 : Tendsto (fun i => localCellRadius (y i)) l (𝓝 0))
    (hw : ∀ᶠ i in l, c₂*(localCellRadius (y i))^(1+masterExponent) ≤ masterWidth c₁ (r₀ i) (s i) (y i))
    (hell : ∀ᶠ i in l, 0 ≤ ell i ∧ ell i ≤ E*(localCellRadius (y i))^(101/100:ℝ)) :
    Tendsto (fun i => (localCellRadius (y i))^6*inverseDensityError c₁ (r₀ i) (s i) (ell i) C (y i)) l (𝓝 0) := by
  have ha := hy.mono fun i hi => localCellRadius_pos hi
  exact inverse_observation_error_tendsto hc₂ hE ha ha0 hw hell (scaled_div_pow_constant ha 3 C)

theorem low_inverse_numerics_eventually_of_width {ι : Type*} {l : Filter ι}
    {y : ι → Space} {r₀ s ell D : ι → ℝ} {c₁ c₂ E C h xi : ℝ}
    (hc : 0 < c₁) (hcL : c₁ < (10*(100000:ℝ))⁻¹) (hc₂ : 0 < c₂) (hE : 0 ≤ E)
    (hh : 0 ≤ h) (hxi : 0 < xi)
    (hy : ∀ᶠ i in l, y i ≠ 0)
    (ha0 : Tendsto (fun i => localCellRadius (y i)) l (𝓝 0))
    (hr : ∀ᶠ i in l, 0 < r₀ i) (hs : ∀ᶠ i in l, 0 < s i) (hs0 : Tendsto s l (𝓝 0))
    (hw : ∀ᶠ i in l, c₂*(localCellRadius (y i))^(1+masterExponent) ≤ masterWidth c₁ (r₀ i) (s i) (y i))
    (hw0 : Tendsto (fun i => masterWidth c₁ (r₀ i) (s i) (y i)/localCellRadius (y i)) l (𝓝 0))
    (hell : ∀ᶠ i in l, 0 ≤ ell i ∧ ell i ≤ E*(localCellRadius (y i))^(101/100:ℝ))
    (hD : Tendsto (fun i => D i*(localCellRadius (y i))^(7-masterExponent)) l (𝓝 0))
    (hDgap : Tendsto (fun i => D i*(localCellRadius (y i))^(7-(1/100:ℝ))) l (𝓝 0)) :
    ∀ᶠ i in l, LowInverseNumerics c₁ (r₀ i) (s i) (ell i) (D i) h xi C (y i) := by
  let a := fun i => localCellRadius (y i)
  let H := fun i => (h+xi/2)/(a i)^4
  have ha : ∀ᶠ i in l, 0 < a i := hy.mono fun i hi => localCellRadius_pos hi
  have hsmallb : ∀ᶠ i in l, (a i)^(6/5:ℝ) < a i := by
    filter_upwards [ha,(microscopic_relative_tendsto ha ha0).eventually
      (gt_mem_nhds (by norm_num : (0:ℝ) < 1))] with i hai hi
    simpa only [one_mul] using (div_lt_iff₀ hai).mp hi
  have hH : Tendsto (fun i => (a i)^4*H i) l (𝓝 (h+xi/2)) := scaled_div_pow_constant ha 4 _
  have hT := scaled_div_pow_constant ha 6 (localTFResponse h)
  have hdenerr := inverse_density_error_tendsto_of_width (C := C) hc₂ hE hy ha0 hw hell
  have ht : ∀ᶠ i in l, 0 ≤ masterWidth c₁ (r₀ i) (s i) (y i) := by
    filter_upwards [hr,hs] with i hri hsi
    exact (masterWidth_pos hc hri hsi _).le
  have hpot := inverse_potential_error_tendsto hy ha0 hD ht hw0
  have hG : Tendsto (fun i => inverseGapBudget (D i) (y i)*(a i)^(7-(1/100:ℝ))) l (𝓝 0) :=
    physical_patch_error_tendsto hy ha0 (by norm_num : (0:ℝ) < 1/100) (by norm_num) hDgap
  apply eventually_forall_mem_of_selections (fun i => 5*a i) (by
    filter_upwards [ha] with i hai
    exact ⟨le_rfl,by linarith⟩)
  intro t htcut
  let R := fun i => t i-4*(a i)^(6/5:ℝ)
  have hR : ∀ᶠ i in l, a i ≤ R i := by
    filter_upwards [hsmallb,htcut] with i hbi hti
    dsimp only [R]
    linarith [hti.1]
  have hF := freshLowThreshold_tendsto_of_width hc hcL hc₂ ha ha0 hr hs hs0 hR hw hw0 hH
  have hdensity := inverse_low_density_margin ha hT hdenerr hF
    (localTFResponse_strict_mono hh (by linarith : h < h+xi/2))
  have hgap := inverse_low_gap_tendsto tfPatchCapConstant_pos.le ha hR hG
  have hleft := (hH.add hgap).add hpot
  simp only [add_zero] at hleft
  have hright := scaled_div_pow_constant ha 4 (h+xi)
  have hsmall := hleft.eventually_lt hright (by linarith : h+xi/2 < h+xi)
  filter_upwards [ha,hdensity,hsmall] with i hai hdi hsi
  refine ⟨hdi,?_⟩
  apply (mul_lt_mul_iff_right₀ (pow_pos hai 4)).mp
  dsimp only [H,R,a,inverseGapBudget,inversePotentialError] at hsi ⊢
  linarith only [hsi]

theorem high_inverse_numerics_eventually_of_width {ι : Type*} {l : Filter ι}
    {y : ι → Space} {r₀ s ell D : ι → ℝ} {c₁ c₂ E C h xi : ℝ}
    (hc : 0 < c₁) (hcL : c₁ < (10*(100000:ℝ))⁻¹) (hc₂ : 0 < c₂) (hE : 0 ≤ E)
    (hxi : 0 < xi) (hxih : xi < 2*h)
    (hy : ∀ᶠ i in l, y i ≠ 0)
    (ha0 : Tendsto (fun i => localCellRadius (y i)) l (𝓝 0))
    (hr : ∀ᶠ i in l, 0 < r₀ i) (hs : ∀ᶠ i in l, 0 < s i) (hs0 : Tendsto s l (𝓝 0))
    (hw : ∀ᶠ i in l, c₂*(localCellRadius (y i))^(1+masterExponent) ≤ masterWidth c₁ (r₀ i) (s i) (y i))
    (hw0 : Tendsto (fun i => masterWidth c₁ (r₀ i) (s i) (y i)/localCellRadius (y i)) l (𝓝 0))
    (hell : ∀ᶠ i in l, 0 ≤ ell i ∧ ell i ≤ E*(localCellRadius (y i))^(101/100:ℝ))
    (hD : Tendsto (fun i => D i*(localCellRadius (y i))^(7-masterExponent)) l (𝓝 0))
    (hDgap : Tendsto (fun i => D i*(localCellRadius (y i))^(7-(1/100:ℝ))) l (𝓝 0)) :
    ∀ᶠ i in l, HighInverseNumerics c₁ (r₀ i) (s i) (ell i) (D i) h xi C (y i) := by
  let a := fun i => localCellRadius (y i)
  let H := fun i => (h-xi/2)/(a i)^4
  have ha : ∀ᶠ i in l, 0 < a i := hy.mono fun i hi => localCellRadius_pos hi
  have hsmallb : ∀ᶠ i in l, (a i)^(6/5:ℝ) < a i := by
    filter_upwards [ha,(microscopic_relative_tendsto ha ha0).eventually
      (gt_mem_nhds (by norm_num : (0:ℝ) < 1))] with i hai hi
    simpa only [one_mul] using (div_lt_iff₀ hai).mp hi
  have hH : Tendsto (fun i => (a i)^4*H i) l (𝓝 (h-xi/2)) := scaled_div_pow_constant ha 4 _
  have hT := scaled_div_pow_constant ha 6 (localTFResponse h)
  have hdenerr := inverse_density_error_tendsto_of_width (C := C) hc₂ hE hy ha0 hw hell
  have ht : ∀ᶠ i in l, 0 ≤ masterWidth c₁ (r₀ i) (s i) (y i) := by
    filter_upwards [hr,hs] with i hri hsi
    exact (masterWidth_pos hc hri hsi _).le
  have hpot := inverse_potential_error_tendsto hy ha0 hD ht hw0
  have hG : Tendsto (fun i => inverseGapBudget (D i) (y i)*(a i)^(7-(1/100:ℝ))) l (𝓝 0) :=
    physical_patch_error_tendsto hy ha0 (by norm_num : (0:ℝ) < 1/100) (by norm_num) hDgap
  have hgap := inverse_high_gap_tendsto ha hH hG
  have hmass := inverse_retained_tendsto hc₂ canonicalMasterAmplitude_pos.le ha ha0 hw
  apply eventually_forall_mem_of_selections (fun i => 5*a i) (by
    filter_upwards [ha] with i hai
    exact ⟨le_rfl,by linarith⟩)
  intro t htcut
  let R := fun i => t i-4*(a i)^(6/5:ℝ)
  have hR : ∀ᶠ i in l, a i ≤ R i := by
    filter_upwards [hsmallb,htcut] with i hbi hti
    dsimp only [R]
    linarith [hti.1]
  have hF := freshHighThreshold_tendsto_of_width hc hcL hc₂ ha ha0 hr hs hs0 hR hw hw0 hH
  have hdensity := inverse_high_density_margin ha hT hdenerr hF hmass
    (localTFResponse_nonneg (h-xi/2))
    (localTFResponse_strict_mono (by linarith : 0 ≤ h-xi/2) (by linarith : h-xi/2 < h))
  have hosc := inverse_unscaled_oscillation_tendsto ha hR hw0 tfPatchOscillationConstant 3
  have hoscsmall := hosc.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1/2))
  have hoscscaled := inverse_oscillation_tendsto tfPatchOscillationConstant_pos.le
    (by norm_num : (0:ℝ) ≤ 3) ha hR ht hw0
  have hleft := (scaled_div_pow_constant ha 4 (h-xi)).add hpot
  simp only [add_zero] at hleft
  have hright := (hH.sub hgap).sub (hoscscaled.const_mul 2)
  simp only [sub_zero,mul_zero] at hright
  have hsmall := hleft.eventually_lt hright (by linarith : h-xi < h-xi/2)
  filter_upwards [ha,hoscsmall,hdensity,hsmall] with i hai hosi hdi hsi
  refine ⟨hosi.le,hdi,?_⟩
  apply (mul_lt_mul_iff_right₀ (pow_pos hai 4)).mp
  dsimp only [H,R,a,inverseGapBudget,inversePotentialError] at hsi ⊢
  linarith only [hsi]

end CoulombAtom

end

end OAI
