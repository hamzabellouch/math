import Mathlib
import OAI.Analysis.CoulombIonization.ThomasFermi.RadialPatchCap
import OAI.Analysis.CoulombIonization.Localization.CanonicalRealPacketBarrier
import OAI.Analysis.CoulombIonization.RadialBounds.InverseKernelMassBarrier

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped Topology ContDiff

namespace CoulombAtom
open CoulombAnalysis

 def localTFResponse (h : ℝ) : ℝ :=
  (max h 0/((5/3:ℝ)*tfKinetic))^(3/2:ℝ)

lemma localTFResponse_continuous : Continuous localTFResponse := by
  unfold localTFResponse
  exact (Real.continuous_rpow_const (by norm_num : (0:ℝ) ≤ 3/2)).comp
    ((continuous_id.max continuous_const).div_const _)

lemma localTFResponse_rescale {a : ℝ} (ha : 0 < a) (h : ℝ) :
    a^6*localTFResponse h = localTFResponse (a^4*h) := by
  have he : max (a^4*h) 0 = a^4*max h 0 := by
    rw [mul_max_of_nonneg _ _ (pow_nonneg ha.le _),mul_zero]
  have hT := tfKinetic_pos
  unfold localTFResponse
  rw [he,mul_div_assoc,Real.mul_rpow (pow_nonneg ha.le _) (by positivity),
    ←Real.rpow_natCast a 4,←Real.rpow_mul ha.le]
  norm_num

lemma inverse_oscillation_rescale {a R : ℝ} (ha : 0 < a) (hR : 0 < R)
    (C n t : ℝ) :
    a^4*(C/R*(n*t))*R⁻¹^4 = C*n*(t/a)*(a/R)^5 := by
  field_simp

lemma inverse_oscillation_tendsto {ι : Type*} {l : Filter ι}
    {a R t : ι → ℝ} {C n : ℝ} (hC : 0 ≤ C) (hn : 0 ≤ n)
    (ha : ∀ᶠ i in l, 0 < a i) (hR : ∀ᶠ i in l, a i ≤ R i)
    (ht : ∀ᶠ i in l, 0 ≤ t i) (ht0 : Tendsto (fun i => t i/a i) l (𝓝 0)) :
    Tendsto (fun i => (a i)^4*(C/R i*(n*t i))*(R i)⁻¹^4) l (𝓝 0) := by
  have hh : Tendsto (fun i => C*n*(t i/a i)) l (𝓝 0) := by
    simpa only [mul_zero] using ht0.const_mul (C*n)
  apply squeeze_zero' _ _ hh
  · filter_upwards [ha,hR,ht] with i hai hRi hti
    have hRi' := hai.trans_le hRi
    positivity
  · filter_upwards [ha,hR,ht] with i hai hRi hti
    have hRi' := hai.trans_le hRi
    rw [inverse_oscillation_rescale hai hRi']
    have hh : (a i/R i)^5 ≤ 1 := pow_le_one₀ (div_nonneg hai.le hRi'.le)
      ((div_le_one hRi').mpr hRi)
    exact (mul_le_mul_of_nonneg_left hh (by positivity)).trans_eq (mul_one _)

theorem fresh_threshold_response_tendsto {ι : Type*} {l : Filter ι}
    {a r₀ s R H : ι → ℝ} {y : ι → Space} {c₁ n sign h : ℝ}
    (hc : 0 < c₁) (hcL : c₁ < (10*(100000:ℝ))⁻¹) (hn : 2 ≤ n)
    (ha : ∀ᶠ i in l, 0 < a i) (ha0 : Tendsto a l (𝓝 0))
    (hr : ∀ᶠ i in l, 0 < r₀ i) (hs : ∀ᶠ i in l, 0 < s i)
    (hs0 : Tendsto s l (𝓝 0))
    (hR : ∀ᶠ i in l, a i ≤ R i)
    (hw : ∀ᶠ i in l, c₁*(a i)^(1+masterExponent) ≤ masterWidth c₁ (r₀ i) (s i) (y i))
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
    hc (by linarith : 0 ≤ n) ha ha0 hw
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

end CoulombAtom

end

end OAI
