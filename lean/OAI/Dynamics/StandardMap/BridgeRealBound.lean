import OAI.Dynamics.StandardMap.FastBridge

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology Classical
namespace StandardMapEntropy
lemma strict_markov_real {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (H : X → ℝ) (hi : Integrable H μ) (h0 : ∀ x,0≤H x) (h : ℝ) (hh : 0<h) :
    μ {x | h<H x} ≤ ENNReal.ofReal ((∫ x,H x ∂μ)/h) := by
  have hb := meas_ge_le_lintegral_div hi.aestronglyMeasurable.aemeasurable.ennreal_ofReal
    (ENNReal.ofReal_ne_zero_iff.mpr hh) ENNReal.ofReal_ne_top
  rw [←ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall h0)] at hb
  have hs : {x | h<H x} ⊆ {x | ENNReal.ofReal h≤ENNReal.ofReal (H x)} := fun x hx => ENNReal.ofReal_le_ofReal hx.le
  exact (measure_mono hs).trans (hb.trans_eq (ENNReal.ofReal_div_of_pos hh).symm)
lemma real_integral_bound_of_lintegral {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (W : X → ℝ) (hi : Integrable W μ) (h0 : ∀ x,0≤W x) (E : Set X)
    (C : ℝ) (hC : 0≤C) (hb : (∫⁻ x in E,ENNReal.ofReal (W x) ∂μ)≤ENNReal.ofReal C) :
    (∫ x in E,W x ∂μ) ≤ C := by
  rw [←ofReal_integral_eq_lintegral_ofReal hi.restrict (Eventually.of_forall h0)] at hb
  exact (ENNReal.ofReal_le_ofReal_iff hC).mp hb
noncomputable def bridgeRealConstant : ℝ := fastBridgeConstant.toReal
lemma bridgeRealConstant_nonneg : 0≤bridgeRealConstant := ENNReal.toReal_nonneg
lemma actual_fast_bridge_real (k : ℝ) (hc : BridgeScalarControl k)
    (N r : ℕ) (hN : 100 ≤ N) (hr : (r:ℝ) ≤ (N:ℝ)/1000)
    {Rw Rh : ℕ} (aw : Fin Rw → ℤ) (nw : Fin Rw → ℕ) (Fw : (Fin Rw → ℝ) → ℝ)
    (ah : Fin Rh → ℤ) (nh : Fin Rh → ℕ) (Fh : (Fin Rh → ℝ) → ℝ)
    (hnw : ∀ j, 0 < nw j) (hnh : ∀ j, 0 < nh j) (L : NNReal)
    (hFw : LipschitzWith L Fw) (hFh : LipschitzWith L Fh)
    (hlenw : ∀ j, nw j ≤ 2*r) (hlenh : ∀ j, nh j ≤ 2*r)
    (hwinw : ∀ j l, 1 ≤ l → l ≤ nw j → (aw j+(l:ℤ)-1).natAbs ≤ r)
    (hwinh : ∀ j l, 1 ≤ l → l ≤ nh j → (ah j+(l:ℤ)-1-(N:ℤ)).natAbs ≤ r)
    (hW0 : ∀ z, 0 ≤ shortfallObservation k aw nw Fw z)
    (hH0 : ∀ z, 0 ≤ shortfallObservation k ah nh Fh z)
    (hlog : 1 ≤ Real.log (growthBase k)) (hLM : 16*Real.pi*L ≤ growthBase k)
    (h : ℝ) (hh : 0<h) (hδ : growthBase k^(-(1/10:ℝ)*(N:ℝ)) < h/2) :
    (∫ z in {z | torusFastBridge k z N} ∩ {z | h < shortfallObservation k ah nh Fh z},
      shortfallObservation k aw nw Fw z ∂area) ≤
      bridgeRealConstant*((∫ z,shortfallObservation k aw nw Fw z ∂area)+
        growthBase k^(-(1/10:ℝ)*(N:ℝ)))*((∫ z,shortfallObservation k ah nh Fh z ∂area)/(h/2)) := by
  have hW := continuous_shortfall_observation k hc.nonneg aw nw Fw hFw.continuous
  have hH := continuous_shortfall_observation k hc.nonneg ah nh Fh hFh.continuous
  have hiW := hW.integrable_of_hasCompactSupport (μ := area) (HasCompactSupport.of_compactSpace _)
  have hiH := hH.integrable_of_hasCompactSupport (μ := area) (HasCompactSupport.of_compactSpace _)
  have hb := actual_fast_bridge_product k hc N r hN hr aw nw Fw ah nh Fh hnw hnh L hFw hFh
    hlenw hlenh hwinw hwinh hW0 hlog hLM h hδ
  have hd0 : 0≤growthBase k^(-(1/10:ℝ)*(N:ℝ)) := Real.rpow_nonneg (by linarith [growthBase_ge_four k hc.nonneg]) _
  have hiW0 := integral_nonneg_of_ae (μ := area) (Eventually.of_forall hW0)
  have hiH0 := integral_nonneg_of_ae (μ := area) (Eventually.of_forall hH0)
  apply real_integral_bound_of_lintegral area _ hiW hW0 _ _
    (mul_nonneg (mul_nonneg bridgeRealConstant_nonneg (add_nonneg hiW0 hd0)) (div_nonneg hiH0 (by linarith)))
  have hm := strict_markov_real area _ hiH hH0 (h/2) (by linarith)
  apply (hb.trans (mul_le_mul_of_nonneg_left hm bot_le)).trans_eq
  change fastBridgeConstant*((∫⁻ z,ENNReal.ofReal (shortfallObservation k aw nw Fw z) ∂area)+ENNReal.ofReal (growthBase k^(-(1/10:ℝ)*(N:ℝ))))*ENNReal.ofReal ((∫ z,shortfallObservation k ah nh Fh z ∂area)/(h/2))=_
  rw [←ofReal_integral_eq_lintegral_ofReal (f := shortfallObservation k aw nw Fw) hiW (Eventually.of_forall hW0),
    ←ENNReal.ofReal_add hiW0 hd0]
  conv_lhs => rw [show fastBridgeConstant=ENNReal.ofReal bridgeRealConstant from (ENNReal.ofReal_toReal fastBridgeConstant_ne_top).symm]
  rw [
    ←ENNReal.ofReal_mul bridgeRealConstant_nonneg,←ENNReal.ofReal_mul (mul_nonneg bridgeRealConstant_nonneg (add_nonneg hiW0 hd0))]
end StandardMapEntropy

end OAI
