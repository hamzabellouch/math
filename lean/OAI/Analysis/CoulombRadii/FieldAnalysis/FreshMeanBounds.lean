import Mathlib
import OAI.Analysis.CoulombRadii.FieldAnalysis.PoissonInterior

namespace OAI

section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
noncomputable section
namespace NeutralAtom

lemma field_lower_of_gap {v G q L : ℝ} (hG : 0≤G) (hq : 0<q) (hL : 0≤L)
    (hgood : G≤q → L≤v) : L-(L/q)*G-max (-v) 0≤v := by
  by_cases hg : G≤q
  · have hp : 0≤(L/q)*G := mul_nonneg (div_nonneg hL hq.le) hG
    linarith [hgood hg,le_max_right (-v) 0]
  · have hg : q≤G := (lt_of_not_ge hg).le
    have H := mul_le_mul_of_nonneg_left hg (div_nonneg hL hq.le)
    rw [div_mul_cancel₀ L hq.ne'] at H
    linarith [le_max_left (-v) 0]

lemma field_upper_of_gap {v G q U C : ℝ} (hG : 0≤G) (hq : 0<q)
    (hU : 0≤U) (hC : 0≤C) (hcap : v≤C) (hgood : G≤q → v≤U) :
    v≤U+(C/q)*G := by
  by_cases hg : G≤q
  · have hp : 0≤(C/q)*G := mul_nonneg (div_nonneg hC hq.le) hG
    linarith [hgood hg]
  · have hg : q≤G := (lt_of_not_ge hg).le
    have H := mul_le_mul_of_nonneg_left hg (div_nonneg hC hq.le)
    rw [div_mul_cancel₀ C hq.ne'] at H
    linarith

lemma weighted_field_integrable {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {w v : X → ℝ} (hw : Integrable w μ) (hw0 : ∀ᵐ x ∂μ, 0≤w x)
    (hv : AEStronglyMeasurable v μ) {C : ℝ} (hC : 0≤C)
    (hcap : ∀ᵐ x ∂μ, w x≠0 → v x≤C)
    (hneg : Integrable (fun x => w x*max (-v x) 0) μ) :
    Integrable (fun x => w x*v x) μ := by
  apply ((hw.const_mul C).add (hneg.const_mul 2)).mono' (hw.aestronglyMeasurable.mul hv)
  filter_upwards [hw0,hcap] with x hw hx
  change ‖w x*v x‖≤C*w x+2*(w x*max (-v x) 0)
  rw [norm_mul,Real.norm_of_nonneg hw,Real.norm_eq_abs]
  by_cases hz : w x=0
  · simp [hz]
  have h : |v x|≤C+2*max (-v x) 0 := by
    rw [abs_le]
    constructor
    · linarith only [hC,le_max_left (-v x) 0,le_max_right (-v x) 0]
    · linarith only [hx hz,le_max_right (-v x) 0]
  nlinarith [mul_le_mul_of_nonneg_left h hw]

lemma weighted_field_mean_lower {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {w v G : X → ℝ} (hw : Integrable w μ) (hw0 : ∀ᵐ x ∂μ, 0≤w x)
    (hv : Integrable (fun x => w x*v x) μ)
    (hGi : Integrable (fun x => w x*G x) μ)
    (hneg : Integrable (fun x => w x*max (-v x) 0) μ)
    {q L : ℝ} (hq : 0<q) (hL : 0≤L) (hG : ∀ᵐ x ∂μ, 0≤G x)
    (hgood : ∀ᵐ x ∂μ, w x≠0 → G x≤q → L≤v x) :
    L*(∫ x,w x ∂μ)-(L/q)*(∫ x,w x*G x ∂μ)-
      (∫ x,w x*max (-v x) 0 ∂μ)≤∫ x,w x*v x ∂μ := by
  have hi := ((hw.const_mul L).sub (hGi.const_mul (L/q))).sub hneg
  have H := integral_mono_ae hi hv (show ∀ᵐ x ∂μ,
      L*w x-(L/q)*(w x*G x)-w x*max (-v x) 0≤w x*v x from ?_)
  · have he := integral_sub ((hw.const_mul L).sub (hGi.const_mul (L/q))) hneg
    have he' := integral_sub (hw.const_mul L) (hGi.const_mul (L/q))
    simp only [Pi.sub_apply] at he he' H
    rw [he,he',integral_const_mul,integral_const_mul] at H
    exact H
  · filter_upwards [hw0,hG,hgood] with x hw hg hh
    by_cases hz : w x=0
    · simp [hz]
    nlinarith [mul_le_mul_of_nonneg_left (field_lower_of_gap hg hq hL (hh hz)) hw]

lemma weighted_field_mean_upper {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {w v G : X → ℝ} (hw : Integrable w μ) (hw0 : ∀ᵐ x ∂μ, 0≤w x)
    (hv : Integrable (fun x => w x*v x) μ)
    (hGi : Integrable (fun x => w x*G x) μ)
    {q U C : ℝ} (hq : 0<q) (hU : 0≤U) (hC : 0≤C)
    (hG : ∀ᵐ x ∂μ, 0≤G x) (hcap : ∀ᵐ x ∂μ, w x≠0 → v x≤C)
    (hgood : ∀ᵐ x ∂μ, w x≠0 → G x≤q → v x≤U) :
    (∫ x,w x*v x ∂μ)≤U*(∫ x,w x ∂μ)+(C/q)*(∫ x,w x*G x ∂μ) := by
  have hi := (hw.const_mul U).add (hGi.const_mul (C/q))
  have H := integral_mono_ae hv hi (show ∀ᵐ x ∂μ,
      w x*v x≤U*w x+(C/q)*(w x*G x) from ?_)
  · simpa only [Pi.add_apply,integral_add (hw.const_mul U) (hGi.const_mul (C/q)),
      integral_const_mul] using H
  · filter_upwards [hw0,hG,hcap,hgood] with x hw hg hc hh
    by_cases hz : w x=0
    · simp [hz]
    nlinarith [mul_le_mul_of_nonneg_left (field_upper_of_gap hg hq hU hC (hc hz) (hh hz)) hw]
end NeutralAtom
end

end

end OAI
