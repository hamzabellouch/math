import OAI.Geometry.RCD.Sobolev.LocalScaledGammaL2

namespace OAI

/-! # Strong energy-density comparison transfers a sharp upper bound -/

open Set Filter MeasureTheory
open scoped Topology
noncomputable section
namespace RegularPointCoordinates

theorem square_positive_excess_le {a b δ : ℝ} (hδ : 0≤δ) (hδ1 : δ≤1)
    (hb : b≤(1+δ)^2) : (max (a-1) 0)^2≤2*(a-b)^2+18*δ^2 := by
  have hmax : max (a-1) 0≤|a-b|+3*δ := by
    apply max_le
    · nlinarith [le_abs_self (a-b),mul_nonneg hδ (sub_nonneg.mpr hδ1)]
    · positivity
  have hs := pow_le_pow_left₀ (le_max_right (a-1) 0) hmax 2
  nlinarith [sq_nonneg (|a-b|-3*δ),sq_abs (a-b)]

theorem positive_energy_excess_tendsto {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (Ω : ℕ → Set X) [∀ k, IsFiniteMeasure (μ.restrict (Ω k))]
    (c : ℕ → ℝ) (hc : ∀ k, 0≤c k) (hmass : ∀ k, c k*μ.real (Ω k)≤1)
    (f g : ℕ → X → ℝ)
    (hf : ∀ᶠ k in atTop, IntegrableOn (fun x => (max (f k x-1) 0)^2) (Ω k) μ)
    (hd : ∀ᶠ k in atTop, IntegrableOn (fun x => (f k x-g k x)^2) (Ω k) μ)
    (hclose : Tendsto (fun k => c k*∫ x in Ω k, (f k x-g k x)^2 ∂μ) atTop (𝓝 0))
    (hupper : ∀ δ : ℝ, 0<δ → ∀ᶠ k in atTop,
      ∀ᵐ x ∂μ.restrict (Ω k), g k x≤(1+δ)^2) :
    Tendsto (fun k => c k*∫ x in Ω k, (max (f k x-1) 0)^2 ∂μ) atTop (𝓝 0) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Eventually.of_forall fun k => ha.trans_le
      (mul_nonneg (hc k) (integral_nonneg fun x => sq_nonneg _))
  · intro b hb
    let δ := min 1 (Real.sqrt b/10)
    have hδ : 0<δ := lt_min zero_lt_one (div_pos (Real.sqrt_pos.mpr hb) (by norm_num))
    have hδ1 : δ≤1 := min_le_left _ _
    have hs : δ^2≤(Real.sqrt b/10)^2 :=
      pow_le_pow_left₀ hδ.le (min_le_right _ _) 2
    have hδb : 18*δ^2<b/2 := by nlinarith [Real.sq_sqrt hb.le]
    filter_upwards [hupper δ hδ,hclose.eventually (eventually_lt_nhds (show 0<b/4 by linarith)),hf,hd]
      with k hk hdk hfk hdki
    have hip := integral_mono_ae hfk (hdki.const_mul 2 |>.add (integrable_const (18*δ^2)))
      (hk.mono fun x hx => square_positive_excess_le hδ.le hδ1 hx)
    change (∫ x in Ω k, (max (f k x-1) 0)^2 ∂μ)≤
      ∫ x in Ω k, (2*(f k x-g k x)^2+18*δ^2) ∂μ at hip
    rw [integral_add (hdki.const_mul 2) (integrable_const (18*δ^2)),integral_const_mul,
      integral_const] at hip
    have hip' : (∫ x in Ω k, (max (f k x-1) 0)^2 ∂μ)≤
        2*(∫ x in Ω k, (f k x-g k x)^2 ∂μ)+18*δ^2*μ.real (Ω k) := by
      simpa only [smul_eq_mul,Measure.real,Measure.restrict_apply_univ,mul_comm] using hip
    have hm := mul_le_mul_of_nonneg_left (hmass k) (show 0≤18*δ^2 by positivity)
    have hh := mul_le_mul_of_nonneg_left hip' (hc k)
    nlinarith

end RegularPointCoordinates

end

end OAI
