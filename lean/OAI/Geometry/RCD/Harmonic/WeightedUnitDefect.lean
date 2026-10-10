import OAI.Geometry.RCD.Sobolev.PositiveEnergyExcess

namespace OAI

/-! # A sharp weighted upper bound and lower integral control give L1 convergence -/

open Set Filter MeasureTheory
open scoped Topology
noncomputable section
namespace RegularPointCoordinates

theorem weighted_unit_defect_tendsto {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (Ω : ℕ → Set X) (c : ℕ → ℝ) (hc : ∀ k, 0≤c k)
    (f g : ℕ → X → ℝ) (hf : ∀ k, IntegrableOn (f k) (Ω k) μ)
    (hfg : ∀ k, IntegrableOn (fun x => f k x*g k x) (Ω k) μ)
    (hf0 : ∀ k, ∀ᵐ x ∂μ.restrict (Ω k), 0≤f k x)
    (hmass : ∀ k, c k*(∫ x in Ω k, f k x ∂μ)≤1)
    {I : ℝ} (hlim : Tendsto (fun k => c k*∫ x in Ω k, f k x ∂μ) atTop (𝓝 I))
    (hlower : ∀ δ : ℝ, 0<δ → ∀ᶠ k in atTop,
      I-δ≤c k*∫ x in Ω k, f k x*g k x ∂μ)
    (hupper : ∀ δ : ℝ, 0<δ → ∀ᶠ k in atTop, ∀ᵐ x ∂μ.restrict (Ω k),
      f k x*g k x≤(1+δ)*f k x) :
    Tendsto (fun k => c k*∫ x in Ω k, f k x*|g k x-1| ∂μ) atTop (𝓝 0) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    exact Eventually.of_forall (fun k => ha.trans_le (mul_nonneg (hc k)
      (integral_nonneg_of_ae (by
        filter_upwards [hf0 k] with x hx
        exact mul_nonneg hx (abs_nonneg _)))))
  · intro b hb
    let δ := b/5
    have hδ : 0<δ := by dsimp only [δ]; positivity
    filter_upwards [hlower δ hδ,hupper δ hδ,hlim.eventually (eventually_lt_nhds (show I<I+δ by linarith))]
      with k hklo hkup hkm
    have hid : IntegrableOn (fun x => f k x*|g k x-1|) (Ω k) μ := by
      apply ((hfg k).sub (hf k)).abs.congr
      filter_upwards [hf0 k] with x hx
      change |f k x*g k x-f k x|=f k x*|g k x-1|
      rw [show f k x*g k x-f k x=f k x*(g k x-1) by ring,abs_mul,abs_of_nonneg hx]
    have hir : IntegrableOn (fun x => (2*δ+1)*f k x-f k x*g k x) (Ω k) μ :=
      ((hf k).const_mul _).sub (hfg k)
    have hi := integral_mono_ae hid hir (by
      filter_upwards [hf0 k,hkup] with x hx hu
      by_cases hg : 0≤g k x-1
      · rw [abs_of_nonneg hg]
        nlinarith
      · rw [abs_of_neg (lt_of_not_ge hg)]
        nlinarith [mul_nonneg hδ.le hx])
    rw [integral_sub ((hf k).const_mul _) (hfg k),integral_const_mul] at hi
    have hi' := mul_le_mul_of_nonneg_left hi (hc k)
    have hm := hmass k
    have hnonneg : 0≤c k*∫ x in Ω k, f k x ∂μ :=
      mul_nonneg (hc k) (integral_nonneg_of_ae (hf0 k))
    have hδm := mul_le_mul_of_nonneg_left hm (show 0≤2*δ by positivity)
    dsimp only [δ] at *
    nlinarith

end RegularPointCoordinates

end

end OAI
