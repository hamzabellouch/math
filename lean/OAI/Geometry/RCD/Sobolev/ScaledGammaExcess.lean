import OAI.Geometry.RCD.Sobolev.PositiveEnergyExcess
import OAI.Geometry.RCD.Sobolev.SobolevLevelChain

namespace OAI

/-! # The actual harmonic gradient excess vanishes under strong recovery -/

open Set Filter MeasureTheory
open scoped Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem scaled_gamma_excess_tendsto (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)
    (Ω : ℕ → Set X) [∀ k, IsFiniteMeasure (μ.restrict (Ω k))]
    (r c : ℕ → ℝ) (hr : ∀ k, 0<r k) (hc : ∀ k, 0≤c k)
    (hmass : ∀ k, c k*μ.real (Ω k)≤1)
    {M : ℝ} (hM : 0≤M) (w q : ℕ → SobolevSpace μ hQ)
    (hw : ∀ᶠ k in atTop, ∀ᵐ x ∂μ.restrict (Ω k), r k^2*localGamma μ hQ (w k) (w k) x≤M^2)
    (hq : ∀ δ : ℝ, 0<δ → ∀ᶠ k in atTop,
      ∀ᵐ x ∂μ.restrict (Ω k), r k^2*localGamma μ hQ (q k) (q k) x≤(1+δ)^2)
    (hstrong : Tendsto (fun k => c k*r k^2*∫ x in Ω k,
      localGamma μ hQ (w k-q k) (w k-q k) x ∂μ) atTop (𝓝 0)) :
    Tendsto (fun k => c k*∫ x in Ω k,
      (max (r k^2*localGamma μ hQ (w k) (w k) x-1) 0)^2 ∂μ) atTop (𝓝 0) := by
  let f := fun k x => r k^2*localGamma μ hQ (w k) (w k) x
  let g := fun k x => r k^2*localGamma μ hQ (q k) (q k) x
  have hq2 : ∀ᶠ k in atTop, ∀ᵐ x ∂μ.restrict (Ω k),
      r k^2*localGamma μ hQ (q k) (q k) x≤(2:ℝ)^2 := by
    simpa only [show (1:ℝ)+1=2 by norm_num] using hq 1 zero_lt_one
  have hwm : ∀ᶠ k in atTop, MemLp (f k) 2 (μ.restrict (Ω k)) := by
    filter_upwards [hw] with k hk
    apply MemLp.of_bound (((localGamma_memL1 μ hQ (w k) (w k)).aestronglyMeasurable.const_mul (r k^2)).restrict) (M^2)
    filter_upwards [hk,ae_restrict_of_ae (localGamma_self μ hQ (w k))] with x hx he
    change ‖r k^2*localGamma μ hQ (w k) (w k) x‖≤M^2
    rw [Real.norm_eq_abs,abs_of_nonneg (by rw [he]; positivity)]
    exact hx
  have hqm : ∀ᶠ k in atTop, MemLp (g k) 2 (μ.restrict (Ω k)) := by
    filter_upwards [hq2] with k hk
    apply MemLp.of_bound (((localGamma_memL1 μ hQ (q k) (q k)).aestronglyMeasurable.const_mul (r k^2)).restrict) ((2:ℝ)^2)
    filter_upwards [hk,ae_restrict_of_ae (localGamma_self μ hQ (q k))] with x hx he
    change ‖r k^2*localGamma μ hQ (q k) (q k) x‖≤(2:ℝ)^2
    rw [Real.norm_eq_abs,abs_of_nonneg (by rw [he]; positivity)]
    exact hx
  have hf : ∀ᶠ k in atTop, IntegrableOn (fun x => (max (f k x-1) 0)^2) (Ω k) μ := by
    filter_upwards [hwm] with k hk
    exact ((upperLevelPart_lipschitz 1).comp_memLp (upperLevelPart_zero zero_le_one) hk).integrable_sq
  have hd : ∀ᶠ k in atTop, IntegrableOn (fun x => (f k x-g k x)^2) (Ω k) μ := by
    filter_upwards [hwm,hqm] with k hk hj
    exact (hk.sub hj).integrable_sq
  have hclose := local_scaled_gamma_l2_tendsto μ hQ Ω r c hr hc hM (by norm_num : (0:ℝ)≤2) w q hw hq2 hstrong
  have hclose' : Tendsto (fun k => c k*∫ x in Ω k, (f k x-g k x)^2 ∂μ) atTop (𝓝 0) := by
    have he : ∀ k x, f k x-g k x=r k^2*(localGamma μ hQ (w k) (w k) x-localGamma μ hQ (q k) (q k) x) := by
      intro k x
      dsimp only [f,g]
      ring
    simp_rw [he]
    exact hclose
  exact positive_energy_excess_tendsto μ Ω c hc hmass f g hf hd hclose' hq

end RegularPointCoordinates

end

end OAI
