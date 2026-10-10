import OAI.Geometry.RCD.Sobolev.HarmonicEnergyTailCover

namespace OAI

/-! # Vanishing energy tails give sharp bounds for harmonic sequences -/

open Set Metric Filter MeasureTheory
open scoped Topology NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.harmonic_energy_tail_sequence {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2≤n)
    (p : ℕ → X) (r : ℕ → ℝ) (hr : ∀ k, 0 < r k)
    (hcurv : ∀ k, -1≤K*(5*r k)^2)
    (w : ℕ → SobolevSpace (hausdorff n X) hX.quadratic)
    (hw : ∀ k, IsSobolevHarmonicOn (hausdorff n X) hX.quadratic (ball (p k) (5*r k)) (w k))
    {B : ℝ} (hB : 0≤B)
    (hgrad : ∀ k, ∀ᵐ x ∂(hausdorff n X).restrict (ball (p k) (4*r k)),
      r k^2*localGamma (hausdorff n X) hX.quadratic (w k) (w k) x≤B)
    (hlim : Tendsto (fun k => ((hausdorff n X).real (ball (p k) (5*r k)))⁻¹*
      ∫ x in ball (p k) (4*r k),
        (max (r k^2*localGamma (hausdorff n X) hX.quadratic (w k) (w k) x-1) 0)^2
        ∂hausdorff n X) atTop (𝓝 0)) :
    ∀ β : ℝ, 0<β → ∀ᶠ k in atTop,
      ∀ᵐ x ∂(hausdorff n X).restrict (ball (p k) (3*r k)),
        r k^2*localGamma (hausdorff n X) hX.quadratic (w k) (w k) x≤1+β := by
  intro β hβ
  obtain ⟨δ,hδ,hbound⟩ := hX.harmonic_energy_tail_inner_bound hn β hβ
  filter_upwards [hlim.eventually (eventually_lt_nhds hδ)] with k hk
  have hm : 0 < (hausdorff n X).real (ball (p k) (5*r k)) :=
    ENNReal.toReal_pos (hX.fullSupport _ _ (mul_pos (by norm_num) (hr k))).ne'
      (hX.finiteOnBounded _ isBounded_ball).ne
  let L : ℝ≥0 := ⟨Real.sqrt (B/(r k)^2),Real.sqrt_nonneg _⟩
  apply hbound (p k) (r k) (hr k) (hcurv k) (w k) L (hw k)
  · filter_upwards [hgrad k] with x hx
    change localGamma (hausdorff n X) hX.quadratic (w k) (w k) x≤(Real.sqrt (B/(r k)^2))^2
    rw [Real.sq_sqrt (div_nonneg hB (sq_nonneg _))]
    exact (le_div_iff₀ (sq_pos_of_pos (hr k))).mpr (by simpa only [mul_comm] using hx)
  · rw [← div_eq_inv_mul] at hk
    exact ((div_lt_iff₀ hm).mp hk).le

end RegularPointCoordinates

end

end OAI
