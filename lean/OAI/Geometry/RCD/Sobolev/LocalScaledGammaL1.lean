import OAI.Geometry.RCD.Coordinates.NormalizedL1FromL2

namespace OAI

/-! # Strong gradient recovery identifies the actual local energy in L1 -/

open Set Filter MeasureTheory
open scoped Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem local_scaled_gamma_l1_tendsto (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)
    (Ω : ℕ → Set X) (hfin : ∀ k, μ (Ω k) ≠ ⊤)
    (r c : ℕ → ℝ) (hr : ∀ k, 0 < r k) (hc : ∀ k, 0 ≤ c k)
    (hmass : ∀ k, c k*μ.real (Ω k) ≤ 1)
    {M Q : ℝ} (hM : 0 ≤ M) (hQ0 : 0 ≤ Q) (f g : ℕ → SobolevSpace μ hQ)
    (hf : ∀ᶠ k in atTop, ∀ᵐ x ∂μ.restrict (Ω k), r k^2*localGamma μ hQ (f k) (f k) x ≤ M^2)
    (hg : ∀ᶠ k in atTop, ∀ᵐ x ∂μ.restrict (Ω k), r k^2*localGamma μ hQ (g k) (g k) x ≤ Q^2)
    (hlim : Tendsto (fun k => c k*r k^2*∫ x in Ω k,
      localGamma μ hQ (f k-g k) (f k-g k) x ∂μ) atTop (𝓝 0)) :
    Tendsto (fun k => c k*∫ x in Ω k,
      |r k^2*(localGamma μ hQ (f k) (f k) x-localGamma μ hQ (g k) (g k) x)| ∂μ)
      atTop (𝓝 0) := by
  let F := fun k x => r k^2*(localGamma μ hQ (f k) (f k) x-localGamma μ hQ (g k) (g k) x)
  have hi (k : ℕ) : IntegrableOn (F k) (Ω k) μ :=
    (((localGamma_memL1 μ hQ (f k) (f k)).sub
      (localGamma_memL1 μ hQ (g k) (g k))).const_mul (r k^2)).integrableOn
  have hi2 : ∀ᶠ k in atTop, IntegrableOn (fun x => (F k x)^2) (Ω k) μ := by
    filter_upwards [hf,hg] with k hfk hgk
    let : IsFiniteMeasure (μ.restrict (Ω k)) :=
      ⟨by simpa only [Measure.restrict_apply_univ] using (hfin k).lt_top⟩
    have hm : MemLp (F k) 2 (μ.restrict (Ω k)) := by
      apply MemLp.of_bound (hi k).aestronglyMeasurable (M^2+Q^2)
      filter_upwards [hfk,hgk,ae_restrict_of_ae (localGamma_self μ hQ (f k)),
        ae_restrict_of_ae (localGamma_self μ hQ (g k))] with x hx hy hxf hyf
      have hfx : 0 ≤ r k^2*localGamma μ hQ (f k) (f k) x := by rw [hxf]; positivity
      have hgx : 0 ≤ r k^2*localGamma μ hQ (g k) (g k) x := by rw [hyf]; positivity
      change ‖r k^2*(localGamma μ hQ (f k) (f k) x-localGamma μ hQ (g k) (g k) x)‖ ≤ M^2+Q^2
      rw [Real.norm_eq_abs,abs_le]
      constructor <;> nlinarith [sq_nonneg M,sq_nonneg Q]
    exact hm.integrable_sq
  exact normalized_l1_tendsto_of_l2 μ Ω c hc hmass F hi hi2 hfin
    (local_scaled_gamma_l2_tendsto μ hQ Ω r c hr hc hM hQ0 f g hf hg hlim)

end RegularPointCoordinates

end

end OAI
