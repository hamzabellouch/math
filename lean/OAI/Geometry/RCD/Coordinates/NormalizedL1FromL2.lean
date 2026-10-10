import OAI.Geometry.RCD.Sobolev.LocalScaledGammaL2

namespace OAI

/-! # Vanishing normalized quadratic error controls normalized absolute error -/

open Set Filter MeasureTheory
open scoped Topology
noncomputable section
namespace RegularPointCoordinates

theorem normalized_l1_tendsto_of_l2 {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (Ω : ℕ → Set X) (c : ℕ → ℝ) (hc : ∀ k, 0 ≤ c k)
    (hmass : ∀ k, c k*μ.real (Ω k) ≤ 1) (f : ℕ → X → ℝ)
    (hf : ∀ k, IntegrableOn (f k) (Ω k) μ)
    (hf2 : ∀ᶠ k in atTop, IntegrableOn (fun x => (f k x)^2) (Ω k) μ)
    (hfin : ∀ k, μ (Ω k) ≠ ⊤)
    (hlim : Tendsto (fun k => c k*∫ x in Ω k, (f k x)^2 ∂μ) atTop (𝓝 0)) :
    Tendsto (fun k => c k*∫ x in Ω k, |f k x| ∂μ) atTop (𝓝 0) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Eventually.of_forall (fun k => ha.trans_le
      (mul_nonneg (hc k) (integral_nonneg (fun _ => abs_nonneg _))))
  · intro b hb
    let δ := b/2
    have hδ : 0 < δ := half_pos hb
    have he : ∀ x : ℝ, |x| ≤ δ+δ⁻¹*x^2 := by
      intro x
      calc
        |x| ≤ (δ^2+x^2)/δ := (le_div_iff₀ hδ).mpr (by
          nlinarith [sq_nonneg (|x|-δ),sq_abs x,mul_nonneg (abs_nonneg x) hδ.le])
        _ = δ+δ⁻¹*x^2 := by field_simp
    filter_upwards [hf2,hlim.eventually (Iio_mem_nhds (sq_pos_of_pos hδ))] with k hk hs
    have hi0 : IntegrableOn (fun _ : X => δ) (Ω k) μ := integrableOn_const (hfin k)
    have hi := integral_mono_ae (hf k).abs
      (hi0.add (hk.const_mul δ⁻¹))
      (Eventually.of_forall (fun x => he (f k x)))
    simp only [Pi.add_apply] at hi
    rw [integral_add hi0 (hk.const_mul δ⁻¹),
      integral_const,integral_const_mul] at hi
    simp only [measureReal_restrict_apply_univ,smul_eq_mul] at hi
    have hmul := mul_le_mul_of_nonneg_left hi (hc k)
    have hsmall : δ⁻¹*(c k*∫ x in Ω k, (f k x)^2 ∂μ) < δ := by
      calc
        _ < δ⁻¹*δ^2 := mul_lt_mul_of_pos_left hs (inv_pos.mpr hδ)
        _ = δ := by field_simp
    have hm := mul_le_mul_of_nonneg_left (hmass k) hδ.le
    dsimp only [δ] at hmul hsmall hm ⊢
    nlinarith

end RegularPointCoordinates

end

end OAI
