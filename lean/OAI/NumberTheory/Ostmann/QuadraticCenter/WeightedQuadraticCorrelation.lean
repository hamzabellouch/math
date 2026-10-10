import OAI.NumberTheory.Ostmann.Quadratic.QuadraticCorrelationExpansion

namespace OAI

/-! # A scalar weight commutes with the exact quadratic normalization -/

namespace Ostmann

open scoped BigOperators ComplexConjugate

theorem weighted_normalized_quadratic_pair_bound {ι κ υ : Type*}
    (S : Finset ι) (W : Finset κ) (V : Finset υ) (σ : ι → ℝ) (ρ : ι → ℂ)
    (F : κ → ι → ℂ) (G : υ → ι → ℂ) (R d e v B : ℝ)
    (hR : 0 < R) (hd : 0 < d) (he : 0 < e) (hv : 0 < v)
    (hσ : ∀ s ∈ S, 0 < σ s)
    (hB : ∀ w ∈ W, ∀ z ∈ V, ‖∑ s ∈ S, ρ s * (F w s * conj (G z s))‖ ≤ B) :
    ‖∑ s ∈ S, ρ s *
      ((((Real.sqrt (R * d / (σ s * v)) : ℝ) : ℂ)⁻¹ * ∑ w ∈ W, F w s) *
        conj (((Real.sqrt (R * e / (σ s * v)) : ℝ) : ℂ)⁻¹ * ∑ z ∈ V, G z s) / (σ s : ℂ))‖ ≤
      v / (R * Real.sqrt (d * e)) * ((W.card : ℝ) * V.card * B) := by
  have hb := normalized_quadratic_pair_bound S W V σ (fun w s => ρ s * F w s) G
    R d e v B hR hd he hv hσ (by
      intro w hw z hz
      convert hB w hw z hz using 1
      congr 1
      apply Finset.sum_congr rfl
      intro s hs
      ring)
  convert hb using 1
  congr 1
  apply Finset.sum_congr rfl
  intro s hs
  rw [← Finset.mul_sum]
  ring

end Ostmann

end OAI
