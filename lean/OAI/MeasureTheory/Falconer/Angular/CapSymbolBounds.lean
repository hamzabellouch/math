import OAI.MeasureTheory.Falconer.Angular.QuantitativeCaps
import OAI.MeasureTheory.Falconer.Angular.CapAmplitudeDerivatives
import OAI.MeasureTheory.Falconer.Angular.CapSupport

namespace OAI

/-!
# The derivative budget of an actual localized endpoint pair

The cap cutoff has scale delta, while each endpoint symbol has scale D.
When D dominates the inverse radius, the full amplitude satisfies the
budget required by the proved nonstationary sphere estimate. The compact
chart interval is deduced from cap support.
-/

namespace Falconer
open Set
open scoped ContDiff

theorem capPairAmplitude_supported_derivatives {n : ℕ}
    (e : Space (n+2) ≃ₗᵢ[ℝ] Space (n+2)) (η : Sphere (n+2) → ℝ)
    (b b' : Space (n+2) → Sphere (n+2) → ℂ)
    (x : Space (n+2) × Space (n+2)) (m : ℕ)
    {δ H B B' D : ℝ} (hδ : 0 < δ) (hsmall : δ ≤ 1/2)
    (hH : 0 ≤ H) (hB : 0 ≤ B) (hB' : 0 ≤ B') (hD : 0 ≤ D) (hscale : δ⁻¹ ≤ D)
    (hcap : ∀ z, η z ≠ 0 → ‖(z : Space (n+2))-e (chartPole n)‖ ≤ δ)
    (hη : ∀ y : Space n, ContDiff ℝ ∞ (rotatedChartAmplitude e (fun w => (η w : ℂ)) y))
    (hb : ∀ y : Space n, ContDiff ℝ ∞ (rotatedChartAmplitude e (b x.1) y))
    (hb' : ∀ y : Space n, ContDiff ℝ ∞ (rotatedChartAmplitude e (b' x.2) y))
    (hηb : ∀ k ≤ m, ∀ y : Space n, ‖y‖ ≤ 1 → ∀ u ∈ Icc (-1 : ℝ) 1,
      ‖iteratedDeriv k (rotatedChartAmplitude e (fun w => (η w : ℂ)) y) u‖ ≤ H*(δ⁻¹)^k)
    (hbb : ∀ k ≤ m, ∀ y : Space n, ‖y‖ ≤ 1 → ∀ u ∈ Icc (-1 : ℝ) 1,
      ‖iteratedDeriv k (rotatedChartAmplitude e (b x.1) y) u‖ ≤ B*D^k)
    (hb'b : ∀ k ≤ m, ∀ y : Space n, ‖y‖ ≤ 1 → ∀ u ∈ Icc (-1 : ℝ) 1,
      ‖iteratedDeriv k (rotatedChartAmplitude e (b' x.2) y) u‖ ≤ B'*D^k) :
    ∀ k ≤ m, ∀ y : Space n, ‖y‖ ≤ 1 →
      ∀ u ∈ tsupport (rotatedChartAmplitude e (capPairAmplitude η b b' x) y),
      ‖iteratedDeriv k (rotatedChartAmplitude e (capPairAmplitude η b b' x) y) u‖ ≤
        (4^m*H*B*B')*D^k := by
  have hpcap := capPairAmplitude_cap_support η b b' (e (chartPole n)) δ hcap x
  have hs := (cap_amplitude_chart_support e (capPairAmplitude η b b' x) hδ.le hsmall hpcap).2.2
  intro k hk y hy u hu
  have hui := hs y hu
  apply capPairAmplitude_chart_derivatives e η b b' x y m (hη y) (hb y) (hb' y)
    hH hB hB' hD u (fun j hj => ?_) (fun j hj => hbb j hj y hy u hui)
    (fun j hj => hb'b j hj y hy u hui) k hk
  exact (hηb j hj y hy u hui).trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (inv_nonneg.mpr hδ.le) hscale j) hH)

end Falconer

end OAI
