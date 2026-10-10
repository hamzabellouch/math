import Mathlib
import OAI.Geometry.SmoothYau.Smoothness.HessianJet
import OAI.Geometry.SmoothYau.Smoothness.PolynomialFiniteWave

namespace OAI

noncomputable section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
namespace YauCounterexamples
variable {E X σ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace X] [Fintype σ] [DecidableEq σ]

theorem generated_phase_gaussian (T : E →L[ℝ] (σ → ℝ))
    (g : X → σ → σ → (σ → ℝ) → ℂ)
    (hg : ∀ p i j, ContDiff ℝ ∞ (g p i j))
    (hg0 : ∀ p i j, g p i j 0 = if i = j then 1 else 0)
    (hdg0 : ∀ p i j, fderiv ℝ (g p i j) 0 = 0)
    (s : X → ℂ) (hs : Continuous s)
    (z : X → σ → ℂ) (hz : ∀ i, Continuous (fun p => z p i)) (hz₀ : ∀ p, z p ≠ 0)
    (Q : X → σ → σ → ℂ) (hQ : ∀ p i j, Q p i j = Q p j i)
    (hQc : ∀ i j, Continuous (fun p => Q p i j))
    (hnull : ∀ p, ∑ i, z p i * z p i = -1)
    (hQz : ∀ p k, ∑ i, z p i * Q p k i = 0)
    (L : ℕ) (hL : 2 ≤ L)
    (hgj : ∀ i j k, k < L → Continuous (fun p => iteratedFDeriv ℝ k (g p i j) 0))
    (φ : X → E → ℝ) (hφ : ∀ p, ContDiff ℝ ∞ (φ p))
    (hφ2 : Continuous (fun q : X × E => iteratedFDeriv ℝ 2 (φ q.1) q.2))
    (hs0 : ∀ p, (s p).re = φ p 0)
    {K : Set X} (hK : IsCompact K) (δ : X → ℝ) {c : ℝ} (hc : 0 < c)
    (hlinear : ∀ p ∈ K, ∀ v,
      (∑ i, (T v i : ℂ)*z p i).re - fderiv ℝ (φ p) 0 v ≤ δ p*‖v‖)
    (hgap : ∀ p ∈ K, ∀ v,
      (∑ i, ∑ j, (T v i : ℂ)*(T v j : ℂ)*Q p j i).re -
        fderiv ℝ (fderiv ℝ (φ p)) 0 v v ≤ -4*c*‖v‖^2) :
    ∃ r > 0, ∀ p ∈ K, ∀ x ∈ Metric.ball (0 : E) r,
      (realPolyEval (smoothPhasePolynomial (g p) (s p) (z p) (Q p) L) (T x)).re -
        φ p x ≤ δ p*‖x‖-c*‖x‖^2 := by
  apply compact_polynomial_gaussian T _
    (smoothPhasePolynomial_coeffContinuous g s hs z hz hz₀ Q hQc L hgj) L
    (fun p => smoothPhasePolynomial_degree (g p) (hg p) (hg0 p) (hdg0 p)
      (s p) (z p) (Q p) (hz₀ p) (hQ p) (hnull p) (hQz p) L hL)
    φ hφ hφ2 s z Q hs0 hQ
    (fun p => (smoothPhasePolynomial_spec (g p) (hg p) (hg0 p) (hdg0 p)
      (s p) (z p) (Q p) (hz₀ p) (hQ p) (hnull p) (hQz p) L hL).1)
    hK δ hc hlinear hgap

end YauCounterexamples

end

end OAI
