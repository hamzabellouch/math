import OAI.Probability.SLE.LoewnerCharts

namespace OAI

/-! The classical published normal-family input, restricted to the interior
normalization used in the ribbon proof.

P. L. Duren, *Univalent Functions*, Springer, 1983, §1.3, unnumbered
theorem on p. 9: compactness of the normalized schlicht class. The
half-plane specialization below follows by disk automorphisms and affine
normalization, using the growth/distortion bounds in §2.3. The moving
normalization points stay on one compact semicircle, their images are
bounded, and the derivative norms stay bounded above and away from zero.
The nonvanishing derivative of the univalent limit is the local mapping
property in §1.2, p. 5.

This is an explicit hypothesis, not an axiom. It contains no boundary
guide, SLE passage, sausage estimate, or uniformity over stopped pasts.
-/

noncomputable section
open Set Filter Metric
open scoped Topology

namespace SLEExactGauge

/-- The minimal nondegenerate univalent normal-family consequence used
at the ribbon waypoint. -/
def PublishedHalfPlaneUnivalentCompactness : Prop :=
  ∀ (Fₙ : ℕ → ℂ → ℂ) (zₙ : ℕ → ℂ) (s m M : ℝ),
    0 < s → 0 < m →
    (∀ n, DifferentiableOn ℂ (Fₙ n) upperHalfPlane) →
    (∀ n, InjOn (Fₙ n) upperHalfPlane) →
    (∀ n, ‖zₙ n‖ = 1 ∧ s ≤ (zₙ n).im) →
    (∀ n, ‖Fₙ n (zₙ n)‖ ≤ M) →
    (∀ n, m ≤ ‖deriv (Fₙ n) (zₙ n)‖ ∧ ‖deriv (Fₙ n) (zₙ n)‖ ≤ M) →
    ∃ (φ : ℕ → ℕ) (F : ℂ → ℂ), StrictMono φ ∧
      DifferentiableOn ℂ F upperHalfPlane ∧ InjOn F upperHalfPlane ∧
      (∀ z ∈ upperHalfPlane, deriv F z ≠ 0) ∧
      TendstoLocallyUniformlyOn (fun n => Fₙ (φ n)) F atTop upperHalfPlane

end SLEExactGauge

end

end OAI
