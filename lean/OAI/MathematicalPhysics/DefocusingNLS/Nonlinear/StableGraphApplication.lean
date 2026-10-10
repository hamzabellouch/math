import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.StableGraphEndpoint
import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.StableGraphPointSources

namespace OAI

/-! # Direct application of the stable graph to endpoint remainders

Only the concrete projected block and pointwise remainder estimates occur
as hypotheses. The weighted sources and the fixed sequence are constructed
inside the proof, and the conclusion is the original endpoint recurrence.
-/

open scoped BoundedContinuousFunction

namespace DefocusingNLS

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

theorem exists_stableGraph_actual_endpoint_sequence
    (ζ : ℕ → F →L[ℝ] E) (π : ℕ → E →L[ℝ] F)
    (A : ℕ → E →L[ℝ] E) (D R : F →L[ℝ] F)
    (hR : ‖R‖ ≤ 1) (hinv : ∀ z, D (R z) = z)
    (hπζ : ∀ n v, π n (ζ n v) = v)
    (hA : ∀ n, ‖stableProjectedBlock (ζ n) (ζ (n + 1))
      (π n) (π (n + 1)) (A n)‖ ≤ 1 / 8)
    (hB : ∀ n, ‖stableMixedBlock (ζ n) (ζ (n + 1)) (π (n + 1)) (A n)‖ ≤ 1 / 16)
    (h : ℕ → E → E) (w₀ : E) (hw₀ : π 0 w₀ = 0)
    (ρ ε C r : ℝ) (hρ : 0 ≤ ρ) (hε : 0 ≤ ε) (hC : 0 ≤ C)
    (hr : 0 ≤ r) (hrsmall : 2 * r ≤ 1) (hζ : ∀ n, ‖ζ n‖ ≤ C)
    (hN : ∀ n v w, ‖v‖ ≤ ρ → ‖w‖ ≤ ρ →
      ‖stableFrameForwardSource ζ π h n v - stableFrameForwardSource ζ π h n w‖ ≤
        (1 / 16 : ℝ) * ‖v - w‖)
    (hH : ∀ n v w, ‖v‖ ≤ ρ → ‖w‖ ≤ ρ →
      ‖stableFrameCoordinateSource ζ π A D h n v -
          stableFrameCoordinateSource ζ π A D h n w‖ ≤ (1 / 16 : ℝ) * ‖v - w‖)
    (hN0 : ∀ n, ‖stableFrameForwardSource ζ π h n 0‖ ≤ ε * r ^ n)
    (hH0 : ∀ n, ‖stableFrameCoordinateSource ζ π A D h n 0‖ ≤ ε * r ^ n)
    (hsmall : ‖w₀‖ + 2 * ε ≤ ρ / 2) :
    ∃ z : ℕ → E,
      stableFrameProjection (ζ 0) (π 0) (z 0) = w₀ ∧
      (∀ n, z (n + 1) = A n (z n) + h n (z n)) ∧
      (∀ n, ‖z n‖ ≤ (2 * (‖w₀‖ + 2 * ε) * (1 + C)) * (1 / 2 : ℝ) ^ n) := by
  let Nf : ℕ → E × F → E := stableFrameForwardSource ζ π h
  let Hf : ℕ → E × F → F := stableFrameCoordinateSource ζ π A D h
  let N := stableWeightedPairSource Nf ρ (1 / 16) ε r
    hρ (by norm_num) hε hr hrsmall hN hN0
  let H := stableWeightedPairSource Hf ρ (1 / 16) ε r
    hρ (by norm_num) hε hr hrsmall hH hH0
  apply exists_stableGraph_endpoint_sequence ζ π A D R hR hinv hπζ hA hB h w₀ hw₀
    N H ρ ε C hρ hε hC hζ
  · intro x y hx hy
    exact stableWeightedPairSource_dist_le Nf ρ (1 / 16) ε r
      hρ (by norm_num) hε hr hrsmall hN hN0 x y hx hy
  · intro x y hx hy
    exact stableWeightedPairSource_dist_le Hf ρ (1 / 16) ε r
      hρ (by norm_num) hε hr hrsmall hH hH0 x y hx hy
  · exact stableWeightedPairSource_zero_bound Nf ρ (1 / 16) ε r
      hρ (by norm_num) hε hr hrsmall hN hN0
  · exact stableWeightedPairSource_zero_bound Hf ρ (1 / 16) ε r
      hρ (by norm_num) hε hr hrsmall hH hH0
  · exact hsmall
  · intro x hx n
    exact (stableWeightedPairSource_value Nf ρ (1 / 16) ε r
      hρ (by norm_num) hε hr hrsmall hN hN0 x hx n).trans
        (stableFrameForwardSource_value ζ π h x n)
  · intro x hx n
    exact (stableWeightedPairSource_value Hf ρ (1 / 16) ε r
      hρ (by norm_num) hε hr hrsmall hH hH0 x hx n).trans
        (stableFrameCoordinateSource_value ζ π A D h x n)

end DefocusingNLS

end OAI
