import OAI.Analysis.LipschitzHilbert.Estimates.IntervalOscillation
import OAI.Analysis.LipschitzHilbert.Estimates.SegmentAmplitudes

namespace OAI

/-! Abel summation bounds the actual weighted packet increments by the
unweighted maximum over subintervals of their common prefix sequence. -/

noncomputable section

open scoped BigOperators

namespace LipschitzHilbert

def packetPrefix {E : Type*} [AddCommMonoid E] (f : ℕ → E) (n : ℕ) : E :=
  ∑ j ∈ Finset.range n, f j

theorem interval_packet_sum_le {E : Type*} [NormedAddCommGroup E]
    (f : ℕ → E) (H a b c d : ℕ) (hac : a ≤ c) (hcd : c ≤ d)
    (hdb : d ≤ b) (hb : b ≤ H) :
    ‖∑ j ∈ Finset.Ico c d, f j‖ ≤ intervalOscillation (packetPrefix f) H a b := by
  rw [Finset.sum_Ico_eq_sub _ hcd]
  exact increment_le_intervalOscillation (packetPrefix f) H a b c d hac hcd hdb hb

/-- The coefficient-variation estimate uses the full root mass ratio.
The packet maximum itself is restricted to the current segment. -/
theorem boundary_segment_amplitude_le_oscillation {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] (n m : ℕ → ℝ) (z : ℕ → ℂ) (f : ℕ → E)
    (start N K H a b : ℕ) (power lower Z : ℝ)
    (hstart : start ≤ N) (ha : a ≤ start) (hb : N + 1 ≤ b) (hbH : b ≤ H)
    (hpower : 0 ≤ power) (hlower : 0 < lower) (hZ : 0 ≤ Z)
    (hn : ∀ j ≤ N, lower ≤ n j) (hmono : AntitoneOn n (Set.Iic N))
    (hm : ∀ j < N, n (j + 1) ≤ m j ∧ m j ≤ n (j + 1 - K))
    (hz0 : ∀ j < N, 0 ≤ (z j).re) (hz : ∀ j < N, ‖z j‖ ≤ Z) :
    ‖∑ j ∈ Finset.Ico start (N + 1),
      segmentWeight n (boundaryLog n m) z power start j • f j‖ ≤
      (lower ^ (-power) * (1 + (power + Z * K) * Real.log (n 0 / n N))) *
        intervalOscillation (packetPrefix f) H a b := by
  apply boundary_segment_amplitude_bound n m z f start N K power lower Z _ hstart
    hpower hlower hZ (intervalOscillation_nonneg _ _ _ _) hn hmono hm hz0 hz
  intro k hsk hkN
  exact interval_packet_sum_le f H a b start (k + 1) ha (by omega) (by omega) hbH

end LipschitzHilbert

end

end OAI
