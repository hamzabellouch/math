import Mathlib
import OAI.Analysis.RieszRectifiability.Limits.FixedCutoffPairingLimit
import OAI.Analysis.RieszRectifiability.Packing.OriginalVectorTestBessel

namespace OAI

/-!
# Bessel bounds for fixed-cutoff pairings

Hard-truncation pairing limits transfer the vector-test Bessel estimate to a
finite family of fixed-cutoff scalar pairings. The resulting bound retains the
interaction packing constant and the mass of the common outer ball.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal

theorem DyadicOscillationTests.fixed_cutoff_bessel {ι : Type*} {p d : ℕ}
    [Nontrivial (Ambient d)] {μ : Measure (Ambient d)} [SFinite μ] {c J : ℝ}
    (F : DyadicOscillationTests ι d μ c J)
    (C G : ℝ) (hC : 0 < C) (hg : GlobalUpperGrowth (p + 1) G μ)
    (hlower : ∀ x ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
      ENNReal.ofReal (r ^ (p + 1) / C) ≤ μ (ball x r))
    (hc : 0 < c) (hJ : 0 < J) (s : Finset ι) (D : ℝ≥0)
    (hR : ∀ ε : ℝ, 0 < ε → ∀ f : Ambient d → ℝ, MemLp f 2 μ →
      MemLp (truncated (p + 1) μ ε f) 2 μ ∧
        eLpNorm (truncated (p + 1) μ ε f) 2 μ ≤ (D : ℝ≥0∞) * eLpNorm f 2 μ)
    (a : Ambient d) (T : ℝ) (hT : 0 < T)
    (houter : ∀ i ∈ s, tsupport (F.test i) ⊆ ball a T)
    (e : ι → Ambient d) (he : ∀ i ∈ s, ‖e i‖ ≤ 1) :
    ∑ i ∈ s, (rieszScalarPairing (p + 1) (μ.restrict (ball a T))
      (F.center i) (2 * (J * F.radius i)) (e i) (F.test i)) ^ 2 / F.radius i ^ (p + 1) ≤
      ((4 * (G * J ^ (p + 1 + 1) * (2 * J + 1) ^ 2) *
        interactionPackingConstant (p + 1) C G c J) * (D : ℝ) ^ 2) * μ.real (ball a T) := by
  have hlim (i : ι) (hi : i ∈ s) := fixed_cutoff_hard_pairing_limit p G μ hg a T hT
    (e i) (F.test i) (F.lip i) (F.lipschitz i) (F.center i) (2 * (J * F.radius i))
    (mul_pos (by norm_num) (mul_pos hJ (F.radius_pos i)))
    (by
      intro x hx
      by_contra hn
      exact hx (houter i hi (subset_tsupport _ hn)))
    (by
      intro x hx
      by_contra hn
      have hb := F.support_subset i (subset_tsupport _ hn)
      apply hx
      exact (ball_subset_ball (by have hr := mul_pos hJ (F.radius_pos i); linarith)) hb)
    (F.mean_zero i)
  have ht := tendsto_finsetSum s (fun i hi => ((hlim i hi).pow 2).div_const (F.radius i ^ (p + 1)))
  apply le_of_tendsto ht
  apply Filter.Eventually.of_forall
  intro k
  obtain ⟨hf, hnorm⟩ := ball_indicator_one_memLp_and_sq_integral (p + 1) G μ hg a T hT
  have hb := F.native_truncation_bessel C G hC hg hlower hc hJ s D hR
    ((1 / 2 : ℝ) ^ k) (pow_pos (by norm_num) k) _ hf e he
  simpa only [hnorm] using! hb

end

end RieszRectifiability

end OAI
