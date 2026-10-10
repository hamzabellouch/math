import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.L2Pairings

namespace OAI

/-!
# Weak subsequences of bounded L² sequences

A bounded sequence in a separable Hilbert space admits a weakly convergent
subsequence whose limit obeys the same norm bound. For real L² functions,
the Hilbert-space pairings become integrals against arbitrary L² tests.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal

theorem bounded_hilbert_sequence_weak_subsequence {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    (u : ℕ → H) (B : ℝ) (hB : ∀ j, ‖u j‖ ≤ B) :
    ∃ ρ : ℕ → ℕ, StrictMono ρ ∧ ∃ v : H, ‖v‖ ≤ B ∧
      ∀ w : H, Tendsto (fun j => inner ℝ (u (ρ j)) w) atTop (𝓝 (inner ℝ v w)) := by
  let F : ℕ → WeakDual ℝ H := fun j =>
    StrongDual.toWeakDual (InnerProductSpace.toDual ℝ H (u j))
  have hin : ∀ j, F j ∈ WeakDual.toStrongDual ⁻¹' closedBall (0 : StrongDual ℝ H) B := by
    intro j
    rw [mem_preimage, mem_closedBall, dist_zero_right]
    change ‖InnerProductSpace.toDual ℝ H (u j)‖ ≤ B
    rw [(InnerProductSpace.toDual ℝ H).norm_map]
    exact hB j
  obtain ⟨T, hT, ρ, hρ, hlim⟩ :=
    (WeakDual.isSeqCompact_closedBall ℝ H (0 : StrongDual ℝ H) B) hin
  let v := (InnerProductSpace.toDual ℝ H).symm (WeakDual.toStrongDual T)
  refine ⟨ρ, hρ, v, ?_, ?_⟩
  · change ‖(InnerProductSpace.toDual ℝ H).symm (WeakDual.toStrongDual T)‖ ≤ B
    rw [(InnerProductSpace.toDual ℝ H).symm.norm_map]
    rw [mem_preimage, mem_closedBall, dist_zero_right] at hT
    exact hT
  · intro w
    have h := ((WeakDual.eval_continuous w).tendsto T).comp hlim
    change Tendsto (fun j => inner ℝ (u (ρ j)) w) atTop (𝓝 (T w)) at h
    simpa only [v, InnerProductSpace.toDual_symm_apply] using! h

theorem bounded_L2_sequence_weak_subsequence {d : ℕ} (μ : Measure (Ambient d)) [SFinite μ]
    (f : ℕ → Ambient d → ℝ) (hf : ∀ j, MemLp (f j) 2 μ)
    (B : ℝ) (hB : ∀ j, ‖(hf j).toLp (f j)‖ ≤ B) :
    ∃ ρ : ℕ → ℕ, StrictMono ρ ∧ ∃ v : Lp ℝ 2 μ, ‖v‖ ≤ B ∧
      ∀ g : Ambient d → ℝ, MemLp g 2 μ →
        Tendsto (fun j => ∫ x, f (ρ j) x * g x ∂μ) atTop (𝓝 (∫ x, v x * g x ∂μ)) := by
  let : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  obtain ⟨ρ, hρ, v, hv, hlim⟩ := bounded_hilbert_sequence_weak_subsequence
    (fun j => (hf j).toLp (f j)) B hB
  refine ⟨ρ, hρ, v, hv, ?_⟩
  intro g hg
  have hright : inner ℝ v (hg.toLp g) = ∫ x, v x * g x ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hg.coeFn_toLp] with x hx
    rw [hx, real_scalar_inner_mul]
  simpa only [toLp_inner_eq_integral, hright] using! hlim (hg.toLp g)

end

end RieszRectifiability

end OAI
