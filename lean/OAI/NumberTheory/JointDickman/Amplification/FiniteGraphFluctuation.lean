import OAI.NumberTheory.JointDickman.Amplification.GraphSquareRemoval
import OAI.NumberTheory.JointDickman.Counting.BlockSquarePeriod

namespace OAI

/-! # Vanishing fluctuations of the original symmetric finite graph -/

namespace JointDickman
open Finset Filter Classical
open scoped Topology

theorem finite_graph_arithmetic_fluctuation
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hMertens : PublishedInputs.PrimeReciprocalMertensInput)
    {L : ℕ} (hL : 1 ≤ L) {τ : ℝ} (hτ : 0 ≤ τ) (hτsmall : τ ≤ samplingTau) :
    ∃ E : ℕ → ℝ, Tendsto E atTop (𝓝 0) ∧
      ∀ᶠ B : ℕ in atTop, ∀ (C : ℝ) (T H M : ℕ),
        0 < T → (T : ℝ) ≤ Real.exp ((1/10 : ℝ)*B) → T ≤ auxiliaryCutoff B →
        0 < M → M ≤ B^2 → (M : ℝ) ≤ Real.exp B →
        ∀ ε : ℝ, 0 < ε → ∀ᶠ K : ℕ in atTop, ∀ N : ℕ,
          (∑ u ∈ range K, finiteGraphLatentError B L T H M N u τ C)/(K : ℝ) < E B+ε := by
  obtain ⟨E,hE,hcut⟩ := finite_cutoff_arithmetic_decay hFord hMertens hL hτ hτsmall
  refine ⟨fun B => E B+1/(B : ℝ),?_,?_⟩
  · simpa only [add_zero] using hE.add (tendsto_const_div_atTop_nhds_zero_nat (𝕜 := ℝ) 1)
  filter_upwards [hcut,finiteGraphCandidateError_cap hL hτ hτsmall,eventually_gt_atTop 1]
    with B hcut hcap hB
  intro C T H M hT hTs hTP hM0 hM hMexp ε hε
  have heps : 0 < ε/2 := by linarith
  filter_upwards [hcut C T H M hT hTs hTP hM0 hM hMexp (ε/2) heps,
    blockSquareWeight_long_mean hB hM heps] with K hcut hsquare
  intro N
  have hsum : (∑ u ∈ range K, finiteGraphLatentError B L T H M N u τ C)/(K : ℝ) ≤
      (∑ u ∈ range K, actualCandidateCutError B L T H M τ C (finiteCandidateCutoff B T N u) u)/(K : ℝ)+
        (∑ u ∈ range K, blockSquareWeight B M u)/(K : ℝ) := by
    rw [← add_div,← sum_add_distrib]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg K)
    apply sum_le_sum
    intro u _
    exact finiteGraphLatentError_pointwise (by omega) hT hTP (hcap C T H M N u hT hM0 hM)
  have hcutN := hcut N
  linarith

end JointDickman

end OAI
