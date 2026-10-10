import OAI.NumberTheory.JointDickman.Probability.ArithmeticKernelPeriod

namespace OAI

/-! # Vanishing fluctuations in ordinary long arithmetic averages -/

namespace JointDickman
open Finset Filter
open scoped Topology

theorem actual_candidate_long_mean_small
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hMertens : PublishedInputs.PrimeReciprocalMertensInput)
    {L : ℕ} (hL : 1 ≤ L) {τ : ℝ} (hτ : 0 ≤ τ) (hτsmall : τ ≤ samplingTau) :
    ∃ E : ℕ → ℝ, Tendsto E atTop (𝓝 0) ∧
      ∀ᶠ B : ℕ in atTop, ∀ (C : ℝ) (T H M : ℕ),
        0 < T → (T : ℝ) ≤ Real.exp ((1/10 : ℝ)*B) → T ≤ auxiliaryCutoff B →
        0 < M → M ≤ B^2 → (M : ℝ) ≤ Real.exp B →
        ∀ χ : BlockCandidateIndex M → ℝ, (∀ e, 0 ≤ χ e ∧ χ e ≤ 1) →
        ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
          (∑ u ∈ range N, actualCandidateCutError B L T H M τ C χ u)/(N : ℝ) < E B+ε := by
  obtain ⟨E,hE,hbound⟩ := actual_arithmetic_fluctuation_decay hFord hMertens hL hτ hτsmall
  refine ⟨E,hE,?_⟩
  filter_upwards [hbound] with B hbound
  intro C T H M hT hTs hTP hM0 hM hMexp χ hχ ε hε
  have hb := hbound C T H M hT hTs hTP hM0 hM hMexp χ hχ
  have ht := actualCandidateCutError_mean_tendsto (L := L) (H := H) (τ := τ) (C := C) hTP χ
  exact ht.eventually (Iio_mem_nhds (lt_add_of_le_of_pos hb hε))

end JointDickman

end OAI
