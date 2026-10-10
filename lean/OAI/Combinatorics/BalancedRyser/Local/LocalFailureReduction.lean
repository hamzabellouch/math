import OAI.Combinatorics.BalancedRyser.Incidence.LocalLargePencils
import OAI.Combinatorics.BalancedRyser.Incidence.PencilReuseEndpoint
import OAI.Combinatorics.BalancedRyser.Local.LocalHighReuse

namespace OAI

namespace Balanced.Local

universe u
open Filter
open scoped Topology

noncomputable section

theorem high_reuse_uniform_error :
    ∀ K : ℝ, 0 < K → ∃ ε : ℕ → ℝ,
      Tendsto ε atTop (𝓝 0) ∧ (∀ q, 0 ≤ ε q) ∧
      ∃ q₀ : ℕ, ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F],
        q₀ ≤ Fintype.card F → ∀ (Q : RetentionRule F) (w : Kernel F),
        KernelConditions Q w K → selectedProbability w HighReuseEvent ≤
          ε (Fintype.card F) :=
  HighReuse.uniform_vanishing_of_pencilReuse pencilReuse_proof

theorem local_failure_le_small_add_uniform_error (K : ℝ) (hK : 0 < K) :
    ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧ (∀ q, 0 ≤ ε q) ∧
      ∃ q₀ : ℕ, ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F],
        q₀ ≤ Fintype.card F → ∀ (Q : RetentionRule F) (w : Kernel F),
        KernelConditions Q w K →
        selectedProbability w (fun C => ¬ C.LocalCondition) ≤
          selectedProbability w SmallBadPatternEvent + ε (Fintype.card F) := by
  obtain ⟨εlarge, hlarge_lim, hlarge_nonneg, hlarge⟩ :=
    large_pencil_uniform_error K hK.le
  obtain ⟨εreuse, hreuse_lim, hreuse_nonneg, q₀, hreuse⟩ :=
    high_reuse_uniform_error.{u} K hK
  refine ⟨fun q => εlarge q + εreuse q, ?_, ?_, q₀, ?_⟩
  · simpa using hlarge_lim.add hreuse_lim
  · intro q
    exact add_nonneg (hlarge_nonneg q) (hreuse_nonneg q)
  · intro F _ _ _ hq Q w hw
    have hl : selectedProbability w LargePencilEvent ≤ εlarge (Fintype.card F) := by
      apply le_trans (KernelBridge.selectedProbability_mono w hw.1 ?_) (hlarge F Q w hw)
      intro C hC
      obtain ⟨p, hp⟩ := hC
      exact ⟨p, hp.le⟩
    have hr := hreuse F hq Q w hw
    calc
      _ ≤ selectedProbability w LargePencilEvent +
          selectedProbability w HighReuseEvent + selectedProbability w SmallBadPatternEvent :=
        local_failure_probability_le Q w K hw
      _ ≤ εlarge (Fintype.card F) + εreuse (Fintype.card F) +
          selectedProbability w SmallBadPatternEvent :=
        add_le_add (add_le_add hl hr) le_rfl
      _ = _ := by ring

theorem pencilLocal_of_smallPattern_uniform_error
    (hsmall : ∀ K : ℝ, 0 < K → ∃ ε : ℕ → ℝ,
      Tendsto ε atTop (𝓝 0) ∧ (∀ q, 0 ≤ ε q) ∧
      ∃ q₀ : ℕ, ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F],
        q₀ ≤ Fintype.card F → ∀ (Q : RetentionRule F) (w : Kernel F),
        KernelConditions Q w K → selectedProbability w SmallBadPatternEvent ≤
          ε (Fintype.card F)) : PencilLocalResult.{u} := by
  intro K hK
  obtain ⟨εsmall, hsmall_lim, hsmall_nonneg, qs, hsmall_bound⟩ := hsmall K hK
  obtain ⟨εother, hother_lim, hother_nonneg, qo, hother_bound⟩ :=
    local_failure_le_small_add_uniform_error.{u} K hK
  refine ⟨fun q => εsmall q + εother q, ?_, ?_, max qs qo, ?_⟩
  · simpa using hsmall_lim.add hother_lim
  · intro q
    exact add_nonneg (hsmall_nonneg q) (hother_nonneg q)
  · intro F _ _ _ hq Q w hw
    have hqs : qs ≤ Fintype.card F := (le_max_left qs qo).trans hq
    have hqo : qo ≤ Fintype.card F := (le_max_right qs qo).trans hq
    exact (hother_bound F hqo Q w hw).trans
      (add_le_add (hsmall_bound F hqs Q w hw) le_rfl)

end
end Balanced.Local

end OAI
