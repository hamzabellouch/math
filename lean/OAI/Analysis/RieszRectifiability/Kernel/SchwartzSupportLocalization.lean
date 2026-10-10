import Mathlib
import OAI.Analysis.RieszRectifiability.Limits.CompactSchwartzApproximation

namespace OAI

/-!
# Support-preserving Schwartz approximation

Multiplication by expanding cutoffs gives compact approximants whose topological
supports remain inside that of the original test. This extends vanishing of tempered
distributions on compact tests away from the origin to all Schwartz tests away from
the origin, and shows that such distributions depend only on the test's germ there.
-/

namespace RieszRectifiability

noncomputable section

open SchwartzMap MeasureTheory Metric Filter Topology Set
open scoped ContDiff

theorem exists_compact_schwartz_approximation_with_support {d : ℕ}
    (g : 𝓢(Ambient d, ℂ)) :
    ∃ G : ℕ → 𝓢(Ambient d, ℂ), (∀ j, HasCompactSupport (G j)) ∧
      (∀ j, tsupport (G j) ⊆ tsupport g) ∧ Tendsto G atTop (𝓝 g) := by
  let G : ℕ → 𝓢(Ambient d, ℂ) := fun j => smulLeftCLM ℂ (expandingSmoothCutoff d j) g
  let q : ℕ → Ambient d → ℝ := fun j x => expandingSmoothCutoff d j x - 1
  have hβ : ∀ j, (expandingSmoothCutoff d j).HasTemperateGrowth :=
    fun j => (expandingSmoothCutoff_compact d j).hasTemperateGrowth (expandingSmoothCutoff_smooth d j)
  have hq : ∀ j, (q j).HasTemperateGrowth :=
    fun j => (hβ j).sub (Function.HasTemperateGrowth.const 1)
  obtain ⟨C, hC, hbound⟩ := expandingSmoothCutoff_error_uniform_derivatives d
  have hRt : Tendsto (fun j : ℕ => (j : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hzero : ∀ (j : ℕ) x, x ∈ ball (0 : Ambient d) ((j : ℝ) + 1) → q j x = 0 := by
    intro j x hx
    simp only [q, expandingSmoothCutoff_one d j x hx, sub_self]
  have ht := schwartz_cutoff_errors_tendsto_zero g q hq C hC hbound
    (fun j : ℕ => (j : ℝ) + 1) (fun j => by positivity) hRt hzero
  refine ⟨G, ?_, ?_, ?_⟩
  · intro j
    have hc : HasCompactSupport (fun x => expandingSmoothCutoff d j x • g x) :=
      (expandingSmoothCutoff_compact d j).smul_right
    simpa only [G, smulLeftCLM_apply (hβ j)] using! hc
  · intro j
    simpa only [G, smulLeftCLM_apply (hβ j)] using!
      tsupport_smul_subset_right (expandingSmoothCutoff d j) (g : Ambient d → ℂ)
  · have heq : G = fun j => g + smulLeftCLM ℂ (q j) g := by
      funext j
      ext x
      simp only [G, add_apply, smulLeftCLM_apply_apply (hβ j),
        smulLeftCLM_apply_apply (hq j), q, sub_smul, one_smul]
      abel
    rw [heq]
    simpa only [add_zero] using! tendsto_const_nhds.add ht

theorem tempered_distribution_zero_away_zero_of_compact_tests {d : ℕ}
    (T : 𝓢'(Ambient d, ℂ))
    (hT : ∀ g : 𝓢(Ambient d, ℂ), HasCompactSupport g →
      (0 : Ambient d) ∉ tsupport g → T g = 0)
    (g : 𝓢(Ambient d, ℂ)) (hg : (0 : Ambient d) ∉ tsupport g) : T g = 0 := by
  obtain ⟨G, hc, hs, ht⟩ := exists_compact_schwartz_approximation_with_support g
  have hlim := T.continuous.tendsto g |>.comp ht
  have hz : ∀ j, T (G j) = 0 := fun j => hT (G j) (hc j) (fun h => hg (hs j h))
  apply tendsto_nhds_unique hlim
  exact (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (𝓝 0)).congr'
    (Eventually.of_forall fun j => (hz j).symm)

theorem tempered_distribution_eq_of_germ_at_zero {d : ℕ}
    (T : 𝓢'(Ambient d, ℂ))
    (hT : ∀ g : 𝓢(Ambient d, ℂ), HasCompactSupport g →
      (0 : Ambient d) ∉ tsupport g → T g = 0)
    (g h : 𝓢(Ambient d, ℂ))
    (hgh : (g : Ambient d → ℂ) =ᶠ[𝓝 (0 : Ambient d)] h) : T g = T h := by
  have hz : (0 : Ambient d) ∉ tsupport (g - h) := by
    apply notMem_tsupport_iff_eventuallyEq.mpr
    filter_upwards [hgh] with x hx
    simp only [sub_apply, Pi.zero_apply, hx, sub_self]
  have heq := tempered_distribution_zero_away_zero_of_compact_tests T hT (g - h) hz
  rw [map_sub, sub_eq_zero] at heq
  exact heq

end

end RieszRectifiability

end OAI
