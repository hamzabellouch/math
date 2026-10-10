import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.DerivativeTests
import OAI.Analysis.RieszRectifiability.Kernel.ExpandingSmoothCutoffs
import OAI.Analysis.RieszRectifiability.Limits.SchwartzCutoffConvergence

namespace OAI

/-!
# Compactly supported approximation in Schwartz space

Expanding smooth cutoffs approximate Schwartz functions in the Schwartz topology.
Continuity of directional differentiation preserves this convergence, while compact
support ensures the approximating derivatives have zero integral. Consequently,
tempered distributions are determined by their compactly supported Schwartz tests.
-/

namespace RieszRectifiability

noncomputable section

open SchwartzMap MeasureTheory Metric Filter Topology
open scoped ContDiff LineDeriv

theorem exists_compact_schwartz_approximation {d : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] (g : 𝓢(Ambient d, F)) :
    ∃ G : ℕ → 𝓢(Ambient d, F), (∀ j, HasCompactSupport (G j)) ∧
      Tendsto G atTop (𝓝 g) := by
  let G : ℕ → 𝓢(Ambient d, F) := fun j => smulLeftCLM F (expandingSmoothCutoff d j) g
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
  refine ⟨G, ?_, ?_⟩
  · intro j
    have hc : HasCompactSupport (fun x => expandingSmoothCutoff d j x • g x) :=
      (expandingSmoothCutoff_compact d j).smul_right
    simpa only [G, smulLeftCLM_apply (hβ j)] using! hc
  · have heq : G = fun j => g + smulLeftCLM F (q j) g := by
      funext j
      ext x
      simp only [G, add_apply, smulLeftCLM_apply_apply (hβ j),
        smulLeftCLM_apply_apply (hq j), q, sub_smul, one_smul]
      abel
    rw [heq]
    simpa only [add_zero] using! tendsto_const_nhds.add ht

theorem exists_compact_directional_schwartz_approximation {d : ℕ}
    (g : 𝓢(Ambient d, ℝ)) (v : Ambient d) :
    ∃ G : ℕ → 𝓢(Ambient d, ℝ),
      (∀ j, HasCompactSupport (G j)) ∧ Tendsto G atTop (𝓝 g) ∧
      (∀ j, HasCompactSupport ((∂_{v} (G j) : 𝓢(Ambient d, ℝ)) : Ambient d → ℝ) ∧
        (∫ x : Ambient d, (∂_{v} (G j) : 𝓢(Ambient d, ℝ)) x) = 0) ∧
      Tendsto (fun j => ∂_{v} (G j)) atTop (𝓝 (∂_{v} g)) := by
  obtain ⟨G, hc, ht⟩ := exists_compact_schwartz_approximation g
  refine ⟨G, hc, ht, ?_, ?_⟩
  · intro j
    exact ⟨(hc j).fderiv_apply ℝ v, schwartz_directional_derivative_integral_zero (G j) v⟩
  · exact (LineDeriv.lineDerivOpCLM ℝ 𝓢(Ambient d, ℝ) v).continuous.tendsto g |>.comp ht

theorem tempered_distribution_eq_of_compact_tests {d : ℕ}
    (T S : 𝓢'(Ambient d, ℂ))
    (h : ∀ g : 𝓢(Ambient d, ℂ), HasCompactSupport g → T g = S g) : T = S := by
  ext g
  obtain ⟨G, hc, ht⟩ := exists_compact_schwartz_approximation g
  have hT := T.continuous.tendsto g |>.comp ht
  have hS := S.continuous.tendsto g |>.comp ht
  apply tendsto_nhds_unique hT
  exact hS.congr' (Filter.Eventually.of_forall fun j => (h (G j) (hc j)).symm)

end

end RieszRectifiability

end OAI
