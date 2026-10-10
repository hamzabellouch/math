import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Basic

namespace OAI

/-! # Smoothness bootstrapping for autonomous integral curves

Only the differential equation and smoothness of its vector field are used.
This is the local analytic step needed for smooth Lie exponential curves.
-/

noncomputable section
namespace PolycyclicRecognition

open Set Filter
open scoped Topology ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem contDiffAt_of_autonomous_curve {F : E → E} {γ : ℝ → E} {t₀ : ℝ}
    (hF : ContDiffAt ℝ ∞ F (γ t₀))
    (hγ : ∀ᶠ t in 𝓝 t₀, HasDerivAt γ (F (γ t)) t) :
    ContDiffAt ℝ ∞ γ t₀ := by
  apply contDiffAt_infty.2
  intro n
  induction n with
  | zero =>
    obtain ⟨U, hU, hder⟩ := eventually_iff_exists_mem.1 hγ
    exact contDiffAt_zero.2 ⟨U, hU, fun t ht => (hder t ht).continuousAt.continuousWithinAt⟩
  | succ n ih =>
    apply contDiffAt_succ_iff_hasFDerivAt.2
    refine ⟨fun t => (1 : ℝ →L[ℝ] ℝ).smulRight (F (γ t)), ?_, ?_⟩
    · obtain ⟨U, hU, hder⟩ := eventually_iff_exists_mem.1 hγ
      exact ⟨U, hU, fun t ht => (hder t ht).hasFDerivAt⟩
    · exact contDiffAt_const.smulRight ((hF.of_le (by simp)).comp t₀ ih)

theorem contDiff_of_autonomous_curve {F : E → E} {γ : ℝ → E}
    (hF : ContDiff ℝ ∞ F) (hγ : ∀ t, HasDerivAt γ (F (γ t)) t) :
    ContDiff ℝ ∞ γ := by
  apply contDiff_iff_contDiffAt.2
  intro t
  exact contDiffAt_of_autonomous_curve hF.contDiffAt (Eventually.of_forall hγ)

end PolycyclicRecognition

end

end OAI
