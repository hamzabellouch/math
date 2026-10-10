import Mathlib
import OAI.Combinatorics.TriangleRemoval.Probability.FiniteMean

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

theorem pmfMean_liminf_le_of_tendsto_upper {α : Type*} [Fintype α]
    (p : PMF α) (f : α → ℕ → ℝ) (hbound : ∀ a j, 0 ≤ f a j)
    (g : ℕ → ℝ) {L : ℝ} (hg : Tendsto g atTop (𝓝 L))
    (hupper : ∀ᶠ j : ℕ in atTop, pmfMean p (fun a => f a j) ≤ g j) :
    pmfMean p (fun a => Filter.liminf (f a) atTop) ≤ L := by
  apply le_of_forall_pos_le_add
  intro ε hε
  have hevent (a : α) : ∀ᶠ j : ℕ in atTop,
      Filter.liminf (f a) atTop - ε ≤ f a j := by
    have hl : atTop.IsBoundedUnder (· ≥ ·) (f a) :=
      Filter.isBoundedUnder_of ⟨0, fun j => hbound a j⟩
    exact (Filter.eventually_lt_of_lt_liminf (sub_lt_self _ hε) hl).mono (fun _ h => h.le)
  have hall : ∀ᶠ j : ℕ in atTop, ∀ a, Filter.liminf (f a) atTop - ε ≤ f a j :=
    Filter.eventually_all.mpr hevent
  have hle : pmfMean p (fun a => Filter.liminf (f a) atTop) - ε ≤ L := by
    apply le_of_tendsto_of_tendsto tendsto_const_nhds hg
    filter_upwards [hall,hupper] with j hj hU
    have hh := pmfMean_mono p (fun a _ => hj a)
    rw [pmfMean_sub,pmfMean_const] at hh
    exact hh.trans hU
  linarith

end SharpTerminalLeave

end

end OAI
