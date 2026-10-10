import Mathlib
import OAI.Analysis.RieszRectifiability.Foundations.BlowupMeasure
import OAI.Analysis.RieszRectifiability.Limits.CompactSupportApproximants

namespace OAI

/-!
# Subspace support of tangent measures

Compact-test convergence preserves containment of supports in a fixed closed set.
Blowups centered in a linear subspace stay in that subspace, so their limits inherit
the same support constraint. Intersecting with the normal hyperplane of a nonzero
subspace vector strictly reduces the dimension, as needed for dimension reduction.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Filter Topology

theorem compactTestConvergence_support_subset_closed {d : ℕ}
    (μ : ℕ → Measure (Ambient d)) (ν : Measure (Ambient d))
    [∀ j, IsFiniteMeasureOnCompacts (μ j)] [IsFiniteMeasureOnCompacts ν]
    (hlocal : CompactTestConvergence μ ν) (E : Set (Ambient d)) (hE : IsClosed E)
    (hsub : ∀ j, (μ j).support ⊆ E) : ν.support ⊆ E := by
  intro b hb
  obtain ⟨φ, a, _, _, has, ha⟩ := compactTestConvergence_support_approximants μ ν hlocal b hb
  exact hE.mem_of_tendsto ha (Eventually.of_forall fun j => hsub (φ j) (has j))

theorem blowupMeasure_support_submodule {d : ℕ} (n : ℕ) (μ : Measure (Ambient d))
    (P : Submodule ℝ (Ambient d)) (hP : μ.support ⊆ (P : Set (Ambient d)))
    (a : Ambient d) (ha : a ∈ P) (s : ℝ) (hs : 0 < s) :
    (blowupMeasure n μ a s).support ⊆ (P : Set (Ambient d)) := by
  intro x hx
  have hy := hP ((blowupMeasure_support_iff n μ a x s hs).mp hx)
  have hz := P.smul_mem s⁻¹ (P.sub_mem hy ha)
  simpa only [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hs.ne', one_smul] using! hz

theorem blowup_limit_support_submodule {d : ℕ} (n : ℕ) (μ ν : Measure (Ambient d))
    [IsFiniteMeasureOnCompacts ν] (G : ℝ) (hg : GlobalUpperGrowth n G μ)
    (P : Submodule ℝ (Ambient d)) (hP : μ.support ⊆ (P : Set (Ambient d)))
    (a : Ambient d) (ha : a ∈ P) (s : ℕ → ℝ) (hs : ∀ j, 0 < s j)
    (hlocal : CompactTestConvergence (fun j => blowupMeasure n μ a (s j)) ν) :
    ν.support ⊆ (P : Set (Ambient d)) := by
  let : ContinuousSMul ℝ (Ambient d) := IsBoundedSMul.continuousSMul
  let : ∀ j, IsFiniteMeasureOnCompacts (blowupMeasure n μ a (s j)) := fun j =>
    globalGrowth_finite_on_compacts G _ (blowupMeasure_growth n μ a (s j) G (hs j) hg)
  exact compactTestConvergence_support_subset_closed _ ν hlocal P P.closed_of_finiteDimensional
    (fun j => blowupMeasure_support_submodule n μ P hP a ha (s j) (hs j))

theorem normal_section_finrank_lt {d : ℕ} (P : Submodule ℝ (Ambient d))
    (e : Ambient d) (heP : e ∈ P) (he : e ≠ 0) :
    Module.finrank ℝ ↥(P ⊓ (innerSL ℝ e).toLinearMap.ker) < Module.finrank ℝ P := by
  apply Submodule.finrank_lt_finrank_of_lt
  apply (lt_iff_le_not_ge).mpr
  refine ⟨inf_le_left, ?_⟩
  intro hle
  have hz := (hle heP).2
  change inner ℝ e e = 0 at hz
  rw [real_inner_self_eq_norm_sq] at hz
  have hp := norm_pos_iff.mpr he
  nlinarith

end

end RieszRectifiability

end OAI
