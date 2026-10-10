import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Module.WeakDual

namespace OAI

/-! The bounded Hilbert-space subsequence used for the scalar fillings
and their two L² differential components. It follows from the library's
sequential Banach–Alaoglu theorem and the Riesz representation isometry. -/
open Set Function Filter Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem exists_hilbert_weak_subsequence
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [TopologicalSpace.SeparableSpace E]
    (u : ℕ → E) (C : ℝ) (hu : ∀ n, ‖u n‖ ≤ C) :
    ∃ v : E, ‖v‖ ≤ C ∧ ∃ σ : ℕ → ℕ, StrictMono σ ∧
      ∀ w : E, Tendsto (fun n => inner ℝ (u (σ n)) w) atTop (𝓝 (inner ℝ v w)) := by
  let a : ℕ → WeakDual ℝ E := fun n => StrongDual.toWeakDual (InnerProductSpace.toDual ℝ E (u n))
  have ha (n : ℕ) : a n ∈ WeakDual.toStrongDual ⁻¹' closedBall (0 : StrongDual ℝ E) C := by
    simpa only [mem_preimage, mem_closedBall, dist_zero_right, a,
      StrongDual.toStrongDual_toWeakDual, LinearIsometryEquiv.norm_map] using hu n
  obtain ⟨l, hl, σ, hσ, hlim⟩ :=
    (WeakDual.isSeqCompact_closedBall (𝕜 := ℝ) (E := E) 0 C).subseq_of_frequently_in
      (Frequently.of_forall ha)
  let v : E := (InnerProductSpace.toDual ℝ E).symm (WeakDual.toStrongDual l)
  refine ⟨v, ?_, σ, hσ, ?_⟩
  · have hn : ‖WeakDual.toStrongDual l‖ ≤ C := by
      simpa only [mem_preimage, mem_closedBall, dist_zero_right] using hl
    exact ((InnerProductSpace.toDual ℝ E).symm.norm_map _).trans_le hn
  · intro w
    have he := (WeakDual.eval_continuous w).continuousAt.tendsto.comp hlim
    have hv : inner ℝ v w = l w := InnerProductSpace.toDual_symm_apply
    simpa only [a, comp_def, StrongDual.toWeakDual_apply, InnerProductSpace.toDual_apply_apply,
      ← hv] using he

end CircleDomainRigidity

end

end OAI
