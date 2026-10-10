import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.InnerProductSpace.Dual

namespace OAI

/-! Sequential weak compactness for the separable complex Hilbert form domain. -/

open Filter Topology Set
namespace DefocusingNLS

theorem spectralHilbert_weak_subsequence {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] [TopologicalSpace.SeparableSpace E]
    (u : ℕ → E) (M : ℝ) (hu : ∀ n, ‖u n‖ ≤ M) :
    ∃ v : E, ‖v‖ ≤ M ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ L : E →L[ℂ] ℂ, Tendsto (fun n => L (u (φ n))) atTop (𝓝 (L v)) := by
  let R := InnerProductSpace.toDual ℂ E
  let w : ℕ → WeakDual ℂ E := fun n => (R (u n)).toWeakDual
  have hw (n : ℕ) : w n ∈ WeakDual.toStrongDual ⁻¹' Metric.closedBall 0 M := by
    change R (u n) ∈ Metric.closedBall 0 M
    simpa only [Metric.mem_closedBall,dist_zero_right,R.norm_map] using hu n
  obtain ⟨v',hv',φ,hφ,ht⟩ := (WeakDual.isSeqCompact_closedBall ℂ E 0 M) hw
  let v := R.symm v'.toStrongDual
  have hv : ‖v‖ ≤ M := by
    change ‖R.symm v'.toStrongDual‖ ≤ M
    rw [R.symm.norm_map]
    simpa only [mem_preimage,Metric.mem_closedBall,dist_zero_right] using hv'
  refine ⟨v,hv,φ,hφ,fun L => ?_⟩
  let x := R.symm L
  have hn (n : ℕ) : star (w (φ n) x)=L (u (φ n)) := by
    change (starRingEnd ℂ) (inner ℂ (u (φ n)) x)=L (u (φ n))
    rw [inner_conj_symm]
    exact InnerProductSpace.toDual_symm_apply
  have hvx : star (v' x)=L v := by
    have he : R v=v'.toStrongDual := R.apply_symm_apply _
    change star (v'.toStrongDual x)=L v
    rw [← he]
    change (starRingEnd ℂ) (inner ℂ v x)=L v
    rw [inner_conj_symm]
    exact InnerProductSpace.toDual_symm_apply
  have h := ((WeakDual.eval_continuous x).continuousAt.tendsto.comp ht).star
  simpa only [Function.comp_def,hn,hvx] using h

end DefocusingNLS

end OAI
