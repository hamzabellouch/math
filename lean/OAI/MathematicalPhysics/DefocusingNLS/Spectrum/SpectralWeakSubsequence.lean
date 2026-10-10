import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralCompactWeak
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.InnerProductSpace.Dual

namespace OAI

/-! Weak subsequences and compact observations for the real variational domain. -/

open Set Filter Topology
namespace DefocusingNLS

theorem spectralRealHilbert_weak_subsequence {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] [TopologicalSpace.SeparableSpace E]
    (u : ℕ → E) (M : ℝ) (hu : ∀ n, ‖u n‖ ≤ M) :
    ∃ v : E, ‖v‖ ≤ M ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ L : E →L[ℝ] ℝ, Tendsto (fun n => L (u (φ n))) atTop (𝓝 (L v)) := by
  let R := InnerProductSpace.toDual ℝ E
  let w : ℕ → WeakDual ℝ E := fun n => (R (u n)).toWeakDual
  have hw (n : ℕ) : w n ∈ WeakDual.toStrongDual ⁻¹' Metric.closedBall 0 M := by
    change R (u n) ∈ Metric.closedBall 0 M
    simpa only [Metric.mem_closedBall,dist_zero_right,R.norm_map] using hu n
  obtain ⟨v',hv',φ,hφ,ht⟩ := (WeakDual.isSeqCompact_closedBall ℝ E 0 M) hw
  let v := R.symm v'.toStrongDual
  have hv : ‖v‖ ≤ M := by
    change ‖R.symm v'.toStrongDual‖ ≤ M
    rw [R.symm.norm_map]
    simpa only [mem_preimage,Metric.mem_closedBall,dist_zero_right] using hv'
  refine ⟨v,hv,φ,hφ,fun L => ?_⟩
  let x := R.symm L
  have hn (n : ℕ) : w (φ n) x=L (u (φ n)) := by
    change inner ℝ (u (φ n)) x=L (u (φ n))
    rw [real_inner_comm]
    exact InnerProductSpace.toDual_symm_apply
  have hvx : v' x=L v := by
    have he : R v=v'.toStrongDual := R.apply_symm_apply _
    change v'.toStrongDual x=L v
    rw [← he]
    change inner ℝ v x=L v
    rw [real_inner_comm]
    exact InnerProductSpace.toDual_symm_apply
  have h := (WeakDual.eval_continuous x).continuousAt.tendsto.comp ht
  simpa only [Function.comp_def,hn,hvx] using h

theorem spectralCompact_weakSequence {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (T : E →L[ℝ] F) (hT : IsCompactOperator T)
    (u : ℕ → E) (u₀ : E) (M : ℝ) (hu : ∀ n, ‖u n‖ ≤ M)
    (hweak : ∀ L : E →L[ℝ] ℝ, Tendsto (fun n => L (u n)) atTop (𝓝 (L u₀))) :
    Tendsto (fun n => T (u n)) atTop (𝓝 (T u₀)) := by
  have hb (n : ℕ) : ‖u n-u₀‖ ≤ M+‖u₀‖ :=
    (norm_sub_le _ _).trans (add_le_add (hu n) le_rfl)
  have hw (L : E →L[ℝ] ℝ) : Tendsto (fun n => L (u n-u₀)) atTop (𝓝 0) := by
    simpa only [map_sub,sub_self] using (hweak L).sub_const (L u₀)
  have h := spectralCompact_weakNull T hT (fun n => u n-u₀) (M+‖u₀‖) hb hw
  simpa only [map_sub,sub_add_cancel,zero_add] using h.add_const (T u₀)

end DefocusingNLS

end OAI
