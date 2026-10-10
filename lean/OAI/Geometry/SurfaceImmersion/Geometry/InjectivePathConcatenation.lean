import Mathlib.Topology.Path

namespace OAI

/-! Concatenating two embedded arcs meeting only at their common endpoint. -/
noncomputable section
open Set unitInterval
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {X : Type*} [TopologicalSpace X] {x y z : X}

theorem path_trans_injective (γ : Path x y) (δ : Path y z)
    (hγ : Function.Injective γ) (hδ : Function.Injective δ)
    (hsep : ∀ s t, γ s = δ t → s = 1 ∧ t = 0) : Function.Injective (γ.trans δ) := by
  intro s t h
  apply Subtype.ext
  rw [Path.trans_apply,Path.trans_apply] at h
  split_ifs at h with hs ht ht
  · have hv := congrArg (fun u : I => (u:ℝ)) (hγ h)
    dsimp only at hv
    linarith
  · obtain ⟨ha,hb⟩ := hsep _ _ h
    have ha' := congrArg (fun u : I => (u:ℝ)) ha
    have hb' := congrArg (fun u : I => (u:ℝ)) hb
    dsimp only at ha' hb'
    norm_num at ha' hb'
    linarith
  · obtain ⟨ha,hb⟩ := hsep _ _ h.symm
    have ha' := congrArg (fun u : I => (u:ℝ)) ha
    have hb' := congrArg (fun u : I => (u:ℝ)) hb
    dsimp only at ha' hb'
    norm_num at ha' hb'
    linarith
  · have hv := congrArg (fun u : I => (u:ℝ)) (hδ h)
    dsimp only at hv
    linarith

theorem path_trans_injective_of_range (γ : Path x y) (δ : Path y z)
    (hγ : Function.Injective γ) (hδ : Function.Injective δ)
    (hmeet : range γ ∩ range δ ⊆ {y}) : Function.Injective (γ.trans δ) := by
  apply path_trans_injective γ δ hγ hδ
  intro s t h
  have hy : γ s = y := mem_singleton_iff.mp (hmeet ⟨mem_range_self s,⟨t,h.symm⟩⟩)
  constructor
  · apply hγ
    simpa only [Path.target] using hy
  · apply hδ
    simpa only [Path.source] using h.symm.trans hy

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
