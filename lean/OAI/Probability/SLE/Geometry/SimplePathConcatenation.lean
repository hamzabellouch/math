import Mathlib.Topology.Path

namespace OAI

/-! Injectivity of two simple paths joined only at their common endpoint. -/
noncomputable section
open Set Function
open scoped unitInterval

namespace SLEExactGauge

theorem path_trans_injective {X : Type*} [TopologicalSpace X] {a b c : X}
    (p : Path a b) (q : Path b c) (hp : Injective p) (hq : Injective q)
    (hcross : ∀ s t, p s=q t → s=1 ∧ t=0) : Injective (p.trans q) := by
  intro s t he
  rw [Path.trans_apply,Path.trans_apply] at he
  split_ifs at he with hs ht ht
  · have hh := congrArg (fun u : unitInterval => (u:ℝ)) (hp he)
    apply Subtype.ext
    dsimp only at hh
    linarith
  · obtain ⟨h₁,h₂⟩ := hcross _ _ he
    have h₁' := congrArg (fun u : unitInterval => (u:ℝ)) h₁
    have h₂' := congrArg (fun u : unitInterval => (u:ℝ)) h₂
    apply Subtype.ext
    dsimp only at h₁' h₂'
    norm_num at h₁' h₂'
    linarith
  · obtain ⟨h₁,h₂⟩ := hcross _ _ he.symm
    have h₁' := congrArg (fun u : unitInterval => (u:ℝ)) h₁
    have h₂' := congrArg (fun u : unitInterval => (u:ℝ)) h₂
    apply Subtype.ext
    dsimp only at h₁' h₂'
    norm_num at h₁' h₂'
    linarith
  · have hh := congrArg (fun u : unitInterval => (u:ℝ)) (hq he)
    apply Subtype.ext
    dsimp only at hh
    linarith

end SLEExactGauge

end

end OAI
