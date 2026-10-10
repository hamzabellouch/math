import OAI.Analysis.CircleDomains.Topology.SimpleLoopCircle

namespace OAI

/-! Two injective arcs that meet only at their prescribed endpoints
concatenate to a simple loop. -/

open Set Function
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

theorem two_arc_loop_injective_before_end {a b : ℂ} (p : Path a b) (q : Path b a)
    (hp : Injective p) (hq : Injective q)
    (hmeet : ∀ s t : PathTime, p s = q t → (s = 1 ∧ t = 0) ∨ (s = 0 ∧ t = 1)) :
    ∀ s t : PathTime, s < 1 → t < 1 → (p.trans q) s = (p.trans q) t → s = t := by
  intro s t hs1 ht1 he
  have hs' : (s : ℝ) < 1 := hs1
  have ht' : (t : ℝ) < 1 := ht1
  rw [Path.trans_apply, Path.trans_apply] at he
  split_ifs at he with hs ht
  · have h := congrArg Subtype.val (hp he)
    apply Subtype.ext
    change 2 * (s : ℝ) = 2 * (t : ℝ) at h
    linarith
  · rcases hmeet _ _ he with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · have h := congrArg Subtype.val hb
      change 2 * (t : ℝ) - 1 = 0 at h
      linarith
    · have h := congrArg Subtype.val hb
      change 2 * (t : ℝ) - 1 = 1 at h
      linarith
  · rcases hmeet _ _ he.symm with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · have h := congrArg Subtype.val hb
      change 2 * (s : ℝ) - 1 = 0 at h
      linarith
    · have h := congrArg Subtype.val hb
      change 2 * (s : ℝ) - 1 = 1 at h
      linarith
  · have h := congrArg Subtype.val (hq he)
    apply Subtype.ext
    change 2 * (s : ℝ) - 1 = 2 * (t : ℝ) - 1 at h
    linarith

end CircleDomainRigidity

end

end OAI
