import OAI.NumberTheory.Ostmann.Construction.FullAtomWeightSupport

namespace OAI

/-! # A nonzero full coefficient uses the forced integer pivot -/

namespace Ostmann

open scoped BigOperators Classical

theorem fullAtomTransferWeight_forced_node {I : Type*} [Fintype I]
    (role : I → CopyScheduleRole) (childBound pivotBound : ℕ → ℕ)
    (ranges : (j : ℕ) → List (ScheduleAtomRange role j))
    (leaf : ScheduleAtomState role → ℤ → ℂ) (n : ℕ)
    (x : CopyScheduleAtoms role (n + 1) → ℕ) (s : ℤ) (t t' : FrequencyTree ℤ n) (M : ℕ)
    (hs : s ≠ 0)
    (hrel : frequencyRoot n t * (scheduleAtomRight role ⟨n + 1, x⟩ : ℤ) -
      frequencyRoot n t' * (scheduleAtomLeft role ⟨n + 1, x⟩ : ℤ) = s * M)
    (hw : fullAtomTransferWeight role childBound pivotBound ranges leaf (n + 1) x (s, t, t') ≠ 0) :
    ValidTransferNode (scheduleAtomSystem role childBound pivotBound)
      ⟨n + 1, x⟩ s (frequencyRoot n t) (frequencyRoot n t') M ∧
      fullAtomRootGuard role ranges n x M s := by
  obtain ⟨hg, Q, hQ, _, _⟩ := fullAtomTransferWeight_support role childBound pivotBound ranges leaf
    (n + 1) x (s, t, t') hw
  have hMQ : (M : ℤ) = Q := mul_left_cancel₀ hs (hrel.symm.trans hQ.relation)
  have he : M = Q := Int.ofNat_inj.mp hMQ
  subst Q
  exact ⟨hQ, ((fullAtomWeightGuard_node role childBound pivotBound ranges n x (s, t, t') M hQ).mp hg).1⟩

end Ostmann

end OAI
