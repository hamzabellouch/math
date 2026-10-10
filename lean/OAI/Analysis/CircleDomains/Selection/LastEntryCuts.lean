import OAI.Analysis.CircleDomains.Selection.FirstExitCuts

namespace OAI

/-! Last-entry collar cuts and the strict separation of the retained
middle fragment from the two endpoint tails. -/

open Set Function
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

variable {X : Type*} [MetricSpace X]

theorem reversedPath_zero (γ : C(PathTime, X)) : reversedPath γ ⊥ = γ ⊤ := by
  apply congrArg γ
  apply Subtype.ext
  change (1 : ℝ) - 0 = 1
  norm_num

theorem reversedPath_one (γ : C(PathTime, X)) : reversedPath γ ⊤ = γ ⊥ := by
  apply congrArg γ
  apply Subtype.ext
  change (1 : ℝ) - 1 = 0
  norm_num

def lastEntryTime (γ : C(PathTime, X)) (V : Set X) : PathTime :=
  unitInterval.symm (firstExitTime (reversedPath γ) V)

theorem lastEntry_frontier (γ : C(PathTime, X)) {V : Set X} (hV : IsOpen V)
    (hstart : γ ⊥ ∉ V) (hend : γ ⊤ ∈ V) : γ (lastEntryTime γ V) ∈ frontier V := by
  exact firstExit_frontier (reversedPath γ) hV
    ((reversedPath_zero γ).symm ▸ hend) ((reversedPath_one γ).symm ▸ hstart)

theorem lastEntry_final_segment (γ : C(PathTime, X)) {V : Set X} (hV : IsOpen V)
    (hstart : γ ⊥ ∉ V) (hend : γ ⊤ ∈ V) :
    MapsTo γ (Ici (lastEntryTime γ V)) (closure V) := by
  intro t ht
  have hle : unitInterval.symm t ≤ firstExitTime (reversedPath γ) V :=
    unitInterval.symm_le_comm.mpr ht
  have hm := firstExit_initial_segment (reversedPath γ) hV
    ((reversedPath_zero γ).symm ▸ hend) ((reversedPath_one γ).symm ▸ hstart) hle
  change γ (unitInterval.symm (unitInterval.symm t)) ∈ closure V at hm
  simpa only [unitInterval.symm_symm] using hm

theorem lastEntry_strict_nested (γ : C(PathTime, X)) {V W : Set X}
    (hV : IsOpen V) (hW : IsOpen W) (hVW : closure V ⊆ W)
    (hstart : γ ⊥ ∉ W) (hend : γ ⊤ ∈ V) :
    lastEntryTime γ W < lastEntryTime γ V := by
  exact unitInterval.symm_lt_symm.mpr
    (firstExit_strict_nested (reversedPath γ) hV hW hVW
      ((reversedPath_zero γ).symm ▸ hend) ((reversedPath_one γ).symm ▸ hstart))

theorem firstExit_lt_lastEntry (γ : C(PathTime, X)) {V W : Set X}
    (hV : IsOpen V) (hW : IsOpen W) (hdis : Disjoint (closure V) (closure W))
    (hstart : γ ⊥ ∈ V) (hend : γ ⊤ ∈ W) :
    firstExitTime γ V < lastEntryTime γ W := by
  have hstartW : γ ⊥ ∉ W := by
    intro h
    exact disjoint_left.mp hdis (subset_closure hstart) (subset_closure h)
  have hendV : γ ⊤ ∉ V := by
    intro h
    exact disjoint_left.mp hdis (subset_closure h) (subset_closure hend)
  by_contra hn
  exact disjoint_left.mp hdis
    (frontier_subset_closure (firstExit_frontier γ hV hstart hendV))
    (lastEntry_final_segment γ hW hstartW hend (le_of_not_gt hn))

end CircleDomainRigidity

end

end OAI
