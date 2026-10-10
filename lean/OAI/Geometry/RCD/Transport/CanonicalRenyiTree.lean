import OAI.Geometry.RCD.Transport.RenyiNodeChildren

namespace OAI

/-! # Compatible finite restrictions of a fixed Rényi midpoint tree -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [SeparableSpace X] [CompleteSpace X]
attribute [local instance] pathBorel pathBorelSpace
variable {n : ℕ} {K q : ℝ}

def FollowsRenyiTree (S : ∀ a : RenyiTransportNode n X, RenyiNodeSplit K q a)
    (a : RenyiTransportNode n X) (ν : Time → Measure X) : ℕ → Prop
  | 0 => ν 0=a.left ∧ ν 1=a.right
  | m+1 => ν 0=a.left ∧ ν 1=a.right ∧
      ν midpointTime=(S a).plan.map (fun γ => γ midpointTime) ∧
      FollowsRenyiTree S (S a).leftNode (fun t => ν (lowerTime t)) m ∧
      FollowsRenyiTree S (S a).rightNode (fun t => ν (upperTime t)) m

theorem FollowsRenyiTree.congr {S : ∀ a : RenyiTransportNode n X, RenyiNodeSplit K q a}
    {a : RenyiTransportNode n X} {ν η : Time → Measure X} {m : ℕ}
    (h : FollowsRenyiTree S a ν m) (he : ∀ t, ν t=η t) : FollowsRenyiTree S a η m := by
  have hf := funext he
  rwa [←hf]

theorem FollowsRenyiTree.of_succ {S : ∀ a : RenyiTransportNode n X, RenyiNodeSplit K q a}
    {m : ℕ} : ∀ {a : RenyiTransportNode n X} {ν : Time → Measure X},
    FollowsRenyiTree S a ν (m+1) → FollowsRenyiTree S a ν m := by
  induction m with
  | zero => intro a ν h; exact ⟨h.1,h.2.1⟩
  | succ m ih =>
    intro a ν h
    exact ⟨h.1,h.2.1,h.2.2.1,ih h.2.2.2.1,ih h.2.2.2.2⟩

theorem FollowsRenyiTree.unique_grid
    {S : ∀ a : RenyiTransportNode n X, RenyiNodeSplit K q a} {m : ℕ} :
    ∀ {a : RenyiTransportNode n X} {ν η : Time → Measure X},
      FollowsRenyiTree S a ν m → FollowsRenyiTree S a η m →
      ∀ t∈dyadicGrid m, ν t=η t := by
  induction m with
  | zero =>
    intro a ν η hν hη t ht
    rcases ht with rfl | ht
    · exact hν.1.trans hη.1.symm
    · have he : t=1 := ht
      subst t
      exact hν.2.trans hη.2.symm
  | succ m ih =>
    intro a ν η hν hη t ht
    rcases ht with ⟨s,hs,rfl⟩ | ⟨s,hs,rfl⟩
    · exact ih hν.2.2.2.1 hη.2.2.2.1 s hs
    · exact ih hν.2.2.2.2 hη.2.2.2.2 s hs

end RegularPointCoordinates

end

end OAI
