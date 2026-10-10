import OAI.Analysis.CircleDomains.Selection.FirstExitCuts
import OAI.Analysis.CircleDomains.Selection.TaggedPhysicalRestriction

namespace OAI

/-! Ordering and support of the actual first-exit fragments in nested
collars. The order gives disjoint open time intervals for the cost budget. -/

open Set Function
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

theorem antitone_interval_interiors {α : Type*} [LinearOrder α] (a : ℕ → α) (ha : Antitone a) :
    Pairwise (Disjoint on fun j => Ioo (a (j+1)) (a j)) := by
  intro i j hij
  apply disjoint_left.mpr
  intro t hi hj
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · exact (hj.2.trans_le (ha (Nat.add_one_le_iff.mpr hlt))).not_ge hi.1.le
  · exact (hi.2.trans_le (ha (Nat.add_one_le_iff.mpr hgt))).not_ge hj.1.le

variable {X : Type*} [TopologicalSpace X]

theorem firstExitTime_antitone (γ : C(PathTime, X)) (V : ℕ → Set X)
    (hV : ∀j, IsOpen (V j)) (hanti : Antitone V) (hend : γ ⊤ ∉ V 0) :
    Antitone (fun j => firstExitTime γ (V j)) := by
  intro i j hij
  apply firstExit_nested γ (hV i) (hanti hij)
  exact fun h => hend (hanti (Nat.zero_le i) h)

theorem firstExitFragments_disjoint (γ : C(PathTime, X)) (V : ℕ → Set X)
    (hV : ∀j, IsOpen (V j)) (hanti : Antitone V) (hend : γ ⊤ ∉ V 0) :
    Pairwise (Disjoint on fun j => Ioo (firstExitTime γ (V (j+1))) (firstExitTime γ (V j))) :=
  antitone_interval_interiors _ (firstExitTime_antitone γ V hV hanti hend)

theorem firstExitFragments_strict (γ : C(PathTime, X)) (V : ℕ → Set X)
    (hV : ∀j, IsOpen (V j)) (hnest : ∀j, closure (V (j+1)) ⊆ V j)
    {n : ℕ} (hstart : γ ⊥ ∈ V (n+1)) (hend : γ ⊤ ∉ V 0) {j : ℕ} (hj : j ≤ n) :
    firstExitTime γ (V (j+1)) < firstExitTime γ (V j) := by
  have hanti : Antitone V := antitone_nat_of_succ_le (fun j => subset_closure.trans (hnest j))
  exact firstExit_strict_nested γ (hV (j+1)) (hV j) (hnest j)
    (hanti (Nat.add_le_add_right hj 1) hstart)
    (fun h => hend (hanti (Nat.zero_le j) h))

end CircleDomainRigidity

end

end OAI
