import OAI.Analysis.CircleDomains.Selection.LastEntryFragmentArray

namespace OAI

/-! Final fragment endpoints lie on their actual collars and carry zero
cut toll whenever the collars do. -/

open Set Function MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace C(PathTime, X)]

theorem lastEntryFragmentArray_frontiers
    (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain)
    (Γ : ℕ → TaggedPhysicalPath d) (W : ℕ → Set X)
    (hcut : ∀n j, j ≤ n → lastEntryTime (Γ n).1.val (W j) < lastEntryTime (Γ n).1.val (W (j+1)))
    (hW : ∀j, IsOpen (W j)) (hanti : Antitone W)
    (hstart : ∀n, (Γ n).1.val ⊥ ∉ W 0) (hend : ∀n, (Γ n).1.val ⊤ ∈ W (n+1))
    {n j : ℕ} (hj : j ≤ n) :
    (lastEntryFragmentArray d hU Γ W hcut n j).1.val ⊥ ∈ frontier (W j) ∧
    (lastEntryFragmentArray d hU Γ W hcut n j).1.val ⊤ ∈ frontier (W (j+1)) := by
  rw [(lastEntryFragmentArray_endpoints d hU Γ W hcut hj).1,
    (lastEntryFragmentArray_endpoints d hU Γ W hcut hj).2]
  constructor
  · exact lastEntry_frontier (Γ n).1.val (hW j)
      (fun h => hstart n (hanti (Nat.zero_le j) h))
      (hanti (hj.trans (Nat.le_succ n)) (hend n))
  · exact lastEntry_frontier (Γ n).1.val (hW (j+1))
      (fun h => hstart n (hanti (Nat.zero_le (j+1)) h))
      (hanti (Nat.add_le_add_right hj 1) (hend n))

theorem lastEntry_toll_zero
    (d : PathCodeData X Y) (Γ : ℕ → TaggedPhysicalPath d) (W : ℕ → Set X)
    (hW : ∀j, IsOpen (W j)) (hanti : Antitone W)
    (hstart : ∀n, (Γ n).1.val ⊥ ∉ W 0) (hend : ∀n, (Γ n).1.val ⊤ ∈ W (n+1))
    (m : X → ℝ≥0∞) (hm : ∀j x, x ∈ frontier (W j) → m x = 0)
    (n j : ℕ) (hj : j ≤ n+1) :
    m ((Γ n).1.val (lastEntryTime (Γ n).1.val (W j))) = 0 := by
  apply hm j
  exact lastEntry_frontier (Γ n).1.val (hW j)
    (fun h => hstart n (hanti (Nat.zero_le j) h)) (hanti hj (hend n))

end CircleDomainRigidity

end

end OAI
