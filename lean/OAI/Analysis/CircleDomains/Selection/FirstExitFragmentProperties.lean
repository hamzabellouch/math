import OAI.Analysis.CircleDomains.Selection.FirstExitFragmentArray

namespace OAI

/-! Frontier endpoints and vanishing endpoint tolls for actual first-exit
fragments. These discharge the geometric premises of fragment splicing. -/

open Set Function MeasureTheory
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [MeasurableSpace C(PathTime, X)]

omit [MeasurableSpace X] in
theorem firstExitFragmentArray_frontiers
    (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain)
    (Γ : ℕ → TaggedPhysicalPath d) (V : ℕ → Set X)
    (hcut : ∀n j, j ≤ n → firstExitTime (Γ n).1.val (V (j+1)) <
      firstExitTime (Γ n).1.val (V j))
    (hV : ∀j, IsOpen (V j)) (hanti : Antitone V)
    (hstart : ∀n, (Γ n).1.val ⊥ ∈ V (n+1)) (hend : ∀n, (Γ n).1.val ⊤ ∉ V 0)
    {n j : ℕ} (hj : j ≤ n) :
    (firstExitFragmentArray d hU Γ V hcut n j).1.val ⊥ ∈ frontier (V (j+1)) ∧
    (firstExitFragmentArray d hU Γ V hcut n j).1.val ⊤ ∈ frontier (V j) := by
  rw [(firstExitFragmentArray_endpoints d hU Γ V hcut hj).1,
    (firstExitFragmentArray_endpoints d hU Γ V hcut hj).2]
  constructor
  · exact firstExit_frontier (Γ n).1.val (hV (j+1))
      (hanti (Nat.add_le_add_right hj 1) (hstart n))
      (fun h => hend n (hanti (Nat.zero_le (j+1)) h))
  · exact firstExit_frontier (Γ n).1.val (hV j)
      (hanti (hj.trans (Nat.le_succ n)) (hstart n))
      (fun h => hend n (hanti (Nat.zero_le j) h))

omit [MeasurableSpace X] in
theorem firstExit_toll_zero
    (d : PathCodeData X Y) (Γ : ℕ → TaggedPhysicalPath d) (V : ℕ → Set X)
    (hV : ∀j, IsOpen (V j)) (hanti : Antitone V)
    (hstart : ∀n, (Γ n).1.val ⊥ ∈ V (n+1)) (hend : ∀n, (Γ n).1.val ⊤ ∉ V 0)
    (m : X → ℝ≥0∞) (hm : ∀j x, x ∈ frontier (V j) → m x = 0)
    (n j : ℕ) (hj : j ≤ n+1) :
    m ((Γ n).1.val (firstExitTime (Γ n).1.val (V j))) = 0 := by
  apply hm j
  exact firstExit_frontier (Γ n).1.val (hV j) (hanti hj (hstart n))
    (fun h => hend n (hanti (Nat.zero_le j) h))

end CircleDomainRigidity

end

end OAI
