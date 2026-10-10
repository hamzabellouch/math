import OAI.Analysis.CircleDomains.Selection.TwoEndedFragmentGeometry
import OAI.Analysis.CircleDomains.Selection.FirstExitFragmentArray

namespace OAI

/-! Actual final collar fragments, in the original time direction. -/

open Set Function MeasureTheory
open scoped ENNReal Topology

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [MeasurableSpace C(PathTime, X)]

def lastEntryFragmentArray (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain)
    (Γ : ℕ → TaggedPhysicalPath d) (W : ℕ → Set X)
    (hcut : ∀n j, j ≤ n → lastEntryTime (Γ n).1.val (W j) <
      lastEntryTime (Γ n).1.val (W (j+1))) (n j : ℕ) : TaggedPhysicalPath d :=
  if hj : j ≤ n then restrictTaggedPhysicalPath d hU (Γ n) (hcut n j hj) else Γ n

omit [MeasurableSpace X] in
theorem lastEntryFragmentArray_eq (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain)
    (Γ : ℕ → TaggedPhysicalPath d) (W : ℕ → Set X)
    (hcut : ∀n j, j ≤ n → lastEntryTime (Γ n).1.val (W j) <
      lastEntryTime (Γ n).1.val (W (j+1))) {n j : ℕ} (hj : j ≤ n) :
    lastEntryFragmentArray d hU Γ W hcut n j =
      restrictTaggedPhysicalPath d hU (Γ n) (hcut n j hj) := by
  simp only [lastEntryFragmentArray, dite_eq_left hj]

omit [MeasurableSpace X] in
theorem lastEntryFragmentArray_endpoints (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain)
    (Γ : ℕ → TaggedPhysicalPath d) (W : ℕ → Set X)
    (hcut : ∀n j, j ≤ n → lastEntryTime (Γ n).1.val (W j) <
      lastEntryTime (Γ n).1.val (W (j+1))) {n j : ℕ} (hj : j ≤ n) :
    (lastEntryFragmentArray d hU Γ W hcut n j).1.val ⊥ =
      (Γ n).1.val (lastEntryTime (Γ n).1.val (W j)) ∧
    (lastEntryFragmentArray d hU Γ W hcut n j).1.val ⊤ =
      (Γ n).1.val (lastEntryTime (Γ n).1.val (W (j+1))) := by
  rw [lastEntryFragmentArray_eq d hU Γ W hcut hj]
  exact ⟨restrictTaggedPhysicalPath_zero _ _ _ _, restrictTaggedPhysicalPath_one _ _ _ _⟩

omit [MeasurableSpace X] in
theorem lastEntryFragmentArray_support (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain)
    (Γ : ℕ → TaggedPhysicalPath d) (W : ℕ → Set X)
    (hcut : ∀n j, j ≤ n → lastEntryTime (Γ n).1.val (W j) <
      lastEntryTime (Γ n).1.val (W (j+1)))
    (hW : ∀j, IsOpen (W j)) (hanti : Antitone W)
    (hstart : ∀n, (Γ n).1.val ⊥ ∉ W 0) (hend : ∀n, (Γ n).1.val ⊤ ∈ W (n+1))
    {n j : ℕ} (hj : j ≤ n) :
    range (lastEntryFragmentArray d hU Γ W hcut n j).1.val ⊆ closure (W j) := by
  rw [lastEntryFragmentArray_eq d hU Γ W hcut hj, restrictTaggedPhysicalPath_range]
  rintro x ⟨t, ht, rfl⟩
  apply lastEntry_final_segment (Γ n).1.val (hW j)
    (fun h => hstart n (hanti (Nat.zero_le j) h))
    (hanti (hj.trans (Nat.le_succ n)) (hend n))
  exact ht.1

variable [MeasurableSingletonClass X]

theorem lastEntryFragmentArray_allowed (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain)
    (Γ : ℕ → TaggedPhysicalPath d) (W : ℕ → Set X)
    (hcut : ∀n j, j ≤ n → lastEntryTime (Γ n).1.val (W j) <
      lastEntryTime (Γ n).1.val (W (j+1)))
    (ν : Measure X) [NullSingletonClass ν]
    (N : ∀n : ℕ, (Fin (n+1) → ℕ) → Set (Fin (n+1) → UnitAddCircle))
    (hΓ : ∀n, AllowedTaggedPath d ν N ((Γ n).1.val, (Γ n).2))
    (hpoint : ∀i x, volume {t | (t, x) ∈ d.levels i} ≤ d.levelWeights i x)
    {n j : ℕ} (hj : j ≤ n) :
    AllowedTaggedPath d ν N ((lastEntryFragmentArray d hU Γ W hcut n j).1.val,
      (lastEntryFragmentArray d hU Γ W hcut n j).2) := by
  rw [lastEntryFragmentArray_eq d hU Γ W hcut hj]
  exact restrictTaggedPhysicalPath_allowed d hU ν N (Γ n) (hΓ n) hpoint (hcut n j hj)

end CircleDomainRigidity

end

end OAI
