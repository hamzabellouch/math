import OAI.Analysis.CircleDomains.Selection.FirstExitFragmentGeometry

namespace OAI

/-! The actual triangular array of initial collar fragments. Entries before
the relevant collar is reached use the old path and are never selected. -/

open Set Function MeasureTheory
open scoped ENNReal Topology

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace X] [MeasurableSpace C(PathTime, X)]

def firstExitFragmentArray (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain)
    (Γ : ℕ → TaggedPhysicalPath d) (V : ℕ → Set X)
    (hcut : ∀n j, j ≤ n → firstExitTime (Γ n).1.val (V (j+1)) <
      firstExitTime (Γ n).1.val (V j)) (n j : ℕ) : TaggedPhysicalPath d :=
  if hj : j ≤ n then restrictTaggedPhysicalPath d hU (Γ n) (hcut n j hj) else Γ n

omit [MeasurableSpace X] in
theorem firstExitFragmentArray_eq (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain)
    (Γ : ℕ → TaggedPhysicalPath d) (V : ℕ → Set X)
    (hcut : ∀n j, j ≤ n → firstExitTime (Γ n).1.val (V (j+1)) <
      firstExitTime (Γ n).1.val (V j)) {n j : ℕ} (hj : j ≤ n) :
    firstExitFragmentArray d hU Γ V hcut n j =
      restrictTaggedPhysicalPath d hU (Γ n) (hcut n j hj) := by
  simp only [firstExitFragmentArray, dite_eq_left hj]

omit [MeasurableSpace X] in
theorem firstExitFragmentArray_endpoints (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain)
    (Γ : ℕ → TaggedPhysicalPath d) (V : ℕ → Set X)
    (hcut : ∀n j, j ≤ n → firstExitTime (Γ n).1.val (V (j+1)) <
      firstExitTime (Γ n).1.val (V j)) {n j : ℕ} (hj : j ≤ n) :
    (firstExitFragmentArray d hU Γ V hcut n j).1.val ⊥ =
      (Γ n).1.val (firstExitTime (Γ n).1.val (V (j+1))) ∧
    (firstExitFragmentArray d hU Γ V hcut n j).1.val ⊤ =
      (Γ n).1.val (firstExitTime (Γ n).1.val (V j)) := by
  rw [firstExitFragmentArray_eq d hU Γ V hcut hj]
  exact ⟨restrictTaggedPhysicalPath_zero _ _ _ _, restrictTaggedPhysicalPath_one _ _ _ _⟩

omit [MeasurableSpace X] in
theorem firstExitFragmentArray_support (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain)
    (Γ : ℕ → TaggedPhysicalPath d) (V : ℕ → Set X)
    (hcut : ∀n j, j ≤ n → firstExitTime (Γ n).1.val (V (j+1)) <
      firstExitTime (Γ n).1.val (V j))
    (hV : ∀j, IsOpen (V j)) (hanti : Antitone V)
    (hstart : ∀n, (Γ n).1.val ⊥ ∈ V (n+1)) (hend : ∀n, (Γ n).1.val ⊤ ∉ V 0)
    {n j : ℕ} (hj : j ≤ n) :
    range (firstExitFragmentArray d hU Γ V hcut n j).1.val ⊆ closure (V j) := by
  rw [firstExitFragmentArray_eq d hU Γ V hcut hj, restrictTaggedPhysicalPath_range]
  rintro x ⟨t, ht, rfl⟩
  apply firstExit_initial_segment (Γ n).1.val (hV j)
    (hanti (show j ≤ n+1 by omega) (hstart n))
    (fun h => hend n (hanti (Nat.zero_le j) h))
  exact ht.2

variable [MeasurableSingletonClass X]

theorem firstExitFragmentArray_allowed (d : PathCodeData X Y) (hU : IsOpen d.quotientDomain)
    (Γ : ℕ → TaggedPhysicalPath d) (V : ℕ → Set X)
    (hcut : ∀n j, j ≤ n → firstExitTime (Γ n).1.val (V (j+1)) <
      firstExitTime (Γ n).1.val (V j))
    (ν : Measure X) [NullSingletonClass ν]
    (N : ∀n : ℕ, (Fin (n+1) → ℕ) → Set (Fin (n+1) → UnitAddCircle))
    (hΓ : ∀n, AllowedTaggedPath d ν N ((Γ n).1.val, (Γ n).2))
    (hpoint : ∀i x, volume {t | (t, x) ∈ d.levels i} ≤ d.levelWeights i x)
    {n j : ℕ} (hj : j ≤ n) :
    AllowedTaggedPath d ν N ((firstExitFragmentArray d hU Γ V hcut n j).1.val,
      (firstExitFragmentArray d hU Γ V hcut n j).2) := by
  rw [firstExitFragmentArray_eq d hU Γ V hcut hj]
  exact restrictTaggedPhysicalPath_allowed d hU ν N (Γ n) (hΓ n) hpoint (hcut n j hj)

end CircleDomainRigidity

end

end OAI
