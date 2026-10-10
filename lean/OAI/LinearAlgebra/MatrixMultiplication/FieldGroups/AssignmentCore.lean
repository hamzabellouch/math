import OAI.LinearAlgebra.MatrixMultiplication.FieldGroups.OrbitData

namespace OAI

/-! Group assignments, orbit counts and extraction capacities. -/

noncomputable section

namespace MatrixMultiplication.AllFieldGroupAssignmentRetention
open AllFieldHistory AllFieldHistoryGroupMasks AllFieldHistoryGroupedRecovery
open AllFieldGroupOrbitData JointCoarseHashing
attribute [local instance] Classical.propDecidable Classical.decEq
variable {K tick : ℕ}

def assigned (allocation : Allocation) (m : ℕ) (ε : ℝ) (sigma : Placement)
    (k : ℕ) (U : Finset (ZMod (37 ^ k)))
    (s : Sample (Pos (K := K) (tick := tick) allocation m sigma) k)
    (v : Variable (K := K) (tick := tick) allocation m sigma) : Option (Triple (Pos (K := K) (tick := tick) allocation m sigma)) :=
  (data allocation m ε sigma).actualAssignment k U
    (actualCompatible allocation m ε sigma) (actualUseful allocation m ε sigma)
    (actualKeep allocation m ε sigma) s v

def physicalAssignment (allocation : Allocation) (m : ℕ) (ε : ℝ) (sigma : Placement)
    (k : ℕ) (U : Finset (ZMod (37 ^ k)))
    (s : Sample (Pos (K := K) (tick := tick) allocation m sigma) k) :
    JointExtraction.Assignment (Raw (K := K) (tick := tick) allocation m sigma) (Raw (K := K) (tick := tick) allocation m sigma)
      (Raw (K := K) (tick := tick) allocation m sigma) (Triple (Pos (K := K) (tick := tick) allocation m sigma)) where
  x w := assigned allocation m ε sigma k U s (sigma.symm 0, w)
  y w := assigned allocation m ε sigma k U s (sigma.symm 1, w)
  z w := assigned allocation m ε sigma k U s (sigma.symm 2, w)

theorem assigned_spec (allocation : Allocation) (m : ℕ) (ε : ℝ) (sigma : Placement)
    (k : ℕ) (U : Finset (ZMod (37 ^ k)))
    (s : Sample (Pos (K := K) (tick := tick) allocation m sigma) k)
    (v : Variable (K := K) (tick := tick) allocation m sigma) (t : Triple (Pos (K := K) (tick := tick) allocation m sigma))
    (h : assigned allocation m ε sigma k U s v = some t) :
    t ∈ (data allocation m ε sigma).actualEligible k U s ∧
      actualCompatible allocation m ε sigma t v ∧ actualUseful allocation m ε sigma t v ∧
      ∀ f, f ∈ (data allocation m ε sigma).actualEligible k U s →
        actualCompatible allocation m ε sigma f v → f = t := by
  have hh := JointExtraction.retainAssignment_some _ _ v t h
  exact JointCoarseAssignment.assignUseful_spec _ _ _ v t hh

theorem assigned_some_idealSide (allocation : Allocation) (m : ℕ) (ε : ℝ)
    (sigma : Placement) (k : ℕ) (U : Finset (ZMod (37 ^ k)))
    (s : Sample (Pos (K := K) (tick := tick) allocation m sigma) k)
    (e : Targets (K := K) (tick := tick) allocation m sigma) (v : Variable (K := K) (tick := tick) allocation m sigma)
    (h : assigned allocation m ε sigma k U s v = some (coarse allocation m sigma e)) :
    groupIdealSide allocation m ε (sigma v.1) sigma e v.2 := by
  exact (actualUseful_coarse allocation m ε sigma e v).mp
    (assigned_spec allocation m ε sigma k U s v _ h).2.2.1

end MatrixMultiplication.AllFieldGroupAssignmentRetention

end

end OAI
