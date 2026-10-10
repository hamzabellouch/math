import OAI.LinearAlgebra.MatrixMultiplication.FieldGroups.AssignmentCore
import OAI.LinearAlgebra.MatrixMultiplication.FieldGroups.AdmissibilityCore
import OAI.LinearAlgebra.MatrixMultiplication.FieldGroups.Compatibility
import OAI.LinearAlgebra.MatrixMultiplication.JointExtraction.MaskedGoodSelection

namespace OAI

/-! Group assignments, orbit counts and extraction capacities. -/

noncomputable section

namespace MatrixMultiplication.AllFieldGroupAssignmentRetention
open AllFieldHistory AllFieldHistoryGroupMasks AllFieldHistoryGroupedRecovery
open AllFieldGroupOrbitData JointCoarseHashing
attribute [local instance] Classical.propDecidable Classical.decEq
variable {K tick : ℕ}

theorem good_failure_fraction_le (allocation : Allocation) (m : ℕ) (ε : ℝ)
    (sigma : Placement) (k : ℕ) (U : Finset (ZMod (37 ^ k)))
    (hAP : ∀ x ∈ U, ∀ y ∈ U, ∀ z ∈ U, x + y = 2 * z → x = z ∧ y = z)
    (N : ℝ) (s : Sample (Pos (K := K) (tick := tick) allocation m sigma) k)
    (e : Targets (K := K) (tick := tick) allocation m sigma)
    (hg : (data (K := K) (tick := tick) allocation m ε sigma).Good k U N e s)
    (o : Orbit (K := K) (tick := tick) allocation m sigma) (ho : o ∈ (data (K := K) (tick := tick) allocation m ε sigma).orbits e) :
    ((((data (K := K) (tick := tick) allocation m ε sigma).passing e o).filter
      (fun v => assigned (K := K) (tick := tick) allocation m ε sigma k U s v ≠ some (coarse (K := K) (tick := tick) allocation m sigma e))).card : ℝ) /
        (((data (K := K) (tick := tick) allocation m ε sigma).full e o).card : ℝ) ≤ 1 / N := by
  have ha (v : Variable (K := K) (tick := tick) allocation m sigma)
      (hv : v ∈ (data (K := K) (tick := tick) allocation m ε sigma).passing e o) :
      Admissible (K := K) (tick := tick) allocation m ε sigma v.1 e v.2 :=
    AllFieldGroupAdmissible.full_admissible (K := K) (tick := tick) allocation m ε sigma e o ho v
      ((mem_passing (K := K) (tick := tick) allocation m ε sigma e o v).mp hv).1
  have hc (v : Variable (K := K) (tick := tick) allocation m sigma)
      (hv : v ∈ (data (K := K) (tick := tick) allocation m ε sigma).passing e o) :
      Compatible (K := K) (tick := tick) allocation m ε sigma v.1 e v.2 :=
    AllFieldGroupCompatibility.admissible_compatible (K := K) (tick := tick) allocation m ε sigma v.1 e v.2 (ha v hv)
  have hh := (data (K := K) (tick := tick) allocation m ε sigma).good_passing_actual_failure_fraction_le k U hAP N e o ho s hg
    (actualCompatible (K := K) (tick := tick) allocation m ε sigma) (actualUseful (K := K) (tick := tick) allocation m ε sigma)
    (actualKeep (K := K) (tick := tick) allocation m ε sigma)
    (fun v hv => (actualCompatible_coarse (K := K) (tick := tick) allocation m ε sigma e v).mpr (hc v hv))
    (fun v hv => (actualUseful_coarse (K := K) (tick := tick) allocation m ε sigma e v).mpr (ha v hv).1)
    (fun v hv => ((mem_passing (K := K) (tick := tick) allocation m ε sigma e o v).mp hv).2)
    (fun v hv f _ hn hcomp => competitor_coverage (K := K) (tick := tick) allocation m ε sigma e o v (hc v hv) f hn hcomp)

  rw [Finset.filter_congr_decidable] at hh
  exact hh

end MatrixMultiplication.AllFieldGroupAssignmentRetention

end

end OAI
