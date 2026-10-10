import OAI.LinearAlgebra.MatrixMultiplication.FieldGroups.OrbitData

namespace OAI

/-! Group assignments, orbit counts and extraction capacities. -/

noncomputable section

namespace MatrixMultiplication.AllFieldGroupSourceSupport

open MatrixMultiplication.Foundation AllFieldHistory AllFieldHistorySupport
open AllFieldHistoryChildLaws AllFieldHistoryGroupMasks AllFieldHistoryGroupedRecovery
open AllFieldGroupOrbitData JointPopulation JointCanonicalization JointCanonicalCW
open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {K tick : ℕ}

theorem masks_of_prepared (F : Type*) [CommRing F] (allocation : Allocation)
    (m : ℕ) (ε : ℝ) (sigma : Placement)
    (x y z : GroupRaw (K := K) (tick := tick) allocation m sigma)
    (hT : groupPreparedSource F allocation m ε sigma x y z ≠ 0) :
    completeKeep allocation m ε 0 sigma x ∧
      completeKeep allocation m ε 1 sigma y ∧
      completeKeep allocation m ε 2 sigma z := by
  by_contra hn
  apply hT
  exact ite_eq_right hn

theorem raw_nonzero (F : Type*) [CommRing F] (allocation : Allocation)
    (m : ℕ) (ε : ℝ) (sigma : Placement)
    (x y z : GroupRaw (K := K) (tick := tick) allocation m sigma)
    (hT : groupPreparedSource F allocation m ε sigma x y z ≠ 0) :
    groupRawSource F allocation m sigma x y z ≠ 0 := by
  have hm := masks_of_prepared F allocation m ε sigma x y z hT
  simpa only [groupPreparedSource, ExactRecovery.delete, ite_eq_left hm] using hT

theorem marginal_sideMask (allocation : Allocation) (m : ℕ) (side : Fin 3)
    (sigma : Placement) (w : GroupRaw (K := K) (tick := tick) allocation m sigma)
    (hm : marginal allocation m side sigma w) :
    JointCanonicalMixed.sideMask (groupCounts allocation m sigma)
      (fun h => activeHalfLength h.val) (fun h => activeHalfLength h.val)
      (fun h => AllFieldHistoryRecovery.halfLength_le_eight h.val) side w := by
  intro h a
  exact (hm h a).trans
    (marginal_population_eq (groupCounts allocation m sigma)
      (projectTarget allocation m sigma (canonicalTarget (activeCounts allocation m)))
      (canonicalTarget (groupCounts allocation m sigma)) h side a)

theorem marginal_source_nonzero (F : Type*) [CommRing F] (allocation : Allocation)
    (m : ℕ) (ε : ℝ) (sigma : Placement)
    (x y z : GroupRaw (K := K) (tick := tick) allocation m sigma)
    (hT : groupPreparedSource F allocation m ε sigma x y z ≠ 0) :
    JointCanonicalMixed.maskedSource (F := F) (groupCounts allocation m sigma)
      (fun h => activeHalfLength h.val) (fun h => activeHalfLength h.val)
      (fun h => activeParentShape h.val) (fun _ => true)
      (fun h => AllFieldHistoryRecovery.halfLength_le_eight h.val) x y z ≠ 0 := by
  have hm := masks_of_prepared F allocation m ε sigma x y z hT
  have hx := marginal_sideMask allocation m 0 sigma x hm.1.1
  have hy := marginal_sideMask allocation m 1 sigma y hm.2.1.1
  have hz := marginal_sideMask allocation m 2 sigma z hm.2.2.1
  rw [JointCanonicalMixed.maskedSource, ExactRecovery.delete,
    ite_eq_left (And.intro hx (And.intro hy hz))]
  exact raw_nonzero F allocation m ε sigma x y z hT

theorem prepared_source_support (F : Type*) [CommRing F] (allocation : Allocation)
    (m : ℕ) (ε : ℝ) (sigma : Placement)
    (x y z : GroupRaw (K := K) (tick := tick) allocation m sigma)
    (hT : groupPreparedSource F allocation m ε sigma x y z ≠ 0) :
    reorder sigma
      (ownWord allocation m sigma x, ownWord allocation m sigma y,
        ownWord allocation m sigma z) ∈ ambient allocation m sigma := by
  apply Finset.mem_image.mpr
  refine ⟨(ownWord allocation m sigma x, ownWord allocation m sigma y,
    ownWord allocation m sigma z), ?_, rfl⟩
  exact JointCanonicalMixed.maskedSource_support (groupCounts allocation m sigma)
    (fun h => activeHalfLength h.val) (fun h => activeHalfLength h.val)
    (fun h => activeParentShape h.val) (fun _ => true)
    (fun h => AllFieldHistoryRecovery.halfLength_le_eight h.val) x y z
    (marginal_source_nonzero F allocation m ε sigma x y z hT)

end MatrixMultiplication.AllFieldGroupSourceSupport

end

end OAI
