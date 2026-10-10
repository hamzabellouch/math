import OAI.LinearAlgebra.MatrixMultiplication.FieldGroups.AssignmentCore
import OAI.LinearAlgebra.MatrixMultiplication.FieldGroups.SourceSupport
import OAI.LinearAlgebra.MatrixMultiplication.FieldGroups.CompatibilityTransfer

namespace OAI

/-! Group assignments, orbit counts and extraction capacities. -/

noncomputable section

namespace MatrixMultiplication.AllFieldGroupAssignments

open AllFieldHistory AllFieldHistoryGroupMasks AllFieldHistoryGroupedRecovery
open AllFieldGroupOrbitData AllFieldGroupAssignmentRetention JointCoarseHashing
attribute [local instance] Classical.propDecidable

variable {K tick : ℕ}

theorem actualCompatible_own (allocation : Allocation) (m : ℕ) (ε : ℝ)
    (sigma : Placement) (t : Triple (Pos (K := K) (tick := tick) allocation m sigma))
    (v : Variable (K := K) (tick := tick) allocation m sigma)
    (hc : actualCompatible allocation m ε sigma t v) :
    tripleSide v.1 t = ownWord allocation m sigma v.2 := by
  obtain ⟨_, rfl, hcompatibility⟩ := hc
  exact hcompatibility.1

theorem physicalAssignment_coherent (F : Type*) [Field F]
    (allocation : Allocation) (m : ℕ) (ε : ℝ) (sigma : Placement)
    (k : ℕ) (U : Finset (ZMod (37 ^ k)))
    (sample : Sample (Pos (K := K) (tick := tick) allocation m sigma) k) :
    JointExtraction.Coherent (groupPreparedSource F allocation m ε sigma)
      (physicalAssignment allocation m ε sigma k U sample) := by
  intro x y z tx ty tz hT htx hty htz
  let a : Fin 3 → Raw (K := K) (tick := tick) allocation m sigma := ![x, y, z]
  let physicalTag : Fin 3 → Triple (Pos (K := K) (tick := tick) allocation m sigma) :=
    ![tx, ty, tz]
  let b : Fin 3 → Raw (K := K) (tick := tick) allocation m sigma := fun r => a (sigma r)
  let tag : Fin 3 → Triple (Pos (K := K) (tick := tick) allocation m sigma) :=
    fun r => physicalTag (sigma r)
  have hphysical (r : Fin 3) :
      assigned allocation m ε sigma k U sample (sigma.symm r, a r) =
        some (physicalTag r) := by
    fin_cases r
    · exact htx
    · exact hty
    · exact htz
  have hassign (r : Fin 3) :
      assigned allocation m ε sigma k U sample (r, b r) = some (tag r) := by
    simpa only [b, tag, sigma.symm_apply_apply] using hphysical (sigma r)
  have hspec (r : Fin 3) :=
    assigned_spec allocation m ε sigma k U sample (r, b r) (tag r) (hassign r)
  let d := data (K := K) (tick := tick) allocation m ε sigma
  let hx := JointMaskedSelection.OrbitData.xFlag k U sample
  let hy := JointMaskedSelection.OrbitData.yFlag k U sample
  let hz := d.zFlag k U sample
  have heligible (r : Fin 3) :=
    (JointCoarseAssignment.mem_eligible_iff d.ambient d.actualTargets hx hy hz (tag r)).mp
      (hspec r).1
  let observed : Triple (Pos (K := K) (tick := tick) allocation m sigma) :=
    reorder sigma (ownWord allocation m sigma x,
      ownWord allocation m sigma y, ownWord allocation m sigma z)
  have hword (r : Fin 3) :
      ownWord allocation m sigma (a r) =
        tripleSide r (ownWord allocation m sigma x,
          ownWord allocation m sigma y, ownWord allocation m sigma z) := by
    fin_cases r <;> rfl
  have hobserved (r : Fin 3) : tripleSide r observed = tripleSide r (tag r) := by
    calc
      tripleSide r observed = ownWord allocation m sigma (b r) := by
        rw [show observed = reorder sigma (ownWord allocation m sigma x,
          ownWord allocation m sigma y, ownWord allocation m sigma z) from rfl,
          tripleSide_reorder]
        exact (hword (sigma r)).symm
      _ = tripleSide r (tag r) :=
        (actualCompatible_own allocation m ε sigma (tag r) (r, b r) (hspec r).2.1).symm
  have hobsX : observed.1 = (tag 0).1 := hobserved 0
  have hobsY : observed.2.1 = (tag 1).2.1 := hobserved 1
  have hobsZ : observed.2.2 = (tag 2).2.2 := hobserved 2
  have hsurvives : JointCoarseAssignment.survives hx hy hz observed := by
    refine ⟨?_, ?_, ?_⟩
    · rw [hobsX]
      exact (heligible 0).2.2.1.1
    · rw [hobsY]
      exact (heligible 1).2.2.1.2.1
    · rw [hobsZ]
      exact (heligible 2).2.2.1.2.2
  have hsupport : observed ∈ d.ambient :=
    AllFieldGroupSourceSupport.prepared_source_support F allocation m ε sigma x y z hT
  have hobs : observed = tag 0 :=
    (heligible 0).2.2.2 observed hsupport hsurvives hobsX
  obtain ⟨e, he, huseX⟩ := (hspec 0).2.2.1
  have hcoarse : reorder sigma (ownWord allocation m sigma (a 0),
      ownWord allocation m sigma (a 1), ownWord allocation m sigma (a 2)) =
        coarse allocation m sigma e := hobs.trans he.symm
  have hraw : groupRawSource F allocation m sigma (a 0) (a 1) (a 2) ≠ 0 :=
    AllFieldGroupSourceSupport.raw_nonzero F allocation m ε sigma x y z hT
  have hcompY : actualCompatible allocation m ε sigma (tag 0) (1, b 1) :=
    ⟨e, he, AllFieldGroupCompatibilityTransfer.transferY F allocation m ε sigma e a
      hraw hcoarse huseX⟩
  have h01 : tag 0 = tag 1 := (hspec 1).2.2.2 (tag 0) (hspec 0).1 hcompY
  have huseY : groupIdealSide allocation m ε (sigma 1) sigma e (b 1) := by
    apply (actualUseful_coarse allocation m ε sigma e (1, b 1)).mp
    rw [he, h01]
    exact (hspec 1).2.2.1
  have hcompZ : actualCompatible allocation m ε sigma (tag 0) (2, b 2) :=
    ⟨e, he, AllFieldGroupCompatibilityTransfer.transferZ F allocation m ε sigma e a
      hraw hcoarse huseX huseY⟩
  have h02 : tag 0 = tag 2 := (hspec 2).2.2.2 (tag 0) (hspec 0).1 hcompZ
  have htag (r : Fin 3) : tag r = tag 0 := by
    fin_cases r
    · rfl
    · exact h01.symm
    · exact h02.symm
  have hphysicalTag (r : Fin 3) : physicalTag r = tag 0 := by
    simpa only [tag, sigma.apply_symm_apply] using htag (sigma.symm r)
  exact ⟨(hphysicalTag 0).trans (hphysicalTag 1).symm,
    (hphysicalTag 0).trans (hphysicalTag 2).symm⟩

end MatrixMultiplication.AllFieldGroupAssignments

end

end OAI
