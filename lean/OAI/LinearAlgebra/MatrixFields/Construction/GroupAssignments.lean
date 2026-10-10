import Mathlib
import OAI.LinearAlgebra.MatrixFields.Construction.GroupAssignmentRetention
import OAI.LinearAlgebra.MatrixFields.Histories.CWShapePhysicalPermutation
import OAI.LinearAlgebra.MatrixFields.Parameters.GroupStatisticComplement
import OAI.LinearAlgebra.MatrixFields.Tensors.JointPopulationCWNonzero

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
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
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.AllFieldGroupCompatibilityTransfer

open MatrixMultiplication.Foundation AllFieldHistory AllFieldHistoryChildLaws
open AllFieldHistoryGroupMasks AllFieldHistoryGroupedRecovery AllFieldGroupOrbitData
open JointPopulation JointCanonicalization JointCanonicalCW CWStrands InheritedMasks
open scoped BigOperators

attribute [local instance] Classical.propDecidable

variable {K tick : ℕ}

theorem physical_coarseMask (allocation : Allocation) (m : ℕ) (sigma : Placement)
    (e : Targets (K := K) (tick := tick) allocation m sigma)
    (a : Fin 3 → Raw (K := K) (tick := tick) allocation m sigma)
    (hcoarse : reorder sigma (ownWord allocation m sigma (a 0),
      ownWord allocation m sigma (a 1), ownWord allocation m sigma (a 2)) =
        AllFieldGroupOrbitData.coarse allocation m sigma e)
    (s : Fin 3) :
    coarseMask (Counts allocation m sigma)
      (fun h => Fin (activeHalfLength h.val) → Fin 7)
      (fun h => Fin (activeHalfLength h.val) → Fin 7)
      groupCoarse s e (a s) := by
  have ht := reorder_injective sigma hcoarse
  intro h i
  have he := congrArg (fun t => tripleSide s t ⟨h, i⟩) ht
  fin_cases s <;> exact he

def halfShape {sigma : Placement} (right : Bool) (h : ActiveOrder K tick sigma)
    (u : JointPopulation.Shape) : Fin 3 → ℕ :=
  if right then activeParentShape h.val - shapeNat u else shapeNat u

def halfLaw {sigma : Placement} (right : Bool) (side : Fin 3) (h : ActiveOrder K tick sigma)
    (u : JointPopulation.Shape) : Statistic h.val → ℝ :=
  if right then rightLaw h.val u side else leftLaw h.val u side

theorem physical_half_product_nonzero (F : Type*) [Field F]
    (allocation : Allocation) (m : ℕ) (sigma : Placement)
    (e : Targets (K := K) (tick := tick) allocation m sigma)
    (a : Fin 3 → Raw (K := K) (tick := tick) allocation m sigma)
    (hraw : groupRawSource F allocation m sigma (a 0) (a 1) (a 2) ≠ 0)
    (hcoarse : reorder sigma (ownWord allocation m sigma (a 0),
      ownWord allocation m sigma (a 1), ownWord allocation m sigma (a 2)) =
        AllFieldGroupOrbitData.coarse allocation m sigma e)
    (right : Bool) (h : ActiveOrder K tick sigma) (u : JointPopulation.Shape)
    (hu : 0 < Counts allocation m sigma h u) :
    (∏ i : Class (Counts allocation m sigma) e h u,
      shapeTensor (F := F) (Fin (activeHalfLength h.val)) (halfShape right h u)
        (if right then (a 0 h i.val).2 else (a 0 h i.val).1)
        (if right then (a 1 h i.val).2 else (a 1 h i.val).1)
        (if right then (a 2 h i.val).2 else (a 2 h i.val).1)) ≠ 0 := by
  have hsupp : ∀ (h : ActiveOrder K tick sigma) (u : JointPopulation.Shape),
      0 < Counts allocation m sigma h u →
      ∀ s, shapeNat u s ≤ activeParentShape h.val s := by
    intro h u hu s
    exact jointCounts_support_le allocation m h.val.val u hu s
  have hsource : sourceTensor (F := F) (Counts (K := K) (tick := tick) allocation m sigma)
      (Left (fun h => activeHalfLength h.val)) (Right (fun h => activeHalfLength h.val))
      (parentTensor (F := F) (fun h : ActiveOrder K tick sigma => activeHalfLength h.val)
        (fun h : ActiveOrder K tick sigma => activeHalfLength h.val)
        (fun h : ActiveOrder K tick sigma => activeParentShape h.val))
      (a 0) (a 1) (a 2) ≠ 0 := by
    exact hraw
  have hp := JointPopulationCWNonzero.class_half_products_nonzero
    (Counts allocation m sigma) (fun h => activeHalfLength h.val)
    (fun h => activeHalfLength h.val) (fun h => activeParentShape h.val)
    (fun h => AllFieldHistoryRecovery.halfLength_le_eight h.val) hsupp e
    (a 0) (a 1) (a 2) hsource
    (physical_coarseMask allocation m sigma e a hcoarse 0)
    (physical_coarseMask allocation m sigma e a hcoarse 1)
    (physical_coarseMask allocation m sigma e a hcoarse 2) h u hu
  cases right
  · exact hp.1
  · exact hp.2

theorem priority_half_product_nonzero (F : Type*) [Field F]
    (allocation : Allocation) (m : ℕ) (sigma : Placement)
    (e : Targets (K := K) (tick := tick) allocation m sigma)
    (a : Fin 3 → Raw (K := K) (tick := tick) allocation m sigma)
    (hraw : groupRawSource F allocation m sigma (a 0) (a 1) (a 2) ≠ 0)
    (hcoarse : reorder sigma (ownWord allocation m sigma (a 0),
      ownWord allocation m sigma (a 1), ownWord allocation m sigma (a 2)) =
        AllFieldGroupOrbitData.coarse allocation m sigma e)
    (right : Bool) (h : ActiveOrder K tick sigma) (u : JointPopulation.Shape)
    (hu : 0 < Counts allocation m sigma h u) :
    (∏ i : Class (Counts allocation m sigma) e h u,
      shapeTensor (F := F) (Fin (activeHalfLength h.val)) (halfShape right h u ∘ sigma)
        (if right then (a (sigma 0) h i.val).2 else (a (sigma 0) h i.val).1)
        (if right then (a (sigma 1) h i.val).2 else (a (sigma 1) h i.val).1)
        (if right then (a (sigma 2) h i.val).2 else (a (sigma 2) h i.val).1)) ≠ 0 := by
  have he := fun i : Class (Counts allocation m sigma) e h u =>
    CWShapePhysicalPermutation.shapeTensor_permute (F := F) sigma (halfShape right h u)
      (fun s => if right then (a s h i.val).2 else (a s h i.val).1)
  simp_rw [he]
  exact physical_half_product_nonzero F allocation m sigma e a hraw hcoarse right h u hu

theorem useful_half_window (allocation : Allocation) (m : ℕ) (ε : ℝ)
    (sigma : Placement) (s : Fin 3)
    (e : Targets (K := K) (tick := tick) allocation m sigma)
    (w : Raw (K := K) (tick := tick) allocation m sigma)
    (hw : groupIdealSide allocation m ε s sigma e w)
    (right : Bool) (h : ActiveOrder K tick sigma) (u : JointPopulation.Shape)
    (hu : 0 < Counts allocation m sigma h u) :
    typeWindow (halfLaw right s h u) (AllFieldHistoryMasks.childWidth ε h.val)
      (fun i : Class (Counts allocation m sigma) e h u =>
        statistic h.val (if right then (w h i.val).2 else (w h i.val).1)) := by
  cases right
  · exact (hw.2 h u hu).1
  · exact (hw.2 h u hu).2

theorem own_coarse_guard (allocation : Allocation) (m : ℕ) (sigma : Placement)
    (e : Targets (K := K) (tick := tick) allocation m sigma)
    (a : Fin 3 → Raw (K := K) (tick := tick) allocation m sigma)
    (hcoarse : reorder sigma (ownWord allocation m sigma (a 0),
      ownWord allocation m sigma (a 1), ownWord allocation m sigma (a 2)) =
        AllFieldGroupOrbitData.coarse allocation m sigma e)
    (side : Fin 3) :
    tripleSide side (AllFieldGroupOrbitData.coarse allocation m sigma e) =
      ownWord allocation m sigma (a (sigma side)) := by
  rw [← hcoarse, tripleSide_reorder]
  generalize sigma side = s
  fin_cases s <;> rfl

theorem transferY (F : Type*) [Field F] (allocation : Allocation) (m : ℕ) (ε : ℝ)
    (sigma : Placement) (e : Targets (K := K) (tick := tick) allocation m sigma)
    (a : Fin 3 → Raw (K := K) (tick := tick) allocation m sigma)
    (hraw : groupRawSource F allocation m sigma (a 0) (a 1) (a 2) ≠ 0)
    (hcoarse : reorder sigma (ownWord allocation m sigma (a 0),
      ownWord allocation m sigma (a 1), ownWord allocation m sigma (a 2)) =
        AllFieldGroupOrbitData.coarse allocation m sigma e)
    (huseX : groupIdealSide allocation m ε (sigma 0) sigma e (a (sigma 0))) :
    Compatible allocation m ε sigma 1 e (a (sigma 1)) := by
  refine ⟨own_coarse_guard allocation m sigma e a hcoarse 1, ?_⟩
  intro right h u hd
  apply JointPopulationCompatibility.shape_count_window_of_typeWindow
    (Counts allocation m sigma) e h u _ _ _
  intro hu
  have hz : halfShape right h u (sigma 2) = 0 := by
    cases right <;> simpa [designated, halfShape, shapeNat] using hd.2
  have hw := CWStrandCompatibility.zeroZ_transfer
    (fun _ : Class (Counts allocation m sigma) e h u => halfShape right h u ∘ sigma)
    (fun i => if right then (a (sigma 0) h i.val).2 else (a (sigma 0) h i.val).1)
    (fun i => if right then (a (sigma 1) h i.val).2 else (a (sigma 1) h i.val).1)
    (fun i => if right then (a (sigma 2) h i.val).2 else (a (sigma 2) h i.val).1)
    (priority_half_product_nonzero F allocation m sigma e a hraw hcoarse right h u hu)
    (statistic h.val) (complement h)
    (AllFieldGroupStatisticComplement.statistic_wordComplement h)
    (halfLaw right (sigma 0) h u) (AllFieldHistoryMasks.childWidth ε h.val)
    (fun _ => hz) (useful_half_window allocation m ε sigma (sigma 0) e _ huseX right h u hu)
  simpa [compatibilityLaw, halfLaw] using hw

theorem transferZ (F : Type*) [Field F] (allocation : Allocation) (m : ℕ) (ε : ℝ)
    (sigma : Placement) (e : Targets (K := K) (tick := tick) allocation m sigma)
    (a : Fin 3 → Raw (K := K) (tick := tick) allocation m sigma)
    (hraw : groupRawSource F allocation m sigma (a 0) (a 1) (a 2) ≠ 0)
    (hcoarse : reorder sigma (ownWord allocation m sigma (a 0),
      ownWord allocation m sigma (a 1), ownWord allocation m sigma (a 2)) =
        AllFieldGroupOrbitData.coarse allocation m sigma e)
    (huseX : groupIdealSide allocation m ε (sigma 0) sigma e (a (sigma 0)))
    (huseY : groupIdealSide allocation m ε (sigma 1) sigma e (a (sigma 1))) :
    Compatible allocation m ε sigma 2 e (a (sigma 2)) := by
  refine ⟨own_coarse_guard allocation m sigma e a hcoarse 2, ?_⟩
  intro right h u hd
  apply JointPopulationCompatibility.shape_count_window_of_typeWindow
    (Counts allocation m sigma) e h u _ _ _
  intro hu
  have hz : halfShape right h u (sigma 0) * halfShape right h u (sigma 1) = 0 := by
    cases right <;> simpa [designated, halfShape, shapeNat] using hd.2
  have hp := priority_half_product_nonzero F allocation m sigma e a hraw hcoarse right h u hu
  by_cases hy : halfShape right h u (sigma 1) = 0
  · have hw := CWStrandCompatibility.zeroY_transfer
      (fun _ : Class (Counts allocation m sigma) e h u => halfShape right h u ∘ sigma)
      (fun i => if right then (a (sigma 0) h i.val).2 else (a (sigma 0) h i.val).1)
      (fun i => if right then (a (sigma 1) h i.val).2 else (a (sigma 1) h i.val).1)
      (fun i => if right then (a (sigma 2) h i.val).2 else (a (sigma 2) h i.val).1)
      hp (statistic h.val) (complement h)
      (AllFieldGroupStatisticComplement.statistic_wordComplement h)
      (halfLaw right (sigma 0) h u) (AllFieldHistoryMasks.childWidth ε h.val)
      (fun _ => hy) (useful_half_window allocation m ε sigma (sigma 0) e _ huseX right h u hu)
    have hy' : (if right then activeParentShape h.val (sigma 1) -
        (shapeSide (sigma 1) u).val else (shapeSide (sigma 1) u).val) = 0 := by
      cases right <;> simpa [halfShape, shapeNat] using hy
    simpa [compatibilityLaw, halfLaw, hy'] using hw
  · have hx : halfShape right h u (sigma 0) = 0 := (Nat.mul_eq_zero.mp hz).resolve_right hy
    have hw := CWStrandCompatibility.zeroX_transfer
      (fun _ : Class (Counts allocation m sigma) e h u => halfShape right h u ∘ sigma)
      (fun i => if right then (a (sigma 0) h i.val).2 else (a (sigma 0) h i.val).1)
      (fun i => if right then (a (sigma 1) h i.val).2 else (a (sigma 1) h i.val).1)
      (fun i => if right then (a (sigma 2) h i.val).2 else (a (sigma 2) h i.val).1)
      hp (statistic h.val) (complement h)
      (AllFieldGroupStatisticComplement.statistic_wordComplement h)
      (halfLaw right (sigma 1) h u) (AllFieldHistoryMasks.childWidth ε h.val)
      (fun _ => hx) (useful_half_window allocation m ε sigma (sigma 1) e _ huseY right h u hu)
    have hy' : (if right then activeParentShape h.val (sigma 1) -
        (shapeSide (sigma 1) u).val else (shapeSide (sigma 1) u).val) ≠ 0 := by
      cases right <;> simpa [halfShape, shapeNat] using hy
    simpa [compatibilityLaw, halfLaw, hy'] using hw

end MatrixMultiplication.AllFieldGroupCompatibilityTransfer

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
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
  obtain ⟨e, he, hc⟩ := hc
  rw [← he]
  exact hc.1

theorem physicalAssignment_coherent (F : Type*) [Field F]
    (allocation : Allocation) (m : ℕ) (ε : ℝ) (sigma : Placement)
    (k : ℕ) (U : Finset (ZMod (37 ^ k)))
    (sample : Sample (Pos (K := K) (tick := tick) allocation m sigma) k) :
    JointExtraction.Coherent (groupPreparedSource F allocation m ε sigma)
      (physicalAssignment allocation m ε sigma k U sample) := by
  intro x y z tx ty tz hT htx hty htz
  let a : Fin 3 → Raw (K := K) (tick := tick) allocation m sigma := (Matrix.vecCons (x) (Matrix.vecCons (y) (Matrix.vecCons (z) Matrix.vecEmpty)))
  let physicalTag : Fin 3 → Triple (Pos (K := K) (tick := tick) allocation m sigma) :=
    (Matrix.vecCons (tx) (Matrix.vecCons (ty) (Matrix.vecCons (tz) Matrix.vecEmpty)))
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
end

end MatrixAllFields

end OAI
