import OAI.LinearAlgebra.MatrixMultiplication.FieldGroups.OrbitData
import OAI.LinearAlgebra.MatrixMultiplication.JointExtraction.PopulationCWNonzero
import OAI.LinearAlgebra.MatrixMultiplication.CoppersmithWinograd.CWShapePhysicalPermutation
import OAI.LinearAlgebra.MatrixMultiplication.FieldGroups.StatisticComplement

namespace OAI

/-! Group assignments, orbit counts and extraction capacities. -/

noncomputable section

namespace MatrixMultiplication.AllFieldGroupCompatibilityTransfer

open MatrixMultiplication.Foundation AllFieldHistory AllFieldHistoryChildLaws
open AllFieldHistoryGroupMasks AllFieldHistoryGroupedRecovery AllFieldGroupOrbitData
open JointPopulation JointCanonicalization JointCanonicalCW CWStrands InheritedMasks
open scoped BigOperators

attribute [local instance] Classical.propDecidable

variable {K tick : ℕ} {sigma : Placement}

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

def halfShape (right : Bool) (h : ActiveOrder K tick sigma)
    (u : JointPopulation.Shape) : Fin 3 → ℕ :=
  if right then activeParentShape h.val - shapeNat u else shapeNat u

def halfLaw (right : Bool) (side : Fin 3) (h : ActiveOrder K tick sigma)
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

end OAI
