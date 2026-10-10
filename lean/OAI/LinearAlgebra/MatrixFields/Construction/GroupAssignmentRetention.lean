import Mathlib
import OAI.LinearAlgebra.MatrixFields.Entropy.GroupBranchLaws
import OAI.LinearAlgebra.MatrixFields.Extraction.JointMaskedGoodSelection
import OAI.LinearAlgebra.MatrixFields.Histories.JointScalarOrbitAdmissibility

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.AllFieldGroupAdmissible

open AllFieldHistory AllFieldHistorySupport AllFieldHistoryChildLaws
open AllFieldHistoryGroupMasks AllFieldHistoryGroupedRecovery AllFieldGroupOrbitData
open JointPopulation JointCanonicalization PermutationMatching
attribute [local instance] Classical.propDecidable Classical.decEq

variable {K tick : ℕ}

abbrev Symmetries (allocation : Allocation) (m : ℕ) (sigma : Placement) :=
  HalfClassPermutations (ClassPositions (Counts (K := K) (tick := tick) allocation m sigma))

@[instance_reducible]
def rawAction (allocation : Allocation) (m : ℕ) (sigma : Placement)
    (e : Targets (K := K) (tick := tick) allocation m sigma) :
    MulAction (Symmetries (K := K) (tick := tick) allocation m sigma) (Raw (K := K) (tick := tick) allocation m sigma) :=
  EquivOrbitTransport.action (groupCoordinates (K := K) (tick := tick) allocation m sigma e)

theorem admissible_smul (allocation : Allocation) (m : ℕ) (ε : ℝ) (sigma : Placement)
    (side : Fin 3) (e : Targets (K := K) (tick := tick) allocation m sigma) :
    letI : MulAction (Symmetries (K := K) (tick := tick) allocation m sigma) (Raw (K := K) (tick := tick) allocation m sigma) :=
      rawAction (K := K) (tick := tick) allocation m sigma e
    ∀ (g : Symmetries (K := K) (tick := tick) allocation m sigma) (w : Raw (K := K) (tick := tick) allocation m sigma),
      Admissible (K := K) (tick := tick) allocation m ε sigma side e w →
      Admissible (K := K) (tick := tick) allocation m ε sigma side e ((rawAction (K := K) (tick := tick) allocation m sigma e).smul g w) := by
  let : MulAction (Symmetries (K := K) (tick := tick) allocation m sigma) (Raw (K := K) (tick := tick) allocation m sigma) :=
    rawAction (K := K) (tick := tick) allocation m sigma e
  intro g w hw
  have hweights : ∀ h j,
      CWStrands.weight (((rawAction (K := K) (tick := tick) allocation m sigma e).smul g w) h j).1 = (shapeSide (sigma side) ((e h).val j)).val ∧
      CWStrands.weight (((rawAction (K := K) (tick := tick) allocation m sigma e).smul g w) h j).2 = activeParentShape h.val (sigma side) -
        (shapeSide (sigma side) ((e h).val j)).val := by
    exact JointScalarOrbitAdmissibility.classWeights_smul
      (Counts (K := K) (tick := tick) allocation m sigma)
      (fun h => Fin (activeHalfLength h.val) → Fin 7)
      (fun h => Fin (activeHalfLength h.val) → Fin 7)
      (fun _ => CWStrands.weight) (fun _ => CWStrands.weight)
      (fun _ u => (shapeSide (sigma side) u).val)
      (fun h u => activeParentShape h.val (sigma side) - (shapeSide (sigma side) u).val)
      e g w hw.2
  refine ⟨⟨?_, ?_⟩, hweights⟩
  · intro h j
    apply Fin.ext
    exact (hweights h j).1
  · exact (JointScalarOrbitAdmissibility.rawWindows_smul
      (SL := fun h : ActiveOrder K tick sigma => Statistic h.val)
      (SR := fun h : ActiveOrder K tick sigma => Statistic h.val)
      (Counts (K := K) (tick := tick) allocation m sigma)
      (fun h => Fin (activeHalfLength h.val) → Fin 7)
      (fun h => Fin (activeHalfLength h.val) → Fin 7)
      (fun c => statistic c.1.val) (fun c => statistic c.1.val)
      (fun c => leftLaw c.1.val c.2 (sigma side))
      (fun c => rightLaw c.1.val c.2 (sigma side))
      (fun c => AllFieldHistoryMasks.childWidth ε c.1.val)
      (fun c => AllFieldHistoryMasks.childWidth ε c.1.val) e g w).mpr hw.1.2

theorem admissible_of_orbitOf_eq (allocation : Allocation) (m : ℕ) (ε : ℝ)
    (sigma : Placement) (side : Fin 3)
    (e : Targets (K := K) (tick := tick) allocation m sigma)
    (w v : Raw (K := K) (tick := tick) allocation m sigma) (hw : Admissible (K := K) (tick := tick) allocation m ε sigma side e w)
    (hv : orbitOf (K := K) (tick := tick) allocation m sigma e v = orbitOf (K := K) (tick := tick) allocation m sigma e w) :
    Admissible (K := K) (tick := tick) allocation m ε sigma side e v := by
  let : MulAction (Symmetries (K := K) (tick := tick) allocation m sigma) (Raw (K := K) (tick := tick) allocation m sigma) :=
    rawAction (K := K) (tick := tick) allocation m sigma e
  have hrel : MulAction.orbitRel
      (Symmetries (K := K) (tick := tick) allocation m sigma)
      (CanonicalPairs (Counts (K := K) (tick := tick) allocation m sigma)
        (fun h => Fin (activeHalfLength h.val) → Fin 7)
        (fun h => Fin (activeHalfLength h.val) → Fin 7))
      (groupCoordinates (K := K) (tick := tick) allocation m sigma e v)
      (groupCoordinates (K := K) (tick := tick) allocation m sigma e w) := Quotient.exact hv
  obtain ⟨g, hg⟩ := hrel
  have hgv : ((rawAction (K := K) (tick := tick) allocation m sigma e).smul g w) = v := by
    apply (groupCoordinates (K := K) (tick := tick) allocation m sigma e).injective
    exact (EquivOrbitTransport.equiv_smul
      (groupCoordinates (K := K) (tick := tick) allocation m sigma e) g w).trans hg
  rw [← hgv]
  exact admissible_smul allocation m ε sigma side e g w hw

theorem full_admissible (allocation : Allocation) (m : ℕ) (ε : ℝ) (sigma : Placement)
    (e : Targets (K := K) (tick := tick) allocation m sigma)
    (o : Orbit (K := K) (tick := tick) allocation m sigma) (ho : o ∈ (data (K := K) (tick := tick) allocation m ε sigma).orbits e)
    (v : Variable (K := K) (tick := tick) allocation m sigma) (hv : v ∈ (data (K := K) (tick := tick) allocation m ε sigma).full e o) :
    Admissible (K := K) (tick := tick) allocation m ε sigma v.1 e v.2 := by
  obtain ⟨w, hw, hwo⟩ := (Finset.mem_filter.mp ho).2
  obtain ⟨hside, hvo⟩ := (Finset.mem_filter.mp hv).2
  rw [hside]
  exact admissible_of_orbitOf_eq allocation m ε sigma o.1 e w v.2 hw (hvo.trans hwo.symm)

end MatrixMultiplication.AllFieldGroupAdmissible

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.AllFieldGroupAdmissible

open AllFieldHistory AllFieldHistorySupport AllFieldHistoryChildLaws
open AllFieldHistoryGroupMasks AllFieldHistoryGroupedRecovery AllFieldGroupOrbitData
open JointPopulation JointCanonicalization PermutationMatching
attribute [local instance] Classical.propDecidable Classical.decEq

variable {K tick : ℕ}

theorem used_project_admissible (F : Type*) [CommRing F]
    (allocation : Allocation) (m : ℕ) (ε : ℝ) (sigma : Placement)
    (e : AllFieldHistoryRecovery.Targets (K := K) (tick := tick) allocation m)
    (side : Fin 3) (w : AllFieldHistoryRecovery.Raw (K := K) (tick := tick) allocation m)
    (hw : AllFieldHistoryRecovery.Used F allocation m ε e (sigma side) w) :
    Admissible (K := K) (tick := tick) allocation m ε sigma side
      (projectTarget (K := K) (tick := tick) allocation m sigma e) (projectRaw (K := K) (tick := tick) allocation m sigma w) := by
  obtain ⟨x, y, z, hq, rfl⟩ := hw
  have hi :
      AllFieldHistoryRecovery.idealSide allocation m ε 0 e x ∧
      AllFieldHistoryRecovery.idealSide allocation m ε 1 e y ∧
      AllFieldHistoryRecovery.idealSide allocation m ε 2 e z := by
    by_contra hn
    apply hq
    rw [AllFieldHistoryRecovery.ideal_eq_delete_source F allocation m ε e]
    exact ite_eq_right hn
  have ht := AllFieldHistoryRecovery.ideal_support_weights F allocation m ε e x y z hq
  have hs (s : Fin 3) :
      AllFieldHistoryRecovery.idealSide allocation m ε s e
          (AllFieldHistoryRecovery.sideVariable s x y z) ∧
        AllFieldHistoryRecovery.sideWeights allocation m s e
          (AllFieldHistoryRecovery.sideVariable s x y z) := by
    fin_cases s
    · exact ⟨hi.1, ht.1⟩
    · exact ⟨hi.2.1, ht.2.1⟩
    · exact ⟨hi.2.2, ht.2.2⟩
  refine ⟨?_, ?_⟩
  · exact (idealSide_iff_all_groups allocation m ε
      (sigma side) e _).mp (hs (sigma side)).1 sigma
  · intro h j
    exact (hs (sigma side)).2 h.val j

theorem used_project_covered (F : Type*) [CommRing F]
    (allocation : Allocation) (m : ℕ) (ε : ℝ) (sigma : Placement)
    (e : AllFieldHistoryRecovery.Targets (K := K) (tick := tick) allocation m)
    (side : Fin 3) (w : AllFieldHistoryRecovery.Raw (K := K) (tick := tick) allocation m)
    (hw : AllFieldHistoryRecovery.Used F allocation m ε e (sigma side) w) :
    ∃ o ∈ (data (K := K) (tick := tick) allocation m ε sigma).orbits (projectTarget (K := K) (tick := tick) allocation m sigma e),
      (side, projectRaw (K := K) (tick := tick) allocation m sigma w) ∈
        (data (K := K) (tick := tick) allocation m ε sigma).full (projectTarget (K := K) (tick := tick) allocation m sigma e) o :=
  admissible_covered allocation m ε sigma side _ _
    (used_project_admissible F allocation m ε sigma e side w hw)

end MatrixMultiplication.AllFieldGroupAdmissible

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
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
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.AllFieldGroupCompatibility

open AllFieldHistory AllFieldHistoryChildLaws AllFieldHistoryGroupMasks
open AllFieldHistoryGroupedRecovery AllFieldGroupOrbitData
open JointPopulation JointCanonicalization

attribute [local instance] Classical.propDecidable

variable {K tick : ℕ}

theorem groupIdealSide_ownWord (allocation : Allocation) (m : ℕ) (ε : ℝ)
    (sigma : Placement) (side : Fin 3)
    (e : Targets (K := K) (tick := tick) allocation m sigma)
    (w : Raw (K := K) (tick := tick) allocation m sigma)
    (hw : groupIdealSide allocation m ε (sigma side) sigma e w) :
    tripleSide side (AllFieldGroupOrbitData.coarse allocation m sigma e) =
      ownWord allocation m sigma w := by
  change tripleSide side
    (reorder sigma (triple (Counts (K := K) (tick := tick) allocation m sigma) e)) = _
  rw [tripleSide_reorder]
  funext p
  have hs : tripleSide (sigma side)
      (triple (Counts (K := K) (tick := tick) allocation m sigma) e) p =
      shapeSide (sigma side) ((e p.1).val p.2) := by
    generalize sigma side = s
    fin_cases s <;> rfl
  rw [hs]
  exact (hw.1 p.1 p.2).symm

theorem groupIdealSide_fineCompatible (allocation : Allocation) (m : ℕ) (ε : ℝ)
    (sigma : Placement) (side : Fin 3)
    (e : Targets (K := K) (tick := tick) allocation m sigma)
    (w : Raw (K := K) (tick := tick) allocation m sigma)
    (hw : groupIdealSide allocation m ε (sigma side) sigma e w) :
    fineCompatible allocation m ε sigma side e w := by
  intro right h u hd
  apply JointPopulationCompatibility.shape_count_window_of_typeWindow
    (Counts (K := K) (tick := tick) allocation m sigma) e h u
    (fun i => statistic h.val (if right then (w h i).2 else (w h i).1))
    (compatibilityLaw right side sigma h u) (AllFieldHistoryMasks.childWidth ε h.val)
  intro hu
  rw [AllFieldGroupNativeLaws.compatibilityLaw_eq allocation m sigma right side h u hu hd]
  cases right
  · exact (hw.2 h u hu).1
  · exact (hw.2 h u hu).2

theorem groupIdealSide_compatible (allocation : Allocation) (m : ℕ) (ε : ℝ)
    (sigma : Placement) (side : Fin 3)
    (e : Targets (K := K) (tick := tick) allocation m sigma)
    (w : Raw (K := K) (tick := tick) allocation m sigma)
    (hw : groupIdealSide allocation m ε (sigma side) sigma e w) :
    Compatible allocation m ε sigma side e w :=
  ⟨groupIdealSide_ownWord allocation m ε sigma side e w hw,
    groupIdealSide_fineCompatible allocation m ε sigma side e w hw⟩

theorem admissible_compatible (allocation : Allocation) (m : ℕ) (ε : ℝ)
    (sigma : Placement) (side : Fin 3)
    (e : Targets (K := K) (tick := tick) allocation m sigma)
    (w : Raw (K := K) (tick := tick) allocation m sigma)
    (hw : Admissible allocation m ε sigma side e w) :
    Compatible allocation m ε sigma side e w :=
  groupIdealSide_compatible allocation m ε sigma side e w hw.1

end MatrixMultiplication.AllFieldGroupCompatibility

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
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
    (fun v hv f hf hn hcomp => competitor_coverage (K := K) (tick := tick) allocation m ε sigma e o v (hc v hv) f hn hcomp)

  rw [Finset.filter_congr_decidable] at hh
  exact hh

end MatrixMultiplication.AllFieldGroupAssignmentRetention

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.AllFieldGroupAssignmentRetention

open AllFieldHistory AllFieldHistoryGroupMasks AllFieldHistoryGroupedRecovery
open AllFieldGroupOrbitData JointCoarseHashing
attribute [local instance] Classical.propDecidable Classical.decEq

variable {K tick : ℕ}

theorem good_local_failure_le (allocation : Allocation) (m : ℕ) (ε : ℝ)
    (sigma : Placement) (k : ℕ) (U : Finset (ZMod (37 ^ k)))
    (hAP : ∀ x ∈ U, ∀ y ∈ U, ∀ z ∈ U, x + y = 2 * z → x = z ∧ y = z)
    (N : ℝ) (s : Sample (Pos (K := K) (tick := tick) allocation m sigma) k)
    (e : Targets (K := K) (tick := tick) allocation m sigma) (hg : (data allocation m ε sigma).Good k U N e s)
    (side : Fin 3) (w : Raw (K := K) (tick := tick) allocation m sigma)
    (hw : Admissible allocation m ε sigma side e w) :
    (((localOrbit allocation m sigma e w).filter (fun v =>
      completeKeep allocation m ε (sigma side) sigma v ∧
        assigned allocation m ε sigma k U s (side, v) ≠ some (coarse allocation m sigma e))).card : ℝ) /
      ((localOrbit allocation m sigma e w).card : ℝ) ≤ 1 / N := by
  have ho : (side, orbitOf allocation m sigma e w) ∈ (data allocation m ε sigma).orbits e :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, w, hw, rfl⟩
  have hh := good_failure_fraction_le allocation m ε sigma k U hAP N s e hg _ ho
  change (((passing allocation m sigma ε e (side, orbitOf allocation m sigma e w)).filter
      (fun v => assigned allocation m ε sigma k U s v ≠ some (coarse allocation m sigma e))).card : ℝ) /
    ((full allocation m sigma e (side, orbitOf allocation m sigma e w)).card : ℝ) ≤ 1 / N at hh
  rw [passing, Finset.filter_filter] at hh
  simp only [full_eq_tagged_localOrbit, Finset.filter_map, Finset.card_map] at hh
  rw [Finset.filter_congr_decidable] at hh
  exact hh

theorem localAssigned_iff (allocation : Allocation) (m : ℕ) (ε : ℝ)
    (sigma : Placement) (k : ℕ) (U : Finset (ZMod (37 ^ k)))
    (s : Sample (Pos (K := K) (tick := tick) allocation m sigma) k)
    (t : Triple (Pos (K := K) (tick := tick) allocation m sigma)) (side : Fin 3) (w : Raw (K := K) (tick := tick) allocation m sigma) :
    localAssigned allocation m sigma (physicalAssignment allocation m ε sigma k U s) t side w ↔
      assigned allocation m ε sigma k U s (sigma.symm side, w) = some t := by
  fin_cases side <;> rfl

theorem good_physical_local_failure_le (allocation : Allocation) (m : ℕ) (ε : ℝ)
    (sigma : Placement) (k : ℕ) (U : Finset (ZMod (37 ^ k)))
    (hAP : ∀ x ∈ U, ∀ y ∈ U, ∀ z ∈ U, x + y = 2 * z → x = z ∧ y = z)
    (N : ℝ) (s : Sample (Pos (K := K) (tick := tick) allocation m sigma) k)
    (e : Targets (K := K) (tick := tick) allocation m sigma) (hg : (data allocation m ε sigma).Good k U N e s)
    (side : Fin 3) (w : Raw (K := K) (tick := tick) allocation m sigma)
    (hw : Admissible allocation m ε sigma (sigma.symm side) e w) :
    (((localOrbit allocation m sigma e w).filter (fun v =>
      completeKeep allocation m ε side sigma v ∧
        ¬localAssigned allocation m sigma (physicalAssignment allocation m ε sigma k U s)
          (coarse allocation m sigma e) side v)).card : ℝ) /
      ((localOrbit allocation m sigma e w).card : ℝ) ≤ 1 / N := by
  simpa only [sigma.apply_symm_apply, localAssigned_iff] using
    good_local_failure_le allocation m ε sigma k U hAP N s e hg (sigma.symm side) w hw

theorem good_projected_failure_le (F : Type*) [CommRing F]
    (allocation : Allocation) (m : ℕ) (ε : ℝ) (sigma : Placement)
    (k : ℕ) (U : Finset (ZMod (37 ^ k)))
    (hAP : ∀ x ∈ U, ∀ y ∈ U, ∀ z ∈ U, x + y = 2 * z → x = z ∧ y = z)
    (N : ℝ) (s : Sample (Pos (K := K) (tick := tick) allocation m sigma) k)
    (e : AllFieldHistoryRecovery.Targets (K := K) (tick := tick) allocation m)
    (hg : (data allocation m ε sigma).Good k U N (projectTarget allocation m sigma e) s)
    (side : Fin 3) (w : AllFieldHistoryRecovery.Raw (K := K) (tick := tick) allocation m)
    (hw : AllFieldHistoryRecovery.Used F allocation m ε e side w) :
    (((localOrbit allocation m sigma (projectTarget allocation m sigma e)
      (projectRaw allocation m sigma w)).filter (fun v =>
        completeKeep allocation m ε side sigma v ∧
          ¬localAssigned allocation m sigma (physicalAssignment allocation m ε sigma k U s)
            (coarse allocation m sigma (projectTarget allocation m sigma e)) side v)).card : ℝ) /
      ((localOrbit allocation m sigma (projectTarget allocation m sigma e)
        (projectRaw allocation m sigma w)).card : ℝ) ≤ 1 / N := by
  apply good_physical_local_failure_le allocation m ε sigma k U hAP N s _ hg
  exact AllFieldGroupAdmissible.used_project_admissible F allocation m ε sigma e
    (sigma.symm side) w (by simpa only [sigma.apply_symm_apply] using hw)

end MatrixMultiplication.AllFieldGroupAssignmentRetention

end
end

end MatrixAllFields

end OAI
