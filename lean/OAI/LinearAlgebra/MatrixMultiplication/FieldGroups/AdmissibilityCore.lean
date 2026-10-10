import OAI.LinearAlgebra.MatrixMultiplication.FieldGroups.OrbitData
import OAI.LinearAlgebra.MatrixMultiplication.JointExtraction.ScalarOrbitAdmissibility

namespace OAI

/-! Group assignments, orbit counts and extraction capacities. -/

noncomputable section

namespace MatrixMultiplication.AllFieldGroupAdmissible

open AllFieldHistory AllFieldHistorySupport AllFieldHistoryChildLaws
open AllFieldHistoryGroupMasks AllFieldHistoryGroupedRecovery AllFieldGroupOrbitData
open JointPopulation JointCanonicalization PermutationMatching
attribute [local instance] Classical.propDecidable Classical.decEq

variable {K tick : ℕ}

abbrev Symmetries (allocation : Allocation) (m : ℕ) (sigma : Placement) :=
  HalfClassPermutations (ClassPositions (Counts (K := K) (tick := tick) allocation m sigma))

@[instance_reducible] def rawAction (allocation : Allocation) (m : ℕ) (sigma : Placement)
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
  let _ : MulAction (Symmetries (K := K) (tick := tick) allocation m sigma) (Raw (K := K) (tick := tick) allocation m sigma) :=
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
  let _ : MulAction (Symmetries (K := K) (tick := tick) allocation m sigma) (Raw (K := K) (tick := tick) allocation m sigma) :=
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

end OAI
