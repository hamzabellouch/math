import OAI.LinearAlgebra.MatrixMultiplication.FieldGroups.OrbitData
import OAI.LinearAlgebra.MatrixMultiplication.FieldHistory.GroupedRecovery
import OAI.LinearAlgebra.MatrixMultiplication.JointExtraction.OrbitFibers

namespace OAI

/-! Group assignments, orbit counts and extraction capacities. -/

noncomputable section

namespace MatrixMultiplication.AllFieldGroupOrbitData

open AllFieldHistory AllFieldHistoryGroupMasks AllFieldHistoryGroupedRecovery
open AllFieldGroupOrbitCount JointCoarseHashing PermutationMatching
attribute [local instance] Classical.propDecidable Classical.decEq

variable {K tick : ℕ}

local instance canonicalGroupAction (allocation : Allocation) (m : ℕ) (sigma : Placement) :
    MulAction
      (HalfClassPermutations (GroupPositions (K := K) (tick := tick) (sigma := sigma) allocation m))
      (JointCanonicalization.CanonicalPairs (groupCounts (K := K) (tick := tick) allocation m sigma)
        (fun h => Fin (activeHalfLength h.val) → Fin 7)
        (fun h => Fin (activeHalfLength h.val) → Fin 7)) :=
  completeWordPairMulAction

local instance canonicalGroupFintype (allocation : Allocation) (m : ℕ) (sigma : Placement) :
    Fintype
      (JointCanonicalization.CanonicalPairs (groupCounts (K := K) (tick := tick) allocation m sigma)
        (fun h => Fin (activeHalfLength h.val) → Fin 7)
        (fun h => Fin (activeHalfLength h.val) → Fin 7)) := by
  letI : ∀ c : GroupClasses K tick sigma,
      Fintype (GroupPositions allocation m c) := fun _ => Fin.fintype _
  letI : ∀ c : GroupClasses K tick sigma,
      DecidableEq (GroupPositions allocation m c) := fun _ => Classical.decEq _
  letI : ∀ c : GroupClasses K tick sigma,
      Fintype (GroupLetters c) := fun _ => Pi.instFintype
  exact HistorySymmetry.completeWordPairFintype

def tag (allocation : Allocation) (m : ℕ) (sigma : Placement) (side : Fin 3) :
    Raw (K := K) (tick := tick) allocation m sigma ↪ Variable (K := K) (tick := tick) allocation m sigma where
  toFun w := (side, w)
  inj' := by intro w v h; exact congrArg Prod.snd h

theorem full_eq_tagged_fiber (allocation : Allocation) (m : ℕ) (sigma : Placement)
    (e : Targets (K := K) (tick := tick) allocation m sigma) (o : Orbit (K := K) (tick := tick) allocation m sigma) :
    full allocation m sigma e o =
      (JointOrbitFibers.transportedFiber (groupCoordinates allocation m sigma e) o.2).map
        (tag allocation m sigma o.1) := by
  ext v
  constructor
  · intro hv
    have hh := (Finset.mem_filter.mp hv).2
    apply Finset.mem_map.mpr
    refine ⟨v.2, ?_, ?_⟩
    · exact (JointOrbitFibers.mem_transportedFiber (groupCoordinates allocation m sigma e)).mpr hh.2
    · exact Prod.ext hh.1.symm rfl
  · intro hv
    obtain ⟨w, hw, rfl⟩ := Finset.mem_map.mp hv
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl,
      (JointOrbitFibers.mem_transportedFiber (groupCoordinates allocation m sigma e)).mp hw⟩

theorem full_eq_tagged_localOrbit (allocation : Allocation) (m : ℕ) (sigma : Placement)
    (e : Targets (K := K) (tick := tick) allocation m sigma)
    (side : Fin 3) (w : Raw (K := K) (tick := tick) allocation m sigma) :
    full allocation m sigma e (side, orbitOf allocation m sigma e w) =
      (localOrbit allocation m sigma e w).map (tag allocation m sigma side) := by
  rw [full_eq_tagged_fiber]
  dsimp only [orbitOf]
  erw [JointOrbitFibers.transportedFiber_mk]
  apply congrArg (fun t : Finset (Raw (K := K) (tick := tick) allocation m sigma) =>
    t.map (tag allocation m sigma side))
  ext v
  simp only [localOrbit, GroupOrbitProjection.rawOrbit, GroupOrbitProjection.transportedOrbit,
    OrbitCounting.orbitSet,
    Finset.mem_image, Finset.mem_univ, true_and]
  rfl

@[simp] theorem full_card_localOrbit (allocation : Allocation) (m : ℕ) (sigma : Placement)
    (e : Targets (K := K) (tick := tick) allocation m sigma)
    (side : Fin 3) (w : Raw (K := K) (tick := tick) allocation m sigma) :
    (full allocation m sigma e (side, orbitOf allocation m sigma e w)).card =
      (localOrbit allocation m sigma e w).card := by
  rw [full_eq_tagged_localOrbit, Finset.card_map]

theorem full_filter_card_localOrbit (allocation : Allocation) (m : ℕ) (sigma : Placement)
    (e : Targets (K := K) (tick := tick) allocation m sigma)
    (side : Fin 3) (w : Raw (K := K) (tick := tick) allocation m sigma) (bad : Variable (K := K) (tick := tick) allocation m sigma → Prop) :
    ((full allocation m sigma e (side, orbitOf allocation m sigma e w)).filter bad).card =
      ((localOrbit allocation m sigma e w).filter (fun v => bad (side, v))).card := by
  rw [full_eq_tagged_localOrbit, Finset.filter_map]
  exact Finset.card_map _

end MatrixMultiplication.AllFieldGroupOrbitData

end

end OAI
