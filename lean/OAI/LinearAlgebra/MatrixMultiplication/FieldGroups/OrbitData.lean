import OAI.LinearAlgebra.MatrixMultiplication.FieldHistory.GroupCore
import OAI.LinearAlgebra.MatrixMultiplication.FieldGroups.OrbitCount
import OAI.LinearAlgebra.MatrixMultiplication.JointExtraction.MaskedAssignment
import OAI.LinearAlgebra.MatrixMultiplication.JointExtraction.CoarseReorder
import OAI.LinearAlgebra.MatrixMultiplication.JointExtraction.PopulationMixedCompatibility

namespace OAI

/-! Group assignments, orbit counts and extraction capacities. -/

noncomputable section

namespace MatrixMultiplication.AllFieldGroupOrbitData

open AllFieldHistory AllFieldHistorySupport AllFieldHistoryChildLaws
open AllFieldHistoryGroupMasks AllFieldHistoryGroupedRecovery
open AllFieldGroupOrbitCount JointPopulation JointCanonicalization
open JointCoarseHashing PermutationMatching
open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {K tick : ℕ}

abbrev Counts (allocation : Allocation) (m : ℕ) (sigma : Placement) :=
  groupCounts (K := K) (tick := tick) allocation m sigma
abbrev Targets (allocation : Allocation) (m : ℕ) (sigma : Placement) :=
  Target (Counts (K := K) (tick := tick) allocation m sigma)
abbrev Pos (allocation : Allocation) (m : ℕ) (sigma : Placement) :=
  Position (Counts (K := K) (tick := tick) allocation m sigma)
abbrev Raw (allocation : Allocation) (m : ℕ) (sigma : Placement) :=
  GroupRaw (K := K) (tick := tick) allocation m sigma
abbrev Orbit (allocation : Allocation) (m : ℕ) (sigma : Placement) :=
  Fin 3 × GroupOrbit (K := K) (tick := tick) allocation m sigma
abbrev Variable (allocation : Allocation) (m : ℕ) (sigma : Placement) :=
  Fin 3 × Raw (K := K) (tick := tick) allocation m sigma

def tripleSide {P : Type*} (s : Fin 3) (t : Triple P) : Word P :=
  ![t.1, t.2.1, t.2.2] s

def reorder {P : Type*} (sigma : Placement) (t : Triple P) : Triple P :=
  (tripleSide (sigma 0) t, tripleSide (sigma 1) t, tripleSide (sigma 2) t)

@[simp] theorem tripleSide_reorder {P : Type*} (sigma : Placement)
    (t : Triple P) (s : Fin 3) :
    tripleSide s (reorder sigma t) = tripleSide (sigma s) t :=
  JointCoarseReorder.tripleSide_reorder sigma t s

theorem reorder_injective {P : Type*} (sigma : Placement) :
    Function.Injective (reorder (P := P) sigma) :=
  JointCoarseReorder.reorder_injective sigma

theorem reorder_support {P : Type*} (sigma : Placement) (S : P → ℕ)
    (t : Triple P) (ht : HasSupportSum S t) : HasSupportSum S (reorder sigma t) :=
  JointCoarseReorder.reorder_support sigma S t ht

def coarse (allocation : Allocation) (m : ℕ) (sigma : Placement)
    (e : Targets (K := K) (tick := tick) allocation m sigma) : Triple (Pos (K := K) (tick := tick) allocation m sigma) :=
  reorder sigma (triple (Counts (K := K) (tick := tick) allocation m sigma) e)

def ambient (allocation : Allocation) (m : ℕ) (sigma : Placement) :
    Finset (Triple (Pos (K := K) (tick := tick) allocation m sigma)) :=
  (ambientSet (Counts (K := K) (tick := tick) allocation m sigma) (fun h => 2 * activeHalfLength h.val)).image
    (reorder sigma)

def support (allocation : Allocation) (m : ℕ) (sigma : Placement)
    (p : Pos (K := K) (tick := tick) allocation m sigma) : ℕ :=
  2 * activeHalfLength p.1.val

theorem counts_support (allocation : Allocation) (m : ℕ) (sigma : Placement)
    (h : ActiveOrder K tick sigma) (u : JointPopulation.Shape)
    (hu : 0 < Counts (K := K) (tick := tick) allocation m sigma h u) :
    u.1.val + u.2.1.val + u.2.2.val = 2 * activeHalfLength h.val :=
  jointCounts_support_sum allocation m h.val.val u hu

theorem coarse_injective (allocation : Allocation) (m : ℕ) (sigma : Placement) :
    Function.Injective (coarse (K := K) (tick := tick) allocation m sigma) :=
  (reorder_injective sigma).comp (triple_injective (Counts (K := K) (tick := tick) allocation m sigma))

theorem ambient_support (allocation : Allocation) (m : ℕ) (sigma : Placement)
    (f : Triple (Pos (K := K) (tick := tick) allocation m sigma))
    (hf : f ∈ ambient allocation m sigma) : HasSupportSum (support allocation m sigma) f := by
  obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hf
  exact reorder_support sigma _ t (Finset.mem_filter.mp ht).2.1

theorem coarse_mem_ambient (allocation : Allocation) (m : ℕ) (sigma : Placement)
    (e : Targets (K := K) (tick := tick) allocation m sigma) :
    coarse allocation m sigma e ∈ ambient allocation m sigma := by
  apply Finset.mem_image.mpr
  refine ⟨triple (Counts (K := K) (tick := tick) allocation m sigma) e, ?_, rfl⟩
  apply targetSet_subset_ambient (Counts (K := K) (tick := tick) allocation m sigma)
    (fun h => 2 * activeHalfLength h.val) (counts_support allocation m sigma)
  simp only [targetSet, Finset.mem_image, Finset.mem_univ, true_and]
  exact ⟨e, rfl⟩

def sharing {sigma : Placement} (h : ActiveOrder K tick sigma) : Bool :=
  match h.val.val.1 with
  | .stageA _ => true
  | .stageB _ => true
  | .stageC _ => false

def workComplement (w : Work K) : w.Statistic ≃ w.Statistic :=
  match w with
  | .stageA _ => CWCompleteStatistics.orderedComplementStatistic
  | .stageB _ => CWCompleteStatistics.complementStatistic
  | .stageC _ => Equiv.refl _

def complement {sigma : Placement} (h : ActiveOrder K tick sigma) : Statistic h.val ≃ Statistic h.val :=
  workComplement h.val.val.1

def compatibilityLaw (right : Bool) (side : Fin 3) (sigma : Placement)
    (h : ActiveOrder K tick sigma) (u : JointPopulation.Shape) : Statistic h.val → ℝ :=
  let weight : Fin 3 → ℕ := fun i =>
    if right then activeParentShape h.val (sigma i) - (shapeSide (sigma i) u).val
    else (shapeSide (sigma i) u).val
  let source : Fin 3 := if side = 2 ∧ weight 1 ≠ 0 then sigma 1 else sigma 0
  (if right then rightLaw h.val u source else leftLaw h.val u source) ∘
    (complement h).symm

def designated (right : Bool) (side : Fin 3) (sigma : Placement)
    (h : ActiveOrder K tick sigma) (u : JointPopulation.Shape) : Prop :=
  sharing h = true ∧
    let weight : Fin 3 → ℕ := fun i =>
      if right then activeParentShape h.val (sigma i) - (shapeSide (sigma i) u).val
      else (shapeSide (sigma i) u).val
    if side = 1 then weight 2 = 0
    else if side = 2 then weight 0 * weight 1 = 0 else False

def fineCompatible (allocation : Allocation) (m : ℕ) (ε : ℝ) (sigma : Placement)
    (side : Fin 3) (e : Targets (K := K) (tick := tick) allocation m sigma)
    (w : Raw (K := K) (tick := tick) allocation m sigma) : Prop :=
  ∀ (right : Bool) h u, designated right side sigma h u → ∀ a : Statistic h.val,
    |(JointPopulationCompatibility.shapeStatisticCount (Counts (K := K) (tick := tick) allocation m sigma) e h u
        (fun i => statistic h.val (if right then (w h i).2 else (w h i).1)) a : ℝ) -
      (Counts (K := K) (tick := tick) allocation m sigma h u : ℝ) * compatibilityLaw right side sigma h u a| ≤
        (Counts (K := K) (tick := tick) allocation m sigma h u : ℝ) * AllFieldHistoryMasks.childWidth ε h.val

def ownWord (allocation : Allocation) (m : ℕ) (sigma : Placement)
    (w : Raw (K := K) (tick := tick) allocation m sigma) : Word (Pos (K := K) (tick := tick) allocation m sigma) :=
  fun p => groupCoarse 0 p.1 (w p.1 p.2)

def Compatible (allocation : Allocation) (m : ℕ) (ε : ℝ) (sigma : Placement)
    (side : Fin 3) (e : Targets (K := K) (tick := tick) allocation m sigma)
    (w : Raw (K := K) (tick := tick) allocation m sigma) : Prop :=
  tripleSide side (coarse allocation m sigma e) = ownWord allocation m sigma w ∧
    fineCompatible allocation m ε sigma side e w

def Admissible (allocation : Allocation) (m : ℕ) (ε : ℝ) (sigma : Placement)
    (side : Fin 3) (e : Targets (K := K) (tick := tick) allocation m sigma)
    (w : Raw (K := K) (tick := tick) allocation m sigma) : Prop :=
  groupIdealSide allocation m ε (sigma side) sigma e w ∧
    ∀ h j, CWStrands.weight (w h j).1 = (shapeSide (sigma side) ((e h).val j)).val ∧
      CWStrands.weight (w h j).2 = activeParentShape h.val (sigma side) -
        (shapeSide (sigma side) ((e h).val j)).val

def orbitOf (allocation : Allocation) (m : ℕ) (sigma : Placement)
    (e : Targets (K := K) (tick := tick) allocation m sigma)
    (w : Raw (K := K) (tick := tick) allocation m sigma) : GroupOrbit (K := K) (tick := tick) allocation m sigma :=
  Quotient.mk'' (groupCoordinates allocation m sigma e w)

def usedOrbits (allocation : Allocation) (m : ℕ) (ε : ℝ) (sigma : Placement)
    (e : Targets (K := K) (tick := tick) allocation m sigma) : Finset (Orbit (K := K) (tick := tick) allocation m sigma) :=
  Finset.univ.filter fun o => ∃ w, Admissible allocation m ε sigma o.1 e w ∧
    orbitOf allocation m sigma e w = o.2

def full (allocation : Allocation) (m : ℕ) (sigma : Placement)
    (e : Targets (K := K) (tick := tick) allocation m sigma) (o : Orbit (K := K) (tick := tick) allocation m sigma) :
    Finset (Variable (K := K) (tick := tick) allocation m sigma) :=
  Finset.univ.filter fun v => v.1 = o.1 ∧ orbitOf allocation m sigma e v.2 = o.2

def passing (allocation : Allocation) (m : ℕ) (sigma : Placement) (ε : ℝ)
    (e : Targets (K := K) (tick := tick) allocation m sigma) (o : Orbit (K := K) (tick := tick) allocation m sigma) :
    Finset (Variable (K := K) (tick := tick) allocation m sigma) :=
  (full allocation m sigma e o).filter fun v => completeKeep allocation m ε (sigma v.1) sigma v.2

def competitors (allocation : Allocation) (m : ℕ) (ε : ℝ) (sigma : Placement)
    (e : Targets (K := K) (tick := tick) allocation m sigma)
    (_o : Orbit (K := K) (tick := tick) allocation m sigma) (v : Variable (K := K) (tick := tick) allocation m sigma) :
    Finset (Triple (Pos (K := K) (tick := tick) allocation m sigma)) :=
  (Finset.univ.image (coarse allocation m sigma)).filter fun t =>
    t ≠ coarse allocation m sigma e ∧
    tripleSide v.1 t = tripleSide v.1 (coarse allocation m sigma e) ∧
    ∃ f, coarse allocation m sigma f = t ∧ Compatible allocation m ε sigma v.1 f v.2

theorem full_pos (allocation : Allocation) (m : ℕ) (ε : ℝ) (sigma : Placement)
    (e : Targets (K := K) (tick := tick) allocation m sigma) (o : Orbit (K := K) (tick := tick) allocation m sigma)
    (ho : o ∈ usedOrbits allocation m ε sigma e) : 0 < (full allocation m sigma e o).card := by
  obtain ⟨w, _, hw⟩ := (Finset.mem_filter.mp ho).2
  apply Finset.card_pos.mpr
  exact ⟨(o.1, w), Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl, hw⟩⟩

theorem competitor_mem (allocation : Allocation) (m : ℕ) (ε : ℝ) (sigma : Placement)
    (e : Targets (K := K) (tick := tick) allocation m sigma) (o : Orbit (K := K) (tick := tick) allocation m sigma)
    (v : Variable (K := K) (tick := tick) allocation m sigma) (t : Triple (Pos (K := K) (tick := tick) allocation m sigma))
    (ht : t ∈ competitors allocation m ε sigma e o v) : t ∈ ambient allocation m sigma := by
  obtain ⟨f, hf, _⟩ := (Finset.mem_filter.mp ht).2.2.2
  rw [← hf]
  exact coarse_mem_ambient allocation m sigma f

theorem competitor_shares (allocation : Allocation) (m : ℕ) (ε : ℝ) (sigma : Placement)
    (e : Targets (K := K) (tick := tick) allocation m sigma) (o : Orbit (K := K) (tick := tick) allocation m sigma)
    (v : Variable (K := K) (tick := tick) allocation m sigma) (t : Triple (Pos (K := K) (tick := tick) allocation m sigma))
    (ht : t ∈ competitors allocation m ε sigma e o v) : SharesSide (coarse allocation m sigma e) t := by
  have h := (Finset.mem_filter.mp ht).2.2.1
  rcases v with ⟨side, w⟩
  fin_cases side
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

def data (allocation : Allocation) (m : ℕ) (ε : ℝ) (sigma : Placement) :
    JointMaskedSelection.OrbitData
      (Pos (K := K) (tick := tick) allocation m sigma) (Targets (K := K) (tick := tick) allocation m sigma)
      (Orbit (K := K) (tick := tick) allocation m sigma) (Variable (K := K) (tick := tick) allocation m sigma) where
  ambient := ambient allocation m sigma
  support := support allocation m sigma
  coarse := coarse allocation m sigma
  support_ambient := ambient_support allocation m sigma
  target_mem := coarse_mem_ambient allocation m sigma
  orbits := usedOrbits allocation m ε sigma
  full := full allocation m sigma
  passing := passing allocation m sigma ε
  full_pos := full_pos allocation m ε sigma
  passing_subset := fun _ _ _ => Finset.filter_subset _ _
  competitors := competitors allocation m ε sigma
  competitor_mem := fun e o _ v _ t ht => competitor_mem allocation m ε sigma e o v t ht
  competitor_ne := fun _ _ _ _ _ _ ht => (Finset.mem_filter.mp ht).2.1
  competitor_shares := fun e o _ v _ t ht => competitor_shares allocation m ε sigma e o v t ht

theorem admissible_covered (allocation : Allocation) (m : ℕ) (ε : ℝ) (sigma : Placement)
    (side : Fin 3) (e : Targets (K := K) (tick := tick) allocation m sigma)
    (w : Raw (K := K) (tick := tick) allocation m sigma) (hw : Admissible allocation m ε sigma side e w) :
    ∃ o ∈ (data allocation m ε sigma).orbits e,
      (side, w) ∈ (data allocation m ε sigma).full e o := by
  refine ⟨(side, orbitOf allocation m sigma e w), ?_, ?_⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, w, hw, rfl⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl, rfl⟩

theorem orbits_card_le (allocation : Allocation) (m : ℕ) (ε : ℝ) (sigma : Placement)
    (e : Targets (K := K) (tick := tick) allocation m sigma) :
    (((data allocation m ε sigma).orbits e).card : ℝ) ≤
      (3 * groupOrbitPrefactor (K := K) (tick := tick) allocation sigma) *
        ((m : ℝ) + 1) ^ groupDegree K tick sigma :=
  taggedUsedGroupOrbits_card_le_real allocation m sigma _

def actualCompatible (allocation : Allocation) (m : ℕ) (ε : ℝ) (sigma : Placement)
    (t : Triple (Pos (K := K) (tick := tick) allocation m sigma))
    (v : Variable (K := K) (tick := tick) allocation m sigma) : Prop :=
  ∃ f, coarse allocation m sigma f = t ∧ Compatible allocation m ε sigma v.1 f v.2

def actualUseful (allocation : Allocation) (m : ℕ) (ε : ℝ) (sigma : Placement)
    (t : Triple (Pos (K := K) (tick := tick) allocation m sigma))
    (v : Variable (K := K) (tick := tick) allocation m sigma) : Prop :=
  ∃ f, coarse allocation m sigma f = t ∧
    groupIdealSide allocation m ε (sigma v.1) sigma f v.2

def actualKeep (allocation : Allocation) (m : ℕ) (ε : ℝ) (sigma : Placement)
    (v : Variable (K := K) (tick := tick) allocation m sigma) : Prop :=
  completeKeep allocation m ε (sigma v.1) sigma v.2

@[simp] theorem actualCompatible_coarse (allocation : Allocation) (m : ℕ) (ε : ℝ)
    (sigma : Placement) (e : Targets (K := K) (tick := tick) allocation m sigma)
    (v : Variable (K := K) (tick := tick) allocation m sigma) :
    actualCompatible allocation m ε sigma (coarse allocation m sigma e) v ↔
      Compatible allocation m ε sigma v.1 e v.2 := by
  constructor
  · rintro ⟨f, hf, hv⟩
    exact (coarse_injective allocation m sigma hf) ▸ hv
  · exact fun hv => ⟨e, rfl, hv⟩

@[simp] theorem actualUseful_coarse (allocation : Allocation) (m : ℕ) (ε : ℝ)
    (sigma : Placement) (e : Targets (K := K) (tick := tick) allocation m sigma)
    (v : Variable (K := K) (tick := tick) allocation m sigma) :
    actualUseful allocation m ε sigma (coarse allocation m sigma e) v ↔
      groupIdealSide allocation m ε (sigma v.1) sigma e v.2 := by
  constructor
  · rintro ⟨f, hf, hv⟩
    exact (coarse_injective allocation m sigma hf) ▸ hv
  · exact fun hv => ⟨e, rfl, hv⟩

theorem competitor_coverage (allocation : Allocation) (m : ℕ) (ε : ℝ)
    (sigma : Placement) (e : Targets (K := K) (tick := tick) allocation m sigma)
    (o : Orbit (K := K) (tick := tick) allocation m sigma) (v : Variable (K := K) (tick := tick) allocation m sigma)
    (he : Compatible allocation m ε sigma v.1 e v.2)
    (t : Triple (Pos (K := K) (tick := tick) allocation m sigma))
    (hne : t ≠ coarse allocation m sigma e)
    (hc : actualCompatible allocation m ε sigma t v) :
    t ∈ (data allocation m ε sigma).competitors e o v := by
  obtain ⟨f, hf, hcomp⟩ := hc
  apply Finset.mem_filter.mpr
  refine ⟨?_, hne, ?_, f, hf, hcomp⟩
  · exact Finset.mem_image.mpr ⟨f, Finset.mem_univ _, hf⟩
  · rw [← hf]
    exact hcomp.1.trans he.1.symm

theorem mem_passing (allocation : Allocation) (m : ℕ) (ε : ℝ)
    (sigma : Placement) (e : Targets (K := K) (tick := tick) allocation m sigma)
    (o : Orbit (K := K) (tick := tick) allocation m sigma) (v : Variable (K := K) (tick := tick) allocation m sigma) :
    v ∈ (data allocation m ε sigma).passing e o ↔
      v ∈ (data allocation m ε sigma).full e o ∧ actualKeep allocation m ε sigma v :=
  Finset.mem_filter

end MatrixMultiplication.AllFieldGroupOrbitData

end

end OAI
