import OAI.LinearAlgebra.MatrixMultiplication.FieldGroups.OrbitData
import OAI.LinearAlgebra.MatrixMultiplication.FieldConstruction.ActiveCapacity
import OAI.LinearAlgebra.MatrixMultiplication.FieldGroups.TargetRate
import OAI.LinearAlgebra.MatrixMultiplication.JointExtraction.PopulationCompatibility
import OAI.LinearAlgebra.MatrixMultiplication.JointExtraction.AmbientDegree

namespace OAI

/-! Group assignments, orbit counts and extraction capacities. -/

noncomputable section

namespace MatrixMultiplication.AllFieldGroupDegrees

open AllFieldHistory AllFieldHistorySupport AllFieldHistoryChildLaws
open AllFieldGroupOrbitData JointPopulation JointCanonicalization
open MatrixMultiplication.Foundation
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

variable {K tick : ℕ}

abbrev Letter (sigma : Placement) (h : ActiveOrder K tick sigma) :=
  Fin (activeHalfLength h.val) → Fin 7

abbrev Class (sigma : Placement) := ActiveOrder K tick sigma × Fin 17

abbrev Symbol (sigma : Placement) (c : Class (K := K) (tick := tick) sigma) :=
  Statistic c.1.val

def projectedStatistic (sigma : Placement)
    (c : Class (K := K) (tick := tick) sigma) : Letter (K := K) (tick := tick) sigma c.1 → Symbol (K := K) (tick := tick) sigma c :=
  statistic c.1.val

def classDesignated (right : Bool) (side : Fin 3) (sigma : Placement)
    (c : Class (K := K) (tick := tick) sigma) (u : JointPopulation.Shape) : Prop :=
  designated right side sigma c.1 u

def classLaw (right : Bool) (side : Fin 3) (sigma : Placement)
    (c : Class (K := K) (tick := tick) sigma) (u : JointPopulation.Shape) :
    Symbol (K := K) (tick := tick) sigma c → ℝ := compatibilityLaw right side sigma c.1 u

theorem tripleSide_eq_sideWord (allocation : Allocation) (m : ℕ) (sigma : Placement)
    (s : Fin 3) (t : JointCoarseHashing.Triple (Pos (K := K) (tick := tick) allocation m sigma))
    (h : ActiveOrder K tick sigma) (i : JointPopulation.Positions (Counts (K := K) (tick := tick) allocation m sigma) h) :
    tripleSide s t ⟨h, i⟩ = sideWord (Counts (K := K) (tick := tick) allocation m sigma) s t h i := by
  fin_cases s <;> rfl

theorem tripleSide_triple (allocation : Allocation) (m : ℕ) (sigma : Placement)
    (s : Fin 3) (e : Targets (K := K) (tick := tick) allocation m sigma)
    (h : ActiveOrder K tick sigma) (i : JointPopulation.Positions (Counts (K := K) (tick := tick) allocation m sigma) h) :
    tripleSide s (triple (Counts (K := K) (tick := tick) allocation m sigma) e) ⟨h, i⟩ =
      shapeSide s ((e h).val i) := by
  fin_cases s <;> rfl

theorem childWidth_le {ε : ℝ} (hε : 0 ≤ ε) (h : Active K tick) :
    AllFieldHistoryMasks.childWidth ε h ≤ ε := by
  have hp : 0 ≤ AllFieldHistoryMasks.pairWidth ε h := by
    unfold AllFieldHistoryMasks.pairWidth
    positivity
  calc
    AllFieldHistoryMasks.childWidth ε h ≤ AllFieldHistoryMasks.pairWidth ε h :=
      div_le_self hp (by norm_num)
    _ ≤ ε := div_le_self hε (one_le_pow₀ (by norm_num))

theorem fineCompatible_uniform (allocation : Allocation) (m : ℕ)
    {ε χ : ℝ} (hε : 0 ≤ ε) (hχ : ε ≤ χ) (sigma : Placement) (side : Fin 3)
    (e : Targets (K := K) (tick := tick) allocation m sigma)
    (w : Raw (K := K) (tick := tick) allocation m sigma)
    (hw : fineCompatible allocation m ε sigma side e w) :
    JointPopulationCompatibility.Compatible (Counts (K := K) (tick := tick) allocation m sigma)
      (Letter (K := K) (tick := tick) sigma) (Letter (K := K) (tick := tick) sigma) (Symbol (K := K) (tick := tick) sigma) (Symbol (K := K) (tick := tick) sigma)
      (projectedStatistic sigma) (projectedStatistic sigma)
      (classDesignated false side sigma) (classDesignated true side sigma)
      (classLaw false side sigma) (classLaw true side sigma) χ (sigma side) e w := by
  constructor
  · intro h u hd a
    exact (hw false h u hd a).trans
      (mul_le_mul_of_nonneg_left ((childWidth_le hε h.val).trans hχ) (Nat.cast_nonneg _))
  · intro h u hd a
    exact (hw true h u hd a).trans
      (mul_le_mul_of_nonneg_left ((childWidth_le hε h.val).trans hχ) (Nat.cast_nonneg _))

def uniformCompatible (allocation : Allocation) (m : ℕ) (χ : ℝ)
    (sigma : Placement) (side : Fin 3)
    (e : Targets (K := K) (tick := tick) allocation m sigma)
    (w : Raw (K := K) (tick := tick) allocation m sigma) : Prop :=
  JointPopulationCompatibility.compatibleWithCoarse (Counts (K := K) (tick := tick) allocation m sigma)
    (Letter (K := K) (tick := tick) sigma) (Letter (K := K) (tick := tick) sigma) (Symbol (K := K) (tick := tick) sigma) (Symbol (K := K) (tick := tick) sigma)
    (projectedStatistic sigma) (projectedStatistic sigma)
    (classDesignated false side sigma) (classDesignated true side sigma)
    (classLaw false side sigma) (classLaw true side sigma) χ
    (ownWord allocation m sigma) (sigma side) (triple (Counts (K := K) (tick := tick) allocation m sigma) e) w

theorem Compatible_uniform (allocation : Allocation) (m : ℕ)
    {ε χ : ℝ} (hε : 0 ≤ ε) (hχ : ε ≤ χ) (sigma : Placement) (side : Fin 3)
    (e : Targets (K := K) (tick := tick) allocation m sigma)
    (w : Raw (K := K) (tick := tick) allocation m sigma)
    (hw : Compatible allocation m ε sigma side e w) :
    uniformCompatible allocation m χ sigma side e w := by
  apply (JointPopulationCompatibility.compatibleWithCoarse_target
    (Counts (K := K) (tick := tick) allocation m sigma) (Letter (K := K) (tick := tick) sigma) (Letter (K := K) (tick := tick) sigma)
    (Symbol (K := K) (tick := tick) sigma) (Symbol (K := K) (tick := tick) sigma) (projectedStatistic sigma) (projectedStatistic sigma)
    (classDesignated false side sigma) (classDesignated true side sigma)
    (classLaw false side sigma) (classLaw true side sigma) χ
    (ownWord allocation m sigma) (sigma side) e w).2
  refine ⟨?_, fineCompatible_uniform allocation m hε hχ sigma side e w hw.2⟩
  intro h i
  have hh := congrFun hw.1 ⟨h, i⟩
  simpa only [coarse, tripleSide_reorder, tripleSide_triple] using hh

def conditionalCount (allocation : Allocation) (m : ℕ) (χ : ℝ)
    (sigma : Placement) (side : Fin 3) (w : Raw (K := K) (tick := tick) allocation m sigma) : ℕ :=
  JointPopulationCompatibility.compatibleTargetCount (Counts (K := K) (tick := tick) allocation m sigma)
    (Letter (K := K) (tick := tick) sigma) (Letter (K := K) (tick := tick) sigma) (Symbol (K := K) (tick := tick) sigma) (Symbol (K := K) (tick := tick) sigma)
    (projectedStatistic sigma) (projectedStatistic sigma)
    (classDesignated false side sigma) (classDesignated true side sigma)
    (classLaw false side sigma) (classLaw true side sigma) χ
    (sigma side) (ownWord allocation m sigma w) w

theorem uniformCompatible_count (allocation : Allocation) (m : ℕ) (χ : ℝ)
    (sigma : Placement) (side : Fin 3) (w : Raw (K := K) (tick := tick) allocation m sigma) :
    Fintype.card {e : Targets (K := K) (tick := tick) allocation m sigma //
      uniformCompatible allocation m χ sigma side e w} =
      conditionalCount allocation m χ sigma side w :=
  JointPopulationCompatibility.compatibleWithCoarse_target_count
    (Counts (K := K) (tick := tick) allocation m sigma) (Letter (K := K) (tick := tick) sigma) (Letter (K := K) (tick := tick) sigma)
    (Symbol (K := K) (tick := tick) sigma) (Symbol (K := K) (tick := tick) sigma) (projectedStatistic sigma) (projectedStatistic sigma)
    (classDesignated false side sigma) (classDesignated true side sigma)
    (classLaw false side sigma) (classLaw true side sigma) χ
    (ownWord allocation m sigma) (sigma side) w

theorem competitors_card_le_conditionalCount (allocation : Allocation) (m : ℕ)
    {ε χ : ℝ} (hε : 0 ≤ ε) (hχ : ε ≤ χ) (sigma : Placement)
    (e : Targets (K := K) (tick := tick) allocation m sigma)
    (o : Orbit (K := K) (tick := tick) allocation m sigma) (v : Variable (K := K) (tick := tick) allocation m sigma) :
    (competitors allocation m ε sigma e o v).card ≤
      conditionalCount allocation m χ sigma v.1 v.2 := by
  classical
  let candidates : Finset (Targets (K := K) (tick := tick) allocation m sigma) :=
    Finset.univ.filter fun f => uniformCompatible allocation m χ sigma v.1 f v.2
  have hsub : competitors allocation m ε sigma e o v ⊆
      candidates.image (coarse allocation m sigma) := by
    intro t ht
    obtain ⟨f, hf, hc⟩ := (Finset.mem_filter.mp ht).2.2.2
    exact Finset.mem_image.mpr ⟨f, Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, Compatible_uniform allocation m hε hχ sigma v.1 f v.2 hc⟩, hf⟩
  calc
    (competitors allocation m ε sigma e o v).card ≤
        (candidates.image (coarse allocation m sigma)).card := Finset.card_le_card hsub
    _ ≤ candidates.card := Finset.card_image_le
    _ = Fintype.card {f : Targets (K := K) (tick := tick) allocation m sigma //
        uniformCompatible allocation m χ sigma v.1 f v.2} := by
      simp only [candidates, Fintype.card_subtype]
    _ = conditionalCount allocation m χ sigma v.1 v.2 :=
      uniformCompatible_count allocation m χ sigma v.1 v.2

theorem eligibility_card_le_sharedAmbient (allocation : Allocation) (m : ℕ)
    (ε : ℝ) (sigma : Placement)
    (e : Targets (K := K) (tick := tick) allocation m sigma) :
    ((data allocation m ε sigma).eligibilityCompetitors e).card ≤
      (JointAmbientDegree.sharedAmbient (Counts (K := K) (tick := tick) allocation m sigma)
        (fun h => 2 * activeHalfLength h.val) (sigma 0)
        (triple (Counts (K := K) (tick := tick) allocation m sigma) e)).card := by
  let a := JointAmbientDegree.sharedAmbient (Counts (K := K) (tick := tick) allocation m sigma)
    (fun h => 2 * activeHalfLength h.val) (sigma 0)
    (triple (Counts (K := K) (tick := tick) allocation m sigma) e)
  have hs : (data allocation m ε sigma).eligibilityCompetitors e ⊆
      a.image (reorder sigma) := by
    intro f hf
    obtain ⟨ha, _, hx⟩ :=
      ((data allocation m ε sigma).mem_eligibilityCompetitors e f).1 hf
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp ha
    apply Finset.mem_image.mpr
    refine ⟨t, Finset.mem_filter.mpr ⟨ht, ?_⟩, rfl⟩
    intro h
    funext i
    have hh := congrFun hx ⟨h, i⟩
    change tripleSide (sigma 0) t ⟨h, i⟩ =
      tripleSide (sigma 0) (triple (Counts (K := K) (tick := tick) allocation m sigma) e) ⟨h, i⟩ at hh
    simpa only [tripleSide_eq_sideWord] using hh
  exact (Finset.card_le_card hs).trans Finset.card_image_le

end MatrixMultiplication.AllFieldGroupDegrees

end

end OAI
