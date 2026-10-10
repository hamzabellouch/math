import OAI.LinearAlgebra.MatrixMultiplication.FieldGroups.Degrees
import OAI.LinearAlgebra.MatrixMultiplication.FieldGroups.NativeLaws
import OAI.LinearAlgebra.MatrixMultiplication.FieldGroups.AmbientDegree

namespace OAI

/-! Group assignments, orbit counts and extraction capacities. -/

noncomputable section

namespace MatrixMultiplication.AllFieldGroupDegreeLaws

open AllFieldHistory AllFieldHistorySupport AllFieldHistoryChildLaws
open AllFieldGroupOrbitData AllFieldGroupDegrees AllFieldGroupNativeLaws
open JointPopulation JointCanonicalization MatrixMultiplication.Foundation Filter
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable Classical.decEq

variable {K tick : ℕ}

def nativeLaw (allocation : Allocation) (right : Bool) (side : Fin 3)
    (sigma : Placement) (c : Class (K := K) (tick := tick) sigma)
    (u : JointPopulation.Shape) : Symbol (K := K) (tick := tick) sigma c → ℝ :=
  supportedHalfLaw allocation right c.1.val u (sigma side)

theorem nativeLaw_bounds (allocation : Allocation) (right : Bool) (side : Fin 3)
    (sigma : Placement) (c : Class (K := K) (tick := tick) sigma)
    (u : JointPopulation.Shape) (a : Symbol (K := K) (tick := tick) sigma c) :
    0 ≤ nativeLaw allocation right side sigma c u a ∧
      nativeLaw allocation right side sigma c u a ≤ 1 :=
  supportedHalfLaw_bounds allocation right c.1.val u (sigma side) a

theorem weighted_classLaw_eq_native (allocation : Allocation) (m : ℕ)
    (right : Bool) (side : Fin 3) (sigma : Placement)
    (h : ActiveOrder K tick sigma) (u : JointPopulation.Shape)
    (hd : designated right side sigma h u) (a : Statistic h.val) :
    (Counts (K := K) (tick := tick) allocation m sigma h u : ℝ) * compatibilityLaw right side sigma h u a =
      (Counts (K := K) (tick := tick) allocation m sigma h u : ℝ) *
        supportedHalfLaw allocation right h.val u (sigma side) a := by
  by_cases hp : 0 < Counts (K := K) (tick := tick) allocation m sigma h u
  · rw [compatibilityLaw_eq allocation m sigma right side h u hp hd,
      supportedHalfLaw_eq_of_counts_pos allocation m right h.val u hp (sigma side)]
    rfl
  · have hz : Counts (K := K) (tick := tick) allocation m sigma h u = 0 := Nat.eq_zero_of_not_pos hp
    simp only [hz, Nat.cast_zero, zero_mul]

theorem compatible_iff_native (allocation : Allocation) (m : ℕ) (χ : ℝ)
    (sigma : Placement) (side : Fin 3)
    (e : Targets (K := K) (tick := tick) allocation m sigma)
    (w : Raw (K := K) (tick := tick) allocation m sigma) :
    JointPopulationCompatibility.Compatible (Counts (K := K) (tick := tick) allocation m sigma)
      (Letter (K := K) (tick := tick) sigma) (Letter (K := K) (tick := tick) sigma) (Symbol (K := K) (tick := tick) sigma) (Symbol (K := K) (tick := tick) sigma)
      (projectedStatistic sigma) (projectedStatistic sigma)
      (classDesignated false side sigma) (classDesignated true side sigma)
      (classLaw false side sigma) (classLaw true side sigma) χ (sigma side) e w ↔
    JointPopulationCompatibility.Compatible (Counts (K := K) (tick := tick) allocation m sigma)
      (Letter (K := K) (tick := tick) sigma) (Letter (K := K) (tick := tick) sigma) (Symbol (K := K) (tick := tick) sigma) (Symbol (K := K) (tick := tick) sigma)
      (projectedStatistic sigma) (projectedStatistic sigma)
      (classDesignated false side sigma) (classDesignated true side sigma)
      (nativeLaw allocation false side sigma) (nativeLaw allocation true side sigma)
      χ (sigma side) e w := by
  constructor <;> rintro ⟨hL, hR⟩ <;> constructor
  · intro h u hd a
    have hh := hL h u hd a
    change |_ - (Counts (K := K) (tick := tick) allocation m sigma h u : ℝ) *
      supportedHalfLaw allocation false h.val u (sigma side) a| ≤ _
    rw [← weighted_classLaw_eq_native allocation m false side sigma h u hd a]
    exact hh
  · intro h u hd a
    have hh := hR h u hd a
    change |_ - (Counts (K := K) (tick := tick) allocation m sigma h u : ℝ) *
      supportedHalfLaw allocation true h.val u (sigma side) a| ≤ _
    rw [← weighted_classLaw_eq_native allocation m true side sigma h u hd a]
    exact hh
  · intro h u hd a
    have hh := hL h u hd a
    change |_ - (Counts (K := K) (tick := tick) allocation m sigma h u : ℝ) *
      compatibilityLaw false side sigma h u a| ≤ _
    rw [weighted_classLaw_eq_native allocation m false side sigma h u hd a]
    exact hh
  · intro h u hd a
    have hh := hR h u hd a
    change |_ - (Counts (K := K) (tick := tick) allocation m sigma h u : ℝ) *
      compatibilityLaw true side sigma h u a| ≤ _
    rw [weighted_classLaw_eq_native allocation m true side sigma h u hd a]
    exact hh

def nativeCount (allocation : Allocation) (m : ℕ) (χ : ℝ)
    (sigma : Placement) (side : Fin 3) (w : Raw (K := K) (tick := tick) allocation m sigma) : ℕ :=
  JointPopulationCompatibility.compatibleTargetCount (Counts (K := K) (tick := tick) allocation m sigma)
    (Letter (K := K) (tick := tick) sigma) (Letter (K := K) (tick := tick) sigma) (Symbol (K := K) (tick := tick) sigma) (Symbol (K := K) (tick := tick) sigma)
    (projectedStatistic sigma) (projectedStatistic sigma)
    (classDesignated false side sigma) (classDesignated true side sigma)
    (nativeLaw allocation false side sigma) (nativeLaw allocation true side sigma) χ
    (sigma side) (ownWord allocation m sigma w) w

theorem conditionalCount_eq_native (allocation : Allocation) (m : ℕ) (χ : ℝ)
    (sigma : Placement) (side : Fin 3) (w : Raw (K := K) (tick := tick) allocation m sigma) :
    conditionalCount allocation m χ sigma side w = nativeCount allocation m χ sigma side w := by
  unfold conditionalCount nativeCount JointPopulationCompatibility.compatibleTargetCount
  exact Fintype.card_congr (Equiv.subtypeEquivRight
    (fun e : JointPopulationCompatibility.FixedSideTargets
      (Counts (K := K) (tick := tick) allocation m sigma) (sigma side)
      (ownWord allocation m sigma w) =>
        compatible_iff_native allocation m χ sigma side e.val w))

theorem competitors_card_le_nativeCount (allocation : Allocation) (m : ℕ)
    {ε χ : ℝ} (hε : 0 ≤ ε) (hχ : ε ≤ χ) (sigma : Placement)
    (e : Targets (K := K) (tick := tick) allocation m sigma)
    (o : Orbit (K := K) (tick := tick) allocation m sigma) (v : Variable (K := K) (tick := tick) allocation m sigma) :
    (competitors allocation m ε sigma e o v).card ≤ nativeCount allocation m χ sigma v.1 v.2 := by
  rw [← conditionalCount_eq_native]
  exact competitors_card_le_conditionalCount allocation m hε hχ sigma e o v

theorem competitors_subset_eligibility_of_first (allocation : Allocation) (m : ℕ)
    (width : ℝ) (sigma : Placement)
    (e : Targets (K := K) (tick := tick) allocation m sigma)
    (o : Orbit (K := K) (tick := tick) allocation m sigma) (v : Variable (K := K) (tick := tick) allocation m sigma) (hv : v.1 = 0) :
    competitors allocation m width sigma e o v ⊆
      (data allocation m width sigma).eligibilityCompetitors e := by
  intro t ht
  apply ((data allocation m width sigma).mem_eligibilityCompetitors e t).2
  refine ⟨competitor_mem allocation m width sigma e o v t ht,
    (Finset.mem_filter.mp ht).2.1, ?_⟩
  have hh := (Finset.mem_filter.mp ht).2.2.1
  simpa only [hv, tripleSide, Matrix.cons_val_zero] using! hh

theorem eventually_eligibility_card_le (allocation : Allocation) (sigma : Placement)
    (width : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ m : ℕ in atTop, ∀ e : Targets (K := K) (tick := tick) allocation m sigma,
      (((data allocation m width sigma).eligibilityCompetitors e).card : ℝ) ≤
        Real.exp ((m : ℝ) *
          (AllFieldActiveCapacity.orderNativeDegree (K := K) (tick := tick) allocation sigma 0 + δ)) := by
  filter_upwards [AllFieldGroupAmbientDegree.eventually_sharedAmbient_first_card_le
    (K := K) (tick := tick) allocation sigma hδ] with m hm
  intro e
  exact (Nat.cast_le.mpr (eligibility_card_le_sharedAmbient allocation m width sigma e)).trans (hm e)

theorem eventually_first_competitors_card_le (allocation : Allocation) (sigma : Placement)
    (width : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ m : ℕ in atTop, ∀ (e : Targets (K := K) (tick := tick) allocation m sigma)
      (o : Orbit (K := K) (tick := tick) allocation m sigma) (v : Variable (K := K) (tick := tick) allocation m sigma), v.1 = 0 →
      ((competitors allocation m width sigma e o v).card : ℝ) ≤
        Real.exp ((m : ℝ) *
          (AllFieldActiveCapacity.orderNativeDegree (K := K) (tick := tick) allocation sigma 0 + δ)) := by
  filter_upwards [eventually_eligibility_card_le (K := K) (tick := tick)
    allocation sigma width hδ] with m hm
  intro e o v hv
  exact (Nat.cast_le.mpr (Finset.card_le_card
    (competitors_subset_eligibility_of_first allocation m width sigma e o v hv))).trans (hm e)

end MatrixMultiplication.AllFieldGroupDegreeLaws

end

end OAI
