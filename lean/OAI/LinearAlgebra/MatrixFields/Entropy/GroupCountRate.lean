import Mathlib
import OAI.LinearAlgebra.MatrixFields.Construction.GroupAmbientDegree
import OAI.LinearAlgebra.MatrixFields.Construction.JointCompatibilityCountProducer

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
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
  simp only [hv, tripleSide, Matrix.cons_val_zero] at hh
  exact hh

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
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.AllFieldGroupCountRate

open AllFieldHistory AllFieldHistorySupport AllFieldHistoryChildLaws
open AllFieldGroupOrbitData AllFieldGroupDegrees AllFieldGroupDegreeLaws
open AllFieldGroupNativeLaws AllFieldGroupPairWindows
open JointCompatibilityControls JointCompatibilityScaling JointCompatibilityRateLimit
open JointPopulationCompatibility JointTypeCounts MatrixMultiplication.Foundation Filter
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable Classical.decEq

variable {K tick : ℕ}

def nativeCompatibilityRate (allocation : Allocation) (sigma : Placement) (side : Fin 3) : ℝ :=
  compatibilityRate (base (K := K) (tick := tick) allocation sigma side)
    (q allocation sigma side)
    (classDesignated false side sigma) (classDesignated true side sigma)
    (groupCap (base allocation sigma side) (classDesignated false side sigma)
      (nativeLaw allocation false side sigma) 0)
    (groupCap (base allocation sigma side) (classDesignated true side sigma)
      (nativeLaw allocation true side sigma) 0)

theorem base_positive_counts (allocation : Allocation) (sigma : Placement) (side : Fin 3)
    (c : Class (K := K) (tick := tick) sigma) (u : JointPopulation.Shape)
    (hu : 0 < base allocation sigma side c u) :
    0 < Counts (K := K) (tick := tick) allocation 1 sigma c.1 u := by
  unfold base classCounts at hu
  split_ifs at hu with hs
  · exact hu
  · exact (Nat.lt_irrefl 0 hu).elim

theorem nativeLaw_normalized (allocation : Allocation) (right : Bool)
    (sigma : Placement) (side : Fin 3)
    (c : Class (K := K) (tick := tick) sigma) (u : JointPopulation.Shape)
    (hu : 0 < base allocation sigma side c u) :
    ∑ a, nativeLaw allocation right side sigma c u a = 1 := by
  have hp := base_positive_counts allocation sigma side c u hu
  simp only [nativeLaw,
    supportedHalfLaw_eq_of_counts_pos allocation 1 right c.1.val u hp (sigma side)]
  exact halfLawAt_normalized allocation 1 right c.1.val u hp (sigma side)

theorem classCounts_dilation (allocation : Allocation) (m : ℕ)
    (sigma : Placement) (side : Fin 3) :
    classCounts (Counts (K := K) (tick := tick) allocation m sigma) (sigma side) =
      fun c u => m * base allocation sigma side c u := by
  funext c u
  change (if JointPopulation.shapeSide (sigma side) u = c.2 then
    activeCounts allocation m c.1.val u else 0) =
    m * (if JointPopulation.shapeSide (sigma side) u = c.2 then
      activeCounts allocation 1 c.1.val u else 0)
  rw [activeCounts_dilation]
  split_ifs <;> simp

theorem exists_widths_eventually_nativeCount_le (allocation : Allocation) (sigma : Placement)
    (side : Fin 3) {δ χMax ηMax : ℝ}
    (hδ : 0 < δ) (hχMax : 0 < χMax) (hηMax : 0 < ηMax) :
    ∃ χ η : ℝ, 0 < χ ∧ χ ≤ χMax ∧ 0 < η ∧ η ≤ ηMax ∧
      ∀ᶠ m : ℕ in atTop,
        ∀ (e : Targets (K := K) (tick := tick) allocation m sigma)
          (w : Raw (K := K) (tick := tick) allocation m sigma),
          (∀ h j, JointPopulation.shapeSide (sigma side) ((e h).val j) =
            ownWord allocation m sigma w ⟨h, j⟩) →
          PairWindow (base allocation sigma side) (q allocation sigma side)
            (Positions (K := K) (tick := tick) allocation m sigma w) (pairCounts allocation m sigma w) η →
          (nativeCount allocation m χ sigma side w : ℝ) ≤
            Real.exp ((m : ℝ) *
              (nativeCompatibilityRate (K := K) (tick := tick) allocation sigma side + δ)) := by
  have hparts : ∀ c : Class (K := K) (tick := tick) sigma,
      Function.Injective (fun a : Symbol (K := K) (tick := tick) sigma c × Symbol (K := K) (tick := tick) sigma c => (a.1, a.2)) :=
    fun _ => fun _ _ h => h
  have hleft : ∀ (c : Class (K := K) (tick := tick) sigma) (a : Symbol (K := K) (tick := tick) sigma c),
      (baseSize (base allocation sigma side) c : ℝ) *
        (∑ b : {b : Symbol (K := K) (tick := tick) sigma c × Symbol (K := K) (tick := tick) sigma c // b.1 = a}, q allocation sigma side c b.val) =
          totalCenterCount (base allocation sigma side) (nativeLaw allocation false side sigma) c a := by
    intro c a
    exact JointPairMixtureControls.pairMixture_left_balance
      (base allocation sigma side) (nativeLaw allocation false side sigma)
      (nativeLaw allocation true side sigma)
      (nativeLaw_normalized allocation true sigma side) c a
  have hright : ∀ (c : Class (K := K) (tick := tick) sigma) (a : Symbol (K := K) (tick := tick) sigma c),
      (baseSize (base allocation sigma side) c : ℝ) *
        (∑ b : {b : Symbol (K := K) (tick := tick) sigma c × Symbol (K := K) (tick := tick) sigma c // b.2 = a}, q allocation sigma side c b.val) =
          totalCenterCount (base allocation sigma side) (nativeLaw allocation true side sigma) c a := by
    intro c a
    exact JointPairMixtureControls.pairMixture_right_balance
      (base allocation sigma side) (nativeLaw allocation false side sigma)
      (nativeLaw allocation true side sigma)
      (nativeLaw_normalized allocation false sigma side) c a
  obtain ⟨χ, η, hχ, hχMax', hη, hηMax', hbound⟩ :=
    JointCompatibilityCountProducer.exists_widths_eventually_count_le
      (base allocation sigma side) (q allocation sigma side)
      (fun _ p => p.1) (fun _ p => p.2)
      (classDesignated false side sigma) (classDesignated true side sigma)
      (nativeLaw allocation false side sigma) (nativeLaw allocation true side sigma)
      hparts
      (fun c u a => (nativeLaw_bounds allocation false side sigma c u a).1)
      (fun c u a => (nativeLaw_bounds allocation false side sigma c u a).2)
      (fun c u a => (nativeLaw_bounds allocation true side sigma c u a).1)
      (fun c u a => (nativeLaw_bounds allocation true side sigma c u a).2)
      hleft hright hδ hχMax hηMax
  refine ⟨χ, η, hχ, hχMax', hη, hηMax', ?_⟩
  filter_upwards [hbound] with m hm
  intro e w hown hwindow
  rw [← classCounts_dilation allocation m sigma side] at hm
  let target : FixedSideTargets (Counts (K := K) (tick := tick) allocation m sigma) (sigma side)
      (ownWord allocation m sigma w) := ⟨e, hown⟩
  have hb := (hm (Positions (K := K) (tick := tick) allocation m sigma w) (pairCounts allocation m sigma w)
    (candidateEquiv (Counts (K := K) (tick := tick) allocation m sigma) (sigma side)
      (ownWord allocation m sigma w) target)
    (statisticElement (Counts (K := K) (tick := tick) allocation m sigma) (Letter (K := K) (tick := tick) sigma) (Letter (K := K) (tick := tick) sigma)
      (Symbol (K := K) (tick := tick) sigma) (Symbol (K := K) (tick := tick) sigma) (projectedStatistic sigma) (projectedStatistic sigma)
      (ownWord allocation m sigma w) w) hwindow).1
  rw [nativeCount, compatibleTargetCount_eq_kernel]
  exact hb

theorem exists_threshold_eventually_competitors_le (allocation : Allocation)
    (sigma : Placement) (side : Fin 3) {δ widthMax : ℝ}
    (hδ : 0 < δ) (hwidthMax : 0 < widthMax) :
    ∃ threshold : ℝ, 0 < threshold ∧ threshold ≤ widthMax ∧
      ∀ width : ℝ, 0 < width → width ≤ threshold →
        ∀ᶠ m : ℕ in atTop,
          ∀ (e : Targets (K := K) (tick := tick) allocation m sigma)
            (o : Orbit (K := K) (tick := tick) allocation m sigma), o ∈ (data allocation m width sigma).orbits e →
            ∀ w : Raw (K := K) (tick := tick) allocation m sigma,
              (side, w) ∈ (data allocation m width sigma).passing e o →
              ((competitors allocation m width sigma e o (side, w)).card : ℝ) ≤
                Real.exp ((m : ℝ) *
                  (nativeCompatibilityRate (K := K) (tick := tick) allocation sigma side + δ)) := by
  obtain ⟨χ, η, hχ, hχMax, hη, _, hbound⟩ :=
    exists_widths_eventually_nativeCount_le (K := K) (tick := tick)
      allocation sigma side (ηMax := 1) hδ hwidthMax zero_lt_one
  let threshold := min χ (η / windowFactor (K := K) (tick := tick) allocation sigma)
  have hf := windowFactor_pos (K := K) (tick := tick) allocation sigma
  have ht : 0 < threshold := lt_min hχ (div_pos hη hf)
  refine ⟨threshold, ht, (min_le_left _ _).trans hχMax, ?_⟩
  intro width hw hwt
  have hwχ : width ≤ χ := hwt.trans (min_le_left _ _)
  have hww : windowFactor (K := K) (tick := tick) allocation sigma * width ≤ η := by
    have hh := (le_div_iff₀ hf).mp (hwt.trans (min_le_right _ _))
    simpa only [mul_comm] using hh
  filter_upwards [hbound, eventually_gt_atTop (0 : ℕ)] with m hm hmpos
  intro e o ho w hpass
  have ha := AllFieldGroupAdmissible.full_admissible allocation m width sigma
    e o ho (side, w) ((data allocation m width sigma).passing_subset e o ho hpass)
  have hp := passing_pairWindow allocation hmpos hw.le sigma e o ho (side, w) hpass
  have hpair : PairWindow (base allocation sigma side) (q allocation sigma side)
      (Positions (K := K) (tick := tick) allocation m sigma w) (pairCounts allocation m sigma w) η :=
    fun c hc a => (hp c hc a).trans hww
  have hc := hm e w (fun h j => (ha.1.1 h j).symm) hpair
  exact (Nat.cast_le.mpr (competitors_card_le_nativeCount allocation m hw.le hwχ sigma
    e o (side, w))).trans hc

end MatrixMultiplication.AllFieldGroupCountRate

end
end

end MatrixAllFields

end OAI
