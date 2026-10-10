import OAI.LinearAlgebra.MatrixMultiplication.FieldGroups.DegreeLaws
import OAI.LinearAlgebra.MatrixMultiplication.FieldGroups.PairWindows
import OAI.LinearAlgebra.MatrixMultiplication.JointExtraction.CompatibilityCountProducer
import OAI.LinearAlgebra.MatrixMultiplication.JointExtraction.PairMixtureControls

namespace OAI

/-! Group assignments, orbit counts and extraction capacities. -/

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

end OAI
