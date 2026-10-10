import OAI.LinearAlgebra.MatrixMultiplication.FieldGroups.AdmissibilityCore
import OAI.LinearAlgebra.MatrixMultiplication.FieldGroups.Degrees
import OAI.LinearAlgebra.MatrixMultiplication.FieldGroups.NativeLaws
import OAI.LinearAlgebra.MatrixMultiplication.FieldHistory.MaskLaws
import OAI.LinearAlgebra.MatrixMultiplication.JointExtraction.PairClassWindows
import OAI.LinearAlgebra.MatrixMultiplication.JointExtraction.PairMixtureControls
import OAI.LinearAlgebra.MatrixMultiplication.JointExtraction.CompatibilityRateLimit

namespace OAI

/-! Group assignments, orbit counts and extraction capacities. -/

noncomputable section

namespace MatrixMultiplication.AllFieldGroupPairWindows

open MatrixMultiplication.Foundation AllFieldHistory AllFieldHistorySupport
open AllFieldHistoryChildLaws AllFieldHistoryMasks AllFieldHistoryMaskLaws
open AllFieldHistoryGroupMasks AllFieldHistoryGroupedRecovery
open AllFieldGroupOrbitData AllFieldGroupDegrees AllFieldGroupNativeLaws
open JointCompatibilityScaling JointCompatibilityRateLimit
open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {K tick : ℕ}

def base (allocation : Allocation) (sigma : Placement) (side : Fin 3) :=
  JointPopulationCompatibility.classCounts
    (Counts (K := K) (tick := tick) allocation 1 sigma) (sigma side)

def q (allocation : Allocation) (sigma : Placement) (side : Fin 3)
    (c : Class (K := K) (tick := tick) sigma) : Symbol (K := K) (tick := tick) sigma c × Symbol (K := K) (tick := tick) sigma c → ℝ :=
  JointPairMixtureControls.pairMixture (base (K := K) (tick := tick) allocation sigma side)
    (fun c u => supportedHalfLaw allocation false c.1.val u (sigma side))
    (fun c u => supportedHalfLaw allocation true c.1.val u (sigma side)) c

abbrev Positions (allocation : Allocation) (m : ℕ) (sigma : Placement)
    (w : Raw (K := K) (tick := tick) allocation m sigma) :=
  JointPopulationCompatibility.ClassPos (Counts (K := K) (tick := tick) allocation m sigma)
    (ownWord (K := K) (tick := tick) allocation m sigma w)

def pairCounts (allocation : Allocation) (m : ℕ) (sigma : Placement)
    (w : Raw (K := K) (tick := tick) allocation m sigma) :=
  JointPopulationCompatibility.statisticCounts (Counts (K := K) (tick := tick) allocation m sigma)
    (Letter (K := K) (tick := tick) sigma) (Letter (K := K) (tick := tick) sigma) (Symbol (K := K) (tick := tick) sigma) (Symbol (K := K) (tick := tick) sigma)
    (projectedStatistic (K := K) (tick := tick) sigma) (projectedStatistic (K := K) (tick := tick) sigma)
    (ownWord (K := K) (tick := tick) allocation m sigma w) w

def parentBase {sigma : Placement} (allocation : Allocation) (h : ActiveOrder K tick sigma) : ℕ :=
  population allocation 1 (h.val.val.1.source, h.val.val.2)

def parentPair (allocation : Allocation) (sigma : Placement) (side : Fin 3)
    (h : ActiveOrder K tick sigma) (a : Statistic h.val × Statistic h.val) : ℝ :=
  (∑ u, (activeCounts allocation 1 h.val u : ℝ) *
    supportedHalfLaw allocation false h.val u (sigma side) a.1 *
    supportedHalfLaw allocation true h.val u (sigma side) a.2) / parentBase (K := K) (tick := tick) allocation h

def classMass (allocation : Allocation) (sigma : Placement) (side : Fin 3)
    (c : Class (K := K) (tick := tick) sigma) : ℝ :=
  (baseSize (base (K := K) (tick := tick) allocation sigma side) c : ℝ) / parentBase (K := K) (tick := tick) allocation c.1

def windowFactor (allocation : Allocation) (sigma : Placement) : ℝ :=
  1 + ∑ h : ActiveOrder K tick sigma, (parentBase (K := K) (tick := tick) allocation h : ℝ)

theorem windowFactor_pos (allocation : Allocation) (sigma : Placement) :
    0 < windowFactor (K := K) (tick := tick) allocation sigma := by
  unfold windowFactor
  positivity

theorem parentBase_pos {sigma : Placement} (allocation : Allocation) (h : ActiveOrder K tick sigma) :
    0 < parentBase (K := K) (tick := tick) allocation h :=
  AllFieldHistorySupport.work_source_population_pos allocation (by decide : 0 < (1 : ℕ)) h.val.val

theorem parent_positions_card (allocation : Allocation) (m : ℕ) (sigma : Placement)
    (h : ActiveOrder K tick sigma) :
    Fintype.card (JointPopulation.Positions (Counts (K := K) (tick := tick) allocation m sigma) h) =
      m * parentBase (K := K) (tick := tick) allocation h := by
  change Fintype.card (Fin (∑ u, jointCounts allocation m h.val.val u)) = _
  rw [Fintype.card_fin, jointCounts_sum]
  exact population_dilation allocation m _

theorem positions_card (allocation : Allocation) (m : ℕ) (ε : ℝ) (sigma : Placement)
    (side : Fin 3) (e : Targets (K := K) (tick := tick) allocation m sigma)
    (w : Raw (K := K) (tick := tick) allocation m sigma) (hw : Admissible allocation m ε sigma side e w)
    (c : Class (K := K) (tick := tick) sigma) :
    Fintype.card (Positions (K := K) (tick := tick) allocation m sigma w c) =
      m * baseSize (base (K := K) (tick := tick) allocation sigma side) c := by
  have he : JointPopulationCompatibility.FixedSideTargets (Counts (K := K) (tick := tick) allocation m sigma)
      (sigma side) (ownWord (K := K) (tick := tick) allocation m sigma w) :=
    ⟨e, fun h j => (hw.1.1 h j).symm⟩
  rw [JointPopulationCompatibility.classCounts_size
    (Counts (K := K) (tick := tick) allocation m sigma) (sigma side) (ownWord (K := K) (tick := tick) allocation m sigma w) he c]
  simp only [JointPopulationCompatibility.classCounts, Counts, groupCounts,
    activeCounts_dilation allocation m, base, baseSize, Finset.mul_sum, mul_ite, mul_zero]

theorem parentPair_eq_parentCenter (allocation : Allocation) (sigma : Placement)
    (side : Fin 3) (h : ActiveOrder K tick sigma)
    (a : Statistic h.val × Statistic h.val) :
    parentPair (K := K) (tick := tick) allocation sigma side h a = parentCenter allocation (sigma side) h.val a.1 a.2 := by
  unfold parentPair parentCenter parentBase
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro u _
  by_cases hu : 0 < activeCounts allocation 1 h.val u
  · simp only [supportedHalfLaw, ite_eq_left hu, halfLawAt, Bool.false_eq_true,
      ite_false, ite_true]
    ring
  · have hz := Nat.eq_zero_of_not_pos hu
    simp only [hz, Nat.cast_zero, zero_mul, zero_div]

theorem parentPair_eq_native (allocation : Allocation) (sigma : Placement)
    (side : Fin 3) (h : ActiveOrder K tick sigma)
    (a : Statistic h.val × Statistic h.val) :
    parentPair (K := K) (tick := tick) allocation sigma side h a = orderPairMixture h side a := by
  rw [parentPair_eq_parentCenter]
  unfold parentCenter orderPairMixture
  apply Finset.sum_congr rfl
  intro u _
  rw [show (activeCounts allocation 1 h.val u : ℝ) /
      population allocation 1 (h.val.val.1.source, h.val.val.2) =
      (AllFieldActiveLaws.orderLaw h).mass u from
    AllFieldActiveLaws.jointCounts_ratio allocation (by decide : 0 < (1 : ℕ)) h.val.val u]
  ring

def parentStatistic (allocation : Allocation) (m : ℕ) (sigma : Placement)
    (w : Raw (K := K) (tick := tick) allocation m sigma) (h : ActiveOrder K tick sigma)
    (j : JointPopulation.Positions (Counts (K := K) (tick := tick) allocation m sigma) h) :
    Statistic h.val × Statistic h.val :=
  (statistic h.val (w h j).1, statistic h.val (w h j).2)

theorem parent_window (allocation : Allocation) (m : ℕ) (ε : ℝ) (sigma : Placement)
    (side : Fin 3) (w : Raw (K := K) (tick := tick) allocation m sigma)
    (hw : AllFieldHistoryGroupMasks.rawPass allocation m ε (sigma side) sigma w)
    (h : ActiveOrder K tick sigma) (a : Statistic h.val × Statistic h.val) :
    |(wordPopulation (parentStatistic (K := K) (tick := tick) allocation m sigma w h) a : ℝ) /
      Fintype.card (JointPopulation.Positions (Counts (K := K) (tick := tick) allocation m sigma) h) -
        parentPair (K := K) (tick := tick) allocation sigma side h a| ≤ pairWidth ε h.val := by
  let defaults : SymbolChoice K tick := fun h => statistic h (fun _ => 0)
  let l : SymbolChoice K tick := Function.update defaults h.val a.1
  let r : SymbolChoice K tick := Function.update defaults h.val a.2
  have hp := hw (h.val, l, r) h.property
  rw [center_eq_parentCenter] at hp
  simp only [l, r, Function.update_self] at hp
  rw [parentPair_eq_parentCenter]
  have hpop : Fintype.card (JointPopulation.Positions (Counts (K := K) (tick := tick) allocation m sigma) h) =
      population allocation m (h.val.val.1.source, h.val.val.2) := by
    change Fintype.card (Fin (∑ u, jointCounts allocation m h.val.val u)) = _
    rw [Fintype.card_fin]
    exact jointCounts_sum allocation m h.val.val
  rw [hpop]
  have hcount : (wordPopulation (parentStatistic (K := K) (tick := tick) allocation m sigma w h) a : ℝ) =
      ∑ j : JointPopulation.Positions (activeCounts allocation m) h.val,
        if statistic h.val (w h j).1 = a.1 ∧ statistic h.val (w h j).2 = a.2
          then (1 : ℝ) else 0 := by
    rcases a with ⟨a₁, a₂⟩
    simp only [wordPopulation, Fintype.card_subtype, Finset.card_eq_sum_ones,
      Finset.sum_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero,
      parentStatistic, Prod.mk.injEq]
    apply Finset.sum_congr rfl
    intro j _
    split_ifs <;> rfl
  rw [hcount]
  exact hp

def weightCode {K : ℕ} (w : Work K) : w.Statistic → Fin 17 :=
  match w with
  | .stageA _ => AllFieldPairMarginals.halfWeightCode
  | .stageB _ => AllFieldPairMarginals.statisticWeightCode
  | .stageC _ => fun _ => 0

@[simp] theorem weightCode_val {K : ℕ} (w : Work K) (a : w.Statistic) :
    (weightCode w a).val = w.statisticWeight a := by
  cases w <;> rfl

theorem weightCode_statistic {K : ℕ} (w : Work K) (hs : w.stage ≠ 2)
    (x : CWWindowedLeaves.Raw w.halfLength) :
    (weightCode w (w.statistic x)).val = CWStrands.weight x :=
  (weightCode_val w _).trans (w.statistic_weight hs x).symm

theorem left_supported_zero (allocation : Allocation) (sigma : Placement) (side : Fin 3)
    (h : ActiveOrder K tick sigma) (hs : h.val.val.1.stage ≠ 2)
    (u : JointPopulation.Shape) (a : Statistic h.val)
    (ha : weightCode h.val.val.1 a ≠ JointPopulation.shapeSide (sigma side) u) :
    supportedHalfLaw allocation false h.val u (sigma side) a = 0 := by
  by_cases hu : 0 < activeCounts allocation 1 h.val u
  · rw [supportedHalfLaw_eq_of_counts_pos allocation 1 false h.val u hu, halfLawAt_eq]
    apply Rat.cast_eq_zero.mpr
    apply h.val.val.1.childLaw_outside_support hs _
      (halfShape_mem_of_counts_pos allocation 1 false h.val u hu) _ a
    rw [halfShape_childWeight]
    simpa only [childWeight, Bool.false_eq_true, ite_false, ← weightCode_val,
      ne_eq, Fin.ext_iff] using ha
  · simp only [supportedHalfLaw, ite_eq_right hu]

theorem filtered_pair_sum (allocation : Allocation) (sigma : Placement) (side : Fin 3)
    (c : Class (K := K) (tick := tick) sigma) (hs : c.1.val.val.1.stage ≠ 2)
    (a : Symbol (K := K) (tick := tick) sigma c × Symbol (K := K) (tick := tick) sigma c) :
    (∑ u, (base (K := K) (tick := tick) allocation sigma side c u : ℝ) *
      supportedHalfLaw allocation false c.1.val u (sigma side) a.1 *
      supportedHalfLaw allocation true c.1.val u (sigma side) a.2) =
      if weightCode c.1.val.val.1 a.1 = c.2 then
        ∑ u, (activeCounts allocation 1 c.1.val u : ℝ) *
          supportedHalfLaw allocation false c.1.val u (sigma side) a.1 *
          supportedHalfLaw allocation true c.1.val u (sigma side) a.2
      else 0 := by
  have hterm (u : JointPopulation.Shape) :
      (base (K := K) (tick := tick) allocation sigma side c u : ℝ) *
        supportedHalfLaw allocation false c.1.val u (sigma side) a.1 *
        supportedHalfLaw allocation true c.1.val u (sigma side) a.2 =
      if weightCode c.1.val.val.1 a.1 = c.2 then
        (activeCounts allocation 1 c.1.val u : ℝ) *
          supportedHalfLaw allocation false c.1.val u (sigma side) a.1 *
          supportedHalfLaw allocation true c.1.val u (sigma side) a.2
      else 0 := by
    by_cases hu : JointPopulation.shapeSide (sigma side) u = c.2
    · simp only [base, JointPopulationCompatibility.classCounts, Counts, groupCounts,
        hu, ite_true]
      by_cases ha : weightCode c.1.val.val.1 a.1 = c.2
      · rw [ite_eq_left ha]
      · have hz := left_supported_zero (K := K) (tick := tick) allocation sigma side c.1 hs u a.1
          (fun he => ha (he.trans hu))
        simp only [ha, ite_false, hz, mul_zero, zero_mul]
    · simp only [base, JointPopulationCompatibility.classCounts, Counts, groupCounts,
        hu, ite_false, Nat.cast_zero, zero_mul]
      by_cases ha : weightCode c.1.val.val.1 a.1 = c.2
      · have hz := left_supported_zero (K := K) (tick := tick) allocation sigma side c.1 hs u a.1
          (fun he => hu (he.symm.trans ha))
        simp only [ha, ite_true, hz, mul_zero, zero_mul]
      · rw [ite_eq_right ha]
  simp_rw [hterm]
  split_ifs <;> simp

theorem q_eq_conditionalCenter (allocation : Allocation) (sigma : Placement) (side : Fin 3)
    (c : Class (K := K) (tick := tick) sigma) (hs : c.1.val.val.1.stage ≠ 2) :
    q (K := K) (tick := tick) allocation sigma side c = JointPairClassWindows.conditionalCenter
      (fun a : Symbol (K := K) (tick := tick) sigma c × Symbol (K := K) (tick := tick) sigma c => weightCode c.1.val.val.1 a.1)
      c.2 (parentPair (K := K) (tick := tick) allocation sigma side c.1) (classMass (K := K) (tick := tick) allocation sigma side c) := by
  funext a
  rw [q, JointPairMixtureControls.pairMixture, filtered_pair_sum (K := K) (tick := tick) allocation sigma side c hs]
  unfold JointPairClassWindows.conditionalCenter parentPair classMass
  by_cases ha : weightCode c.1.val.val.1 a.1 = c.2
  · simp only [ha, ite_true]
    have hp : (parentBase (K := K) (tick := tick) allocation c.1 : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.ne_of_gt (parentBase_pos (K := K) (tick := tick) allocation c.1))
    rw [div_div_div_cancel_right₀ hp]
  · simp only [ha, ite_false, zero_div]

theorem classMass_pos (allocation : Allocation) (sigma : Placement) (side : Fin 3)
    (c : Class (K := K) (tick := tick) sigma)
    (hc : 0 < baseSize (base (K := K) (tick := tick) allocation sigma side) c) :
    0 < classMass (K := K) (tick := tick) allocation sigma side c :=
  div_pos (Nat.cast_pos.mpr hc) (Nat.cast_pos.mpr (parentBase_pos (K := K) (tick := tick) allocation c.1))

theorem fiber_mass (allocation : Allocation) (m : ℕ) (ε : ℝ) (sigma : Placement)
    (side : Fin 3) (e : Targets (K := K) (tick := tick) allocation m sigma)
    (w : Raw (K := K) (tick := tick) allocation m sigma) (hw : Admissible allocation m ε sigma side e w)
    (c : Class (K := K) (tick := tick) sigma) :
    (Fintype.card (Positions (K := K) (tick := tick) allocation m sigma w c) : ℝ) =
      (Fintype.card (JointPopulation.Positions (Counts (K := K) (tick := tick) allocation m sigma) c.1) : ℝ) *
        classMass (K := K) (tick := tick) allocation sigma side c := by
  rw [positions_card (K := K) (tick := tick) allocation m ε sigma side e w hw, parent_positions_card]
  simp only [Nat.cast_mul, classMass]
  have hp : (parentBase (K := K) (tick := tick) allocation c.1 : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt (parentBase_pos (K := K) (tick := tick) allocation c.1))
  rw [mul_assoc, mul_div_cancel₀ _ hp]

theorem width_le (allocation : Allocation) {ε : ℝ} (hε : 0 ≤ ε)
    (sigma : Placement) (side : Fin 3) (c : Class (K := K) (tick := tick) sigma)
    (hc : 0 < baseSize (base (K := K) (tick := tick) allocation sigma side) c) :
    pairWidth ε c.1.val / classMass (K := K) (tick := tick) allocation sigma side c ≤
      windowFactor (K := K) (tick := tick) allocation sigma * ε := by
  have hpw : 0 ≤ pairWidth ε c.1.val := by unfold pairWidth; positivity
  have hw : pairWidth ε c.1.val ≤ ε :=
    div_le_self hε (one_le_pow₀ (by norm_num))
  have hb : (1 : ℝ) ≤ baseSize (base (K := K) (tick := tick) allocation sigma side) c := by exact_mod_cast hc
  have hn : (parentBase (K := K) (tick := tick) allocation c.1 : ℝ) ≤ windowFactor (K := K) (tick := tick) allocation sigma := by
    unfold windowFactor
    exact (Finset.single_le_sum (fun _ _ => Nat.cast_nonneg _) (Finset.mem_univ c.1)).trans
      (le_add_of_nonneg_left zero_le_one)
  unfold classMass
  rw [div_div_eq_mul_div]
  calc
    pairWidth ε c.1.val * (parentBase (K := K) (tick := tick) allocation c.1 : ℝ) /
        (baseSize (base (K := K) (tick := tick) allocation sigma side) c : ℝ) ≤
        pairWidth ε c.1.val * (parentBase (K := K) (tick := tick) allocation c.1 : ℝ) :=
      div_le_self (mul_nonneg hpw (Nat.cast_nonneg _)) hb
    _ ≤ ε * windowFactor (K := K) (tick := tick) allocation sigma := mul_le_mul hw hn (Nat.cast_nonneg _) hε
    _ = _ := mul_comm _ _

theorem sharing_window (allocation : Allocation) (m : ℕ) {ε : ℝ} (hε : 0 ≤ ε)
    (sigma : Placement) (side : Fin 3)
    (e : Targets (K := K) (tick := tick) allocation m sigma)
    (w : Raw (K := K) (tick := tick) allocation m sigma) (hw : Admissible allocation m ε sigma side e w)
    (hp : AllFieldHistoryGroupMasks.rawPass allocation m ε (sigma side) sigma w)
    (c : Class (K := K) (tick := tick) sigma) (hs : c.1.val.val.1.stage ≠ 2)
    (hc : 0 < baseSize (base (K := K) (tick := tick) allocation sigma side) c)
    (a : Symbol (K := K) (tick := tick) sigma c × Symbol (K := K) (tick := tick) sigma c) :
    |(pairCounts (K := K) (tick := tick) allocation m sigma w c a : ℝ) /
        Fintype.card (Positions (K := K) (tick := tick) allocation m sigma w c) - q (K := K) (tick := tick) allocation sigma side c a| ≤
      windowFactor (K := K) (tick := tick) allocation sigma * ε := by
  let z := parentStatistic (K := K) (tick := tick) allocation m sigma w c.1
  let k : JointPopulation.Positions (Counts (K := K) (tick := tick) allocation m sigma) c.1 → Fin 17 :=
    fun j => ownWord (K := K) (tick := tick) allocation m sigma w ⟨c.1, j⟩
  let f : Symbol (K := K) (tick := tick) sigma c × Symbol (K := K) (tick := tick) sigma c → Fin 17 :=
    fun a => weightCode c.1.val.val.1 a.1
  have hf (j) : f (z j) = k j := by
    apply Fin.ext
    exact weightCode_statistic c.1.val.val.1 hs (w c.1 j).1
  have hη : 0 ≤ pairWidth ε c.1.val := by unfold pairWidth; positivity
  have hh := JointPairClassWindows.fiber_window z k f hf c.2
    (parentPair (K := K) (tick := tick) allocation sigma side c.1) (classMass (K := K) (tick := tick) allocation sigma side c)
    (pairWidth ε c.1.val) (classMass_pos (K := K) (tick := tick) allocation sigma side c hc) hη
    (fiber_mass (K := K) (tick := tick) allocation m ε sigma side e w hw c)
    (parent_window (K := K) (tick := tick) allocation m ε sigma side w hp c.1) a
  rw [← q_eq_conditionalCenter (K := K) (tick := tick) allocation sigma side c hs] at hh
  exact hh.trans (width_le (K := K) (tick := tick) allocation hε sigma side c hc)

theorem q_eq_one_of_subsingleton (allocation : Allocation) (sigma : Placement) (side : Fin 3)
    (c : Class (K := K) (tick := tick) sigma) [Subsingleton (Symbol (K := K) (tick := tick) sigma c)]
    (hc : 0 < baseSize (base (K := K) (tick := tick) allocation sigma side) c)
    (a : Symbol (K := K) (tick := tick) sigma c × Symbol (K := K) (tick := tick) sigma c) : q (K := K) (tick := tick) allocation sigma side c a = 1 := by
  have hl (right : Bool) (u : JointPopulation.Shape)
      (hu : 0 < base (K := K) (tick := tick) allocation sigma side c u) :
      supportedHalfLaw allocation right c.1.val u (sigma side) (if right then a.2 else a.1) = 1 := by
    have hu' : 0 < activeCounts allocation 1 c.1.val u := by
      unfold base JointPopulationCompatibility.classCounts Counts groupCounts at hu
      split_ifs at hu with he
      · exact hu
      · omega
    rw [supportedHalfLaw_eq_of_counts_pos allocation 1 right c.1.val u hu']
    have ht := halfLawAt_normalized allocation 1 right c.1.val u hu' (sigma side)
    have he : (∑ b, halfLawAt right c.1.val u (sigma side) b) =
        halfLawAt right c.1.val u (sigma side) (if right then a.2 else a.1) :=
      Fintype.sum_subsingleton _ _
    exact he.symm.trans ht
  unfold q JointPairMixtureControls.pairMixture
  have hn : (∑ u, (base (K := K) (tick := tick) allocation sigma side c u : ℝ) *
      supportedHalfLaw allocation false c.1.val u (sigma side) a.1 *
      supportedHalfLaw allocation true c.1.val u (sigma side) a.2) =
      (baseSize (base (K := K) (tick := tick) allocation sigma side) c : ℝ) := by
    rw [baseSize, Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro u _
    by_cases hu : 0 < base (K := K) (tick := tick) allocation sigma side c u
    · have hleft : supportedHalfLaw allocation false c.1.val u (sigma side) a.1 = 1 := by
        simpa only [Bool.false_eq_true, ite_false] using hl false u hu
      have hright : supportedHalfLaw allocation true c.1.val u (sigma side) a.2 = 1 := by
        simpa only [ite_true] using hl true u hu
      rw [hleft, hright, mul_one, mul_one]
    · simp only [Nat.eq_zero_of_not_pos hu, Nat.cast_zero, zero_mul]
  rw [hn]
  exact div_self (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hc))

theorem pairWindow_of_completeKeep (allocation : Allocation) {m : ℕ} (hm : 0 < m)
    {ε : ℝ} (hε : 0 ≤ ε) (sigma : Placement) (side : Fin 3)
    (e : Targets (K := K) (tick := tick) allocation m sigma)
    (w : Raw (K := K) (tick := tick) allocation m sigma) (hw : Admissible allocation m ε sigma side e w)
    (hp : completeKeep allocation m ε (sigma side) sigma w) :
    PairWindow (base (K := K) (tick := tick) allocation sigma side) (q (K := K) (tick := tick) allocation sigma side)
      (Positions (K := K) (tick := tick) allocation m sigma w) (pairCounts (K := K) (tick := tick) allocation m sigma w)
      (windowFactor (K := K) (tick := tick) allocation sigma * ε) := by
  intro c hc a
  by_cases hs : c.1.val.val.1.stage ≠ 2
  · exact sharing_window (K := K) (tick := tick) allocation m hε sigma side e w hw hp.2.2 c hs hc a
  · have hstage : c.1.val.val.1.stage = 2 := not_ne_iff.mp hs
    have : Subsingleton (Symbol (K := K) (tick := tick) sigma c) := by
      change Subsingleton c.1.val.val.1.Statistic
      cases hh : c.1.val.val.1 with
      | stageA h => simp [hh, Work.stage] at hstage
      | stageB h => simp [hh, Work.stage] at hstage
      | stageC h => dsimp [Work.Statistic]; infer_instance
    have hpc : pairCounts (K := K) (tick := tick) allocation m sigma w c a =
        Fintype.card (Positions (K := K) (tick := tick) allocation m sigma w c) := by
      unfold pairCounts JointPopulationCompatibility.statisticCounts
      have hall : ∀ i, JointPopulationCompatibility.statisticWord
          (Counts (K := K) (tick := tick) allocation m sigma) (Letter (K := K) (tick := tick) sigma) (Letter (K := K) (tick := tick) sigma) (Symbol (K := K) (tick := tick) sigma) (Symbol (K := K) (tick := tick) sigma)
          (projectedStatistic (K := K) (tick := tick) sigma) (projectedStatistic (K := K) (tick := tick) sigma)
          (ownWord (K := K) (tick := tick) allocation m sigma w) w c i = a := fun _ => Subsingleton.elim _ _
      simp [wordPopulation, hall]
    have hn : (Fintype.card (Positions (K := K) (tick := tick) allocation m sigma w c) : ℝ) ≠ 0 := by
      rw [positions_card (K := K) (tick := tick) allocation m ε sigma side e w hw c]
      exact Nat.cast_ne_zero.mpr (Nat.ne_of_gt (Nat.mul_pos hm hc))
    rw [hpc, div_self hn, q_eq_one_of_subsingleton (K := K) (tick := tick) allocation sigma side c hc a,
      sub_self, abs_zero]
    exact mul_nonneg (windowFactor_pos (K := K) (tick := tick) allocation sigma).le hε

theorem passing_pairWindow (allocation : Allocation) {m : ℕ} (hm : 0 < m)
    {ε : ℝ} (hε : 0 ≤ ε) (sigma : Placement)
    (e : Targets (K := K) (tick := tick) allocation m sigma)
    (o : Orbit (K := K) (tick := tick) allocation m sigma) (ho : o ∈ (data (K := K) (tick := tick) allocation m ε sigma).orbits e)
    (v : Variable (K := K) (tick := tick) allocation m sigma) (hv : v ∈ (data (K := K) (tick := tick) allocation m ε sigma).passing e o) :
    PairWindow (base (K := K) (tick := tick) allocation sigma v.1) (q (K := K) (tick := tick) allocation sigma v.1)
      (Positions (K := K) (tick := tick) allocation m sigma v.2) (pairCounts (K := K) (tick := tick) allocation m sigma v.2)
      (windowFactor (K := K) (tick := tick) allocation sigma * ε) := by
  have hpass := (mem_passing allocation m ε sigma e o v).mp hv
  exact pairWindow_of_completeKeep (K := K) (tick := tick) allocation hm hε sigma v.1 e v.2
    (AllFieldGroupAdmissible.full_admissible allocation m ε sigma e o ho v hpass.1) hpass.2

end MatrixMultiplication.AllFieldGroupPairWindows

end

end OAI
