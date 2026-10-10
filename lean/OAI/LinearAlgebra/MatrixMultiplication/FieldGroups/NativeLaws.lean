import OAI.LinearAlgebra.MatrixMultiplication.FieldGroups.OrbitData
import OAI.LinearAlgebra.MatrixMultiplication.FieldConstruction.ActiveLaws
import OAI.LinearAlgebra.MatrixMultiplication.FieldConstruction.PairConditionalEntropy
import OAI.LinearAlgebra.MatrixMultiplication.FieldParameters.HalfComplement
import OAI.LinearAlgebra.MatrixMultiplication.JointExtraction.EntropyMax

namespace OAI

/-! Group assignments, orbit counts and extraction capacities. -/

noncomputable section

namespace MatrixMultiplication.AllFieldGroupNativeLaws

open MatrixMultiplication.Foundation AllFieldParameters AllFieldHistory
open AllFieldHistoryChildLaws AllFieldGroupOrbitData AllFieldActiveLaws
open AllFieldNativeCapacity AllFieldPairMarginals AllFieldPairConditionalEntropy
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq

def statisticComplement {K : ℕ} (w : Work K) : w.Statistic ≃ w.Statistic :=
  match w with
  | .stageA _ => CWCompleteStatistics.orderedComplementStatistic
  | .stageB _ => CWCompleteStatistics.complementStatistic
  | .stageC _ => Equiv.refl _

theorem childLaw_complementary_sides {K : ℕ} (w : Work K)
    (u : Shape) (hu : u ∈ shapes (2 * w.halfLength))
    (source target : Fin 3) (hne : source ≠ target)
    (hsum : u source + u target = 2 * w.halfLength) (a : w.Statistic) :
    w.childLaw u source ((statisticComplement w).symm a) = w.childLaw u target a := by
  cases w with
  | stageA h => exact halfLaw_complementary_sides u hu source target hne hsum a
  | stageB h =>
      exact littleLaw_complement (aShape h.val) u source target
        (lt_of_le_of_lt (mem_shapes_bound hu source) (by norm_num [Work.halfLength]))
        (lt_of_le_of_lt (mem_shapes_bound hu target) (by norm_num [Work.halfLength]))
        hsum a
  | stageC h => rfl

def halfLawAt {K tick : ℕ} (right : Bool) (h : Active K tick)
    (u : JointPopulation.Shape) (side : Fin 3) : Statistic h → ℝ :=
  if right then rightLaw h u side else leftLaw h u side

def childWeight {K tick : ℕ} (right : Bool) (h : Active K tick)
    (u : JointPopulation.Shape) (side : Fin 3) : ℕ :=
  if right then activeParentShape h side - (JointPopulation.shapeSide side u).val
  else (JointPopulation.shapeSide side u).val

theorem halfLawAt_eq {K tick : ℕ} (right : Bool) (h : Active K tick)
    (u : JointPopulation.Shape) (side : Fin 3) (a : Statistic h) :
    halfLawAt right h u side a =
      (h.val.1.childLaw
        (halfShape h.val.1.parentShape (canonicalChildShape h.val u) right)
        (h.val.2.symm side) a : ℝ) := by
  cases right <;> rfl

theorem halfLawAt_nonnegative {K tick : ℕ} (right : Bool) (h : Active K tick)
    (u : JointPopulation.Shape) (side : Fin 3) (a : Statistic h) :
    0 ≤ halfLawAt right h u side a := by
  cases right
  · exact leftLaw_nonnegative h u side a
  · exact rightLaw_nonnegative h u side a

theorem halfLawAt_normalized {K tick : ℕ} (allocation : Allocation) (m : ℕ)
    (right : Bool) (h : Active K tick) (u : JointPopulation.Shape)
    (hu : 0 < activeCounts allocation m h u) (side : Fin 3) :
    ∑ a, halfLawAt right h u side a = 1 := by
  cases right
  · exact leftLaw_normalized allocation m h u hu side
  · exact rightLaw_normalized allocation m h u hu side

theorem halfLawAt_le_one_of_counts_pos {K tick : ℕ} (allocation : Allocation) (m : ℕ)
    (right : Bool) (h : Active K tick) (u : JointPopulation.Shape)
    (hu : 0 < activeCounts allocation m h u) (side : Fin 3) (a : Statistic h) :
    halfLawAt right h u side a ≤ 1 := by
  have hle := Finset.single_le_sum
    (fun b (_ : b ∈ Finset.univ) => halfLawAt_nonnegative right h u side b)
    (Finset.mem_univ a)
  rw [halfLawAt_normalized allocation m right h u hu side] at hle
  exact hle

def supportedHalfLaw {K tick : ℕ} (allocation : Allocation) (right : Bool)
    (h : Active K tick) (u : JointPopulation.Shape) (side : Fin 3) : Statistic h → ℝ :=
  if 0 < activeCounts allocation 1 h u then halfLawAt right h u side else fun _ => 0

theorem supportedHalfLaw_bounds {K tick : ℕ} (allocation : Allocation) (right : Bool)
    (h : Active K tick) (u : JointPopulation.Shape) (side : Fin 3) (a : Statistic h) :
    0 ≤ supportedHalfLaw allocation right h u side a ∧
      supportedHalfLaw allocation right h u side a ≤ 1 := by
  unfold supportedHalfLaw
  split_ifs with hu
  · exact ⟨halfLawAt_nonnegative right h u side a,
      halfLawAt_le_one_of_counts_pos allocation 1 right h u hu side a⟩
  · norm_num

theorem supportedHalfLaw_eq_of_counts_pos {K tick : ℕ} (allocation : Allocation)
    (m : ℕ) (right : Bool) (h : Active K tick) (u : JointPopulation.Shape)
    (hu : 0 < activeCounts allocation m h u) (side : Fin 3) :
    supportedHalfLaw allocation right h u side = halfLawAt right h u side := by
  have hbase : 0 < activeCounts allocation 1 h u := by
    rw [AllFieldHistorySupport.activeCounts_dilation] at hu
    exact Nat.pos_of_mul_pos_left hu
  simp only [supportedHalfLaw, ite_eq_left hbase]

theorem placedLaw_mass_zero_of_count_zero {K : ℕ} (allocation : Allocation)
    (w : PlacedWork K) (u : JointPopulation.Shape)
    (hu : jointCounts allocation 1 w u = 0) : (placedLaw w).mass u = 0 := by
  have hp : (population allocation 1 (w.1.source, w.2) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt
      (AllFieldHistory.work_source_population_pos allocation (by decide : 0 < (1 : ℕ)) w)
  have he := jointCounts_cast allocation 1 w u
  rw [hu, Nat.cast_zero] at he
  exact (mul_eq_zero.mp he.symm).resolve_left hp

theorem halfShape_childWeight {K tick : ℕ} (right : Bool) (h : Active K tick)
    (u : JointPopulation.Shape) (side : Fin 3) :
    (halfShape h.val.1.parentShape (canonicalChildShape h.val u) right)
      (h.val.2.symm side) = childWeight right h u side := by
  cases right <;>
    simp [halfShape, canonicalChildShape, childWeight, activeParentShape,
      physicalShape, decodeShape, AllFieldParameters.complement]

theorem halfShape_mem_of_counts_pos {K tick : ℕ} (allocation : Allocation) (m : ℕ)
    (right : Bool) (h : Active K tick) (u : JointPopulation.Shape)
    (hu : 0 < activeCounts allocation m h u) :
    halfShape h.val.1.parentShape (canonicalChildShape h.val u) right ∈
      shapes (2 * h.val.1.halfLength) := by
  obtain ⟨b, rfl, _⟩ := shapeCounts_positive _ _ u hu
  rw [canonicalChildShape_branchShape]
  exact h.val.1.halfShape_mem b right

theorem childWeight_sum {K tick : ℕ} (allocation : Allocation) (m : ℕ)
    (right : Bool) (h : Active K tick) (u : JointPopulation.Shape)
    (hu : 0 < activeCounts allocation m h u) (sigma : Placement) :
    childWeight right h u (sigma 0) + childWeight right h u (sigma 1) +
      childWeight right h u (sigma 2) = 2 * h.val.1.halfLength := by
  let v := halfShape h.val.1.parentShape (canonicalChildShape h.val u) right
  have ht := mem_shapes_total (halfShape_mem_of_counts_pos allocation m right h u hu)
  have hp := Equiv.sum_comp (sigma.trans h.val.2.symm) v
  have he : (∑ i : Fin 3, v (h.val.2.symm (sigma i))) = 2 * h.val.1.halfLength := by
    calc
      _ = ∑ i : Fin 3, v i := hp
      _ = _ := by simpa [v, shapeTotal, Fin.sum_univ_succ, Nat.add_assoc] using ht
  simpa [v, halfShape_childWeight, Fin.sum_univ_succ, Nat.add_assoc] using he

theorem designated_source_geometry (weight : Fin 3 → ℕ) (total : ℕ)
    (htotal : weight 0 + weight 1 + weight 2 = total) (side : Fin 3)
    (hd : if side = 1 then weight 2 = 0
      else if side = 2 then weight 0 * weight 1 = 0 else False) :
    let source : Fin 3 := if side = 2 ∧ weight 1 ≠ 0 then 1 else 0
    source ≠ side ∧ weight source + weight side = total := by
  fin_cases side
  · simp at hd
  · simp at hd ⊢
    omega
  · by_cases hzero : weight 1 = 0
    · simp [hzero] at hd ⊢
      omega
    · have hz : weight 0 = 0 := by simpa [hzero] using hd
      simp [hzero]
      omega

theorem compatibilityLaw_eq {K tick : ℕ} (allocation : Allocation) (m : ℕ)
    (sigma : Placement) (right : Bool) (side : Fin 3)
    (h : ActiveOrder K tick sigma) (u : JointPopulation.Shape)
    (hu : 0 < Counts allocation m sigma h u)
    (hd : designated right side sigma h u) :
    compatibilityLaw right side sigma h u =
      if right then rightLaw h.val u (sigma side) else leftLaw h.val u (sigma side) := by
  let weight : Fin 3 → ℕ := fun i => childWeight right h.val u (sigma i)
  let source : Fin 3 := if side = 2 ∧ weight 1 ≠ 0 then 1 else 0
  have hdesignated : if side = 1 then weight 2 = 0
      else if side = 2 then weight 0 * weight 1 = 0 else False := by
    simpa only [AllFieldGroupOrbitData.designated, weight, childWeight] using hd.2
  have hgeom := designated_source_geometry weight (2 * h.val.val.1.halfLength)
    (childWeight_sum allocation m right h.val u hu sigma) side hdesignated
  have hsource : (if side = 2 ∧ weight 1 ≠ 0 then sigma 1 else sigma 0) = sigma source := by
    dsimp only [source]
    split_ifs <;> rfl
  have hne : h.val.val.2.symm (sigma source) ≠ h.val.val.2.symm (sigma side) := by
    intro heq
    exact hgeom.1 (sigma.injective (h.val.val.2.symm.injective heq))
  have hsum :
      (halfShape h.val.val.1.parentShape (canonicalChildShape h.val.val u) right)
          (h.val.val.2.symm (sigma source)) +
        (halfShape h.val.val.1.parentShape (canonicalChildShape h.val.val u) right)
          (h.val.val.2.symm (sigma side)) = 2 * h.val.val.1.halfLength := by
    simpa only [halfShape_childWeight] using hgeom.2
  funext a
  have hlaw := childLaw_complementary_sides h.val.val.1
    (halfShape h.val.val.1.parentShape (canonicalChildShape h.val.val u) right)
    (halfShape_mem_of_counts_pos allocation m right h.val u hu)
    (h.val.val.2.symm (sigma source)) (h.val.val.2.symm (sigma side)) hne hsum a
  have hre : halfLawAt right h.val u (sigma source)
      ((statisticComplement h.val.val.1).symm a) =
        halfLawAt right h.val u (sigma side) a := by
    rw [halfLawAt_eq, halfLawAt_eq]
    exact_mod_cast hlaw
  change ((if right then rightLaw h.val u
      (if side = 2 ∧ weight 1 ≠ 0 then sigma 1 else sigma 0)
    else leftLaw h.val u
      (if side = 2 ∧ weight 1 ≠ 0 then sigma 1 else sigma 0))
      ((statisticComplement h.val.val.1).symm a)) = _
  rw [hsource]
  exact hre

def nativePairLaw {K : ℕ} (w : Work K) (side : Fin 3) :
    FiniteLaw (w.Statistic × w.Statistic) :=
  match w with
  | .stageA h => stageAPairLaw (initialShape h.val) h.property side
  | .stageB h => stageBPairLaw (aShape h.val) h.property side
  | .stageC _ =>
      { mass := fun _ => 1
        nonneg := fun _ => zero_le_one
        total := Fintype.sum_subsingleton (fun _ : PUnit × PUnit => (1 : ℝ))
          (PUnit.unit, PUnit.unit) }

theorem placedLaw_sum_mul {K : ℕ} (w : PlacedWork K)
    (f : JointPopulation.Shape → ℝ) :
    (∑ u, (placedLaw w).mass u * f u) =
      ∑ b : w.1.Branch, (branchLaw w.1).mass b * f (branchShape w b) := by
  exact (JointEntropyMax.sum_mass_mul_coordinate
    (branchLaw w.1) (branchShape w) f).symm

theorem childLaw_branchShape {K : ℕ} (w : PlacedWork K)
    (b : w.1.Branch) (side : Fin 3) (a : w.1.Statistic) :
    childLaw w (branchShape w b) side a =
      (w.1.childLaw (w.1.splitShape b) (w.2.symm side) a : ℝ) := by
  change (w.1.childLaw (canonicalChildShape w (branchShape w b))
    (w.2.symm side) a : ℝ) = _
  rw [canonicalChildShape_branchShape]

theorem rightChildLaw_branchShape {K : ℕ} (w : PlacedWork K)
    (b : w.1.Branch) (side : Fin 3) (a : w.1.Statistic) :
    rightChildLaw w (branchShape w b) side a =
      (w.1.childLaw (AllFieldParameters.complement w.1.parentShape (w.1.splitShape b))
        (w.2.symm side) a : ℝ) := by
  change (w.1.childLaw
    (AllFieldParameters.complement w.1.parentShape (canonicalChildShape w (branchShape w b)))
    (w.2.symm side) a : ℝ) = _
  rw [canonicalChildShape_branchShape]

theorem branchPairMixture_eq_native {K : ℕ} (w : Work K) (side : Fin 3)
    (a : w.Statistic × w.Statistic) :
    (∑ b : w.Branch, (branchLaw w).mass b *
      (w.childLaw (w.splitShape b) side a.1 : ℝ) *
      (w.childLaw (AllFieldParameters.complement w.parentShape (w.splitShape b)) side a.2 : ℝ)) =
      (nativePairLaw w side).mass a := by
  cases w with
  | stageA h =>
      change (∑ b : Fin (below (initialShape h.val)).length,
        (stageALaw (initialShape h.val) (below (initialShape h.val))[b.val] : ℝ) *
          (halfLaw (below (initialShape h.val))[b.val] side a.1 : ℝ) *
          (halfLaw (AllFieldParameters.complement (initialShape h.val)
            (below (initialShape h.val))[b.val]) side a.2 : ℝ)) = _
      exact Fin.sum_univ_fun_getElem _ (fun u : Shape =>
        (stageALaw (initialShape h.val) u : ℝ) * (halfLaw u side a.1 : ℝ) *
          (halfLaw (AllFieldParameters.complement (initialShape h.val) u) side a.2 : ℝ))
  | stageB h =>
      change (∑ b : Fin (below (aShape h.val)).length,
        (stageBLaw (aShape h.val) (below (aShape h.val))[b.val] : ℝ) *
          (littleLaw (aShape h.val) (below (aShape h.val))[b.val] side a.1 : ℝ) *
          (littleLaw (aShape h.val) (AllFieldParameters.complement (aShape h.val)
            (below (aShape h.val))[b.val]) side a.2 : ℝ)) = _
      exact Fin.sum_univ_fun_getElem _ (fun u : Shape =>
        (stageBLaw (aShape h.val) u : ℝ) *
          (littleLaw (aShape h.val) u side a.1 : ℝ) *
          (littleLaw (aShape h.val) (AllFieldParameters.complement (aShape h.val) u) side a.2 : ℝ))
  | stageC h =>
      simpa only [Work.childLaw, Rat.cast_one, mul_one, nativePairLaw] using
        (branchLaw (Work.stageC h)).total

def placedPairMixture {K : ℕ} (w : PlacedWork K) (side : Fin 3)
    (a : w.1.Statistic × w.1.Statistic) : ℝ :=
  ∑ u, (placedLaw w).mass u * childLaw w u side a.1 * rightChildLaw w u side a.2

theorem placedPairMixture_eq_native {K : ℕ} (w : PlacedWork K) (side : Fin 3)
    (a : w.1.Statistic × w.1.Statistic) :
    placedPairMixture w side a = (nativePairLaw w.1 (w.2.symm side)).mass a := by
  simp only [placedPairMixture, mul_assoc]
  rw [placedLaw_sum_mul]
  simpa only [childLaw_branchShape, rightChildLaw_branchShape, mul_assoc] using
    branchPairMixture_eq_native w.1 (w.2.symm side) a

theorem placement_symm_order_side {K tick : ℕ} {sigma : Placement}
    (h : ActiveOrder K tick sigma) (side : Fin 3) :
    h.val.val.2.symm (sigma side) = h.val.val.1.priority side := by
  have hs : h.val.val.2 (h.val.val.1.priority side) = sigma side :=
    Equiv.congr_fun h.property side
  rw [← hs, Equiv.symm_apply_apply]

def orderPairMixture {K tick : ℕ} {sigma : Placement}
    (h : ActiveOrder K tick sigma) (side : Fin 3)
    (a : Statistic h.val × Statistic h.val) : ℝ :=
  ∑ u, (orderLaw h).mass u * leftLaw h.val u (sigma side) a.1 *
    rightLaw h.val u (sigma side) a.2

theorem orderPairMixture_eq_native {K tick : ℕ} {sigma : Placement}
    (h : ActiveOrder K tick sigma) (side : Fin 3)
    (a : Statistic h.val × Statistic h.val) :
    orderPairMixture h side a =
      (nativePairLaw h.val.val.1 (h.val.val.1.priority side)).mass a := by
  change placedPairMixture h.val.val (sigma side) a = _
  rw [placedPairMixture_eq_native, placement_symm_order_side]

theorem orderPairMixture_supported {K tick : ℕ} {sigma : Placement}
    (allocation : Allocation) (h : ActiveOrder K tick sigma) (side : Fin 3)
    (a : Statistic h.val × Statistic h.val) :
    (∑ u, (orderLaw h).mass u *
      supportedHalfLaw allocation false h.val u (sigma side) a.1 *
      supportedHalfLaw allocation true h.val u (sigma side) a.2) =
        (nativePairLaw h.val.val.1 (h.val.val.1.priority side)).mass a := by
  rw [← orderPairMixture_eq_native]
  unfold orderPairMixture
  apply Finset.sum_congr rfl
  intro u _
  by_cases hu : 0 < activeCounts allocation 1 h.val u
  · simp [supportedHalfLaw, hu, halfLawAt]
  · have hz : (orderLaw h).mass u = 0 :=
      placedLaw_mass_zero_of_count_zero allocation h.val.val u (Nat.eq_zero_of_not_pos hu)
    simp only [hz, zero_mul]

theorem orderPairMixture_nonneg {K tick : ℕ} {sigma : Placement}
    (h : ActiveOrder K tick sigma) (side : Fin 3)
    (a : Statistic h.val × Statistic h.val) : 0 ≤ orderPairMixture h side a := by
  rw [orderPairMixture_eq_native]
  exact (nativePairLaw h.val.val.1 (h.val.val.1.priority side)).nonneg a

theorem orderPairMixture_total {K tick : ℕ} {sigma : Placement}
    (h : ActiveOrder K tick sigma) (side : Fin 3) :
    ∑ a, orderPairMixture h side a = 1 := by
  simp_rw [orderPairMixture_eq_native]
  exact (nativePairLaw h.val.val.1 (h.val.val.1.priority side)).total

theorem orderPairMixture_entropy {K tick : ℕ} {sigma : Placement}
    (h : ActiveOrder K tick sigma) (side : Fin 3) :
    finiteEntropy (orderPairMixture h side) =
      finiteEntropy (nativePairLaw h.val.val.1 (h.val.val.1.priority side)).mass := by
  have hm : orderPairMixture h side =
      (nativePairLaw h.val.val.1 (h.val.val.1.priority side)).mass :=
    funext (orderPairMixture_eq_native h side)
  rw [hm]

def nativeStatisticWeightCode {K : ℕ} (w : Work K) : w.Statistic → Fin 17 :=
  match w with
  | .stageA _ => halfWeightCode
  | .stageB _ => statisticWeightCode
  | .stageC _ => fun _ => 0

def nativeSplitWeightCode {K : ℕ} (w : Work K) (side : Fin 3)
    (b : w.Branch) : Fin 17 :=
  ⟨w.splitShape b side, Nat.lt_succ_of_le ((w.splitShape_spec b).1 side)⟩

@[simp] theorem nativeSplitWeightCode_val {K : ℕ} (w : Work K) (side : Fin 3)
    (b : w.Branch) : (nativeSplitWeightCode w side b).val = w.splitShape b side := rfl

theorem nativePairLaw_weight_marginal {K : ℕ} (w : Work K) (side : Fin 3)
    (hstage : w.stage ≠ 2) :
    (nativePairLaw w side).map (fun a => nativeStatisticWeightCode w a.1) =
      (branchLaw w).map (nativeSplitWeightCode w side) := by
  cases w with
  | stageA h =>
      change (stageAPairLaw (initialShape h.val) h.property side).map
        (fun a => halfWeightCode a.1) =
          (stageASplitLaw (initialShape h.val) h.property).map
            (stageASplitWeight (initialShape h.val) h.property side)
      rw [stageAPairLaw_leftWeight_marginal, stageASplitLaw_ownWeight_marginal]
  | stageB h =>
      change (stageBPairLaw (aShape h.val) h.property side).map
        (fun a => statisticWeightCode a.1) =
          (stageBSplitLaw (aShape h.val) h.property).map
            (stageBSplitWeight (aShape h.val) h.property side)
      rw [stageBPairLaw_leftWeight_marginal, stageBSplitLaw_ownWeight_marginal]
  | stageC h => exact False.elim (hstage rfl)

private theorem commonWeight_law_ext {A : Type*} [Fintype A]
    (p q : FiniteLaw A) (hmass : ∀ a, p.mass a = q.mass a) : p = q := by
  cases p with
  | mk p hp htotal =>
      cases q with
      | mk q hq hqtotal =>
          have heq : p = q := funext hmass
          subst q
          rfl

theorem order_branch_weight {K tick : ℕ} {sigma : Placement}
    (h : ActiveOrder K tick sigma) (side : Fin 3) (b : h.val.val.1.Branch) :
    JointPopulation.shapeSide (sigma side) (branchShape h.val.val b) =
      nativeSplitWeightCode h.val.val.1 (h.val.val.1.priority side) b := by
  apply Fin.ext
  rw [branchShape, encodePhysicalShape_side, nativeSplitWeightCode_val,
    placement_symm_order_side]

theorem orderLaw_weight_marginal {K tick : ℕ} {sigma : Placement}
    (h : ActiveOrder K tick sigma) (side : Fin 3) :
    (orderLaw h).map (JointPopulation.shapeSide (sigma side)) =
      (branchLaw h.val.val.1).map
        (nativeSplitWeightCode h.val.val.1 (h.val.val.1.priority side)) := by
  apply commonWeight_law_ext
  intro k
  have hm : ((orderLaw h).map (JointPopulation.shapeSide (sigma side))).mass k =
      JointPopulationRates.sideMass (placedLaw h.val.val).mass (sigma side) k := by
    rw [FiniteLaw.map_mass]
    unfold JointPopulationRates.sideMass
    apply Finset.sum_congr rfl
    intro u _
    by_cases hu : JointPopulation.shapeSide (sigma side) u = k <;> simp [hu, orderLaw]
  rw [hm, placedLaw_sideMass, FiniteLaw.map_mass]
  apply Finset.sum_congr rfl
  intro b _
  simp only [order_branch_weight, branchLaw_mass]

theorem orderPairLaw_common_weight {K tick : ℕ} {sigma : Placement}
    (h : ActiveOrder K tick sigma) (side : Fin 3) (hstage : h.val.val.1.stage ≠ 2) :
    (nativePairLaw h.val.val.1 (h.val.val.1.priority side)).map
        (fun a => nativeStatisticWeightCode h.val.val.1 a.1) =
      (orderLaw h).map (JointPopulation.shapeSide (sigma side)) := by
  rw [nativePairLaw_weight_marginal _ _ hstage, orderLaw_weight_marginal]

theorem order_entropy_sub_pair_eq_conditional_sum
    {K tick : ℕ} {sigma : Placement} (h : ActiveOrder K tick sigma)
    (side : Fin 3) (hstage : h.val.val.1.stage ≠ 2) :
    finiteEntropy (orderLaw h).mass -
        finiteEntropy (nativePairLaw h.val.val.1 (h.val.val.1.priority side)).mass =
      ∑ k, ((orderLaw h).map (JointPopulation.shapeSide (sigma side))).mass k *
        (finiteEntropy ((orderLaw h).conditional
            (JointPopulation.shapeSide (sigma side)) k).mass -
          finiteEntropy ((nativePairLaw h.val.val.1 (h.val.val.1.priority side)).conditional
            (fun a => nativeStatisticWeightCode h.val.val.1 a.1) k).mass) :=
  entropy_sub_eq_conditional_sum _ _ _ _ _ rfl (orderPairLaw_common_weight h side hstage)

theorem order_entropy_sub_mixture_eq_conditional_sum
    {K tick : ℕ} {sigma : Placement} (h : ActiveOrder K tick sigma)
    (side : Fin 3) (hstage : h.val.val.1.stage ≠ 2) :
    finiteEntropy (orderLaw h).mass - finiteEntropy (orderPairMixture h side) =
      ∑ k, ((orderLaw h).map (JointPopulation.shapeSide (sigma side))).mass k *
        (finiteEntropy ((orderLaw h).conditional
            (JointPopulation.shapeSide (sigma side)) k).mass -
          finiteEntropy ((nativePairLaw h.val.val.1 (h.val.val.1.priority side)).conditional
            (fun a => nativeStatisticWeightCode h.val.val.1 a.1) k).mass) := by
  rw [orderPairMixture_entropy]
  exact order_entropy_sub_pair_eq_conditional_sum h side hstage

end MatrixMultiplication.AllFieldGroupNativeLaws

end

end OAI
