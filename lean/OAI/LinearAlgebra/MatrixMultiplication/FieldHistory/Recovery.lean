import OAI.LinearAlgebra.MatrixMultiplication.FieldHistory.RecoveryCore
import OAI.LinearAlgebra.MatrixMultiplication.FieldHistory.Masks
import OAI.LinearAlgebra.MatrixMultiplication.FieldHistory.RecoveryBudget
import OAI.LinearAlgebra.MatrixMultiplication.FieldHistory.RawMasks
import OAI.LinearAlgebra.MatrixMultiplication.FieldHistory.IncomingMasks
import OAI.LinearAlgebra.MatrixMultiplication.JointExtraction.CanonicalSymmetry
import OAI.LinearAlgebra.MatrixMultiplication.JointExtraction.OrbitRecovery

namespace OAI

/-! Finite extraction histories, inherited masks and recovery bounds. -/

noncomputable section

namespace MatrixMultiplication.AllFieldHistoryRecovery

open MatrixMultiplication.Foundation AllFieldHistory AllFieldHistoryChildLaws
open AllFieldHistorySupport JointPopulation JointCanonicalization JointCanonicalCW
open PermutationMatching
open scoped BigOperators

attribute [local instance] Classical.propDecidable Classical.decEq

variable {K tick : ℕ}

theorem ideal_coordinates (F : Type*) [CommRing F] (allocation : Allocation)
    (m : ℕ) (ε : ℝ) (e : Targets (K := K) (tick := tick) allocation m)
    (x y z : Raw (K := K) (tick := tick) allocation m) :
    ideal F allocation m ε e x y z = canonical F allocation m ε
      (coordinates allocation m e x) (coordinates allocation m e y)
      (coordinates allocation m e z) :=
  ideal_eq_canonicalIdeal (activeCounts allocation m) (Left activeHalfLength)
    (Right activeHalfLength) (parents F)
    (coarse activeHalfLength activeHalfLength halfLength_le_eight)
    childStatistic childStatistic leftPrescription rightPrescription
    (outputWidth ε) (outputWidth ε) e x y z

theorem ideal_support_windows (F : Type*) [CommRing F] (allocation : Allocation)
    (m : ℕ) (ε : ℝ) (e : Targets (K := K) (tick := tick) allocation m)
    (x y z : Raw (K := K) (tick := tick) allocation m) (hq : ideal F allocation m ε e x y z ≠ 0) :
    AllFieldHistoryMasks.childWindows allocation m ε 0 (coordinates allocation m e x) ∧
    AllFieldHistoryMasks.childWindows allocation m ε 1 (coordinates allocation m e y) ∧
    AllFieldHistoryMasks.childWindows allocation m ε 2 (coordinates allocation m e z) := by
  by_contra hn
  apply hq
  rw [ideal_coordinates]
  change (if AllFieldHistoryMasks.childWindows allocation m ε 0 (coordinates allocation m e x) ∧
      AllFieldHistoryMasks.childWindows allocation m ε 1 (coordinates allocation m e y) ∧
      AllFieldHistoryMasks.childWindows allocation m ε 2 (coordinates allocation m e z)
    then _ else 0) = 0
  exact ite_eq_right hn

theorem raw_pair_loss_le (allocation : Allocation) {m : ℕ} (hm : 2 ≤ m)
    {ε : ℝ} (hε : 0 < ε) (side : Fin 3)
    (e : Targets (K := K) (tick := tick) allocation m) (w : Raw (K := K) (tick := tick) allocation m)
    (hw : AllFieldHistoryMasks.childWindows allocation m ε side
      (coordinates allocation m e w)) :
    letI : MulAction (Symmetries (K := K) (tick := tick) allocation m) (Raw (K := K) (tick := tick) allocation m) := rawAction allocation m e
    (((OrbitCounting.orbitSet (G := Symmetries (K := K) (tick := tick) allocation m) w).filter
      (fun v => ¬AllFieldHistoryRawMasks.rawPass allocation m ε side v)).card : ℝ) /
        (OrbitCounting.orbitSet (G := Symmetries (K := K) (tick := tick) allocation m) w).card ≤
      AllFieldHistoryMasks.lossConstant (K := K) (tick := tick) allocation ε / m := by
  let _ : MulAction (Symmetries (K := K) (tick := tick) allocation m) (Raw (K := K) (tick := tick) allocation m) := rawAction allocation m e
  have htransport := EquivOrbitTransport.rejected_fraction
    (G := Symmetries (K := K) (tick := tick) allocation m) (coordinates allocation m e)
    (fun v => ¬AllFieldHistoryRawMasks.rawPass allocation m ε side v) w
  have hcanonical := orbit_bad_fraction_eq_fullOrbitFilter_of_iff
    (G := Symmetries (K := K) (tick := tick) allocation m)
    (coordinates allocation m e w)
    ((fun v => ¬AllFieldHistoryRawMasks.rawPass allocation m ε side v) ∘
      (coordinates allocation m e).symm)
    (fun v => ∃ i : AllFieldHistoryMasks.MaskIndex K tick,
      selectedWordPairMaskBad (AllFieldHistoryMasks.testedClasses allocation i)
        AllFieldHistoryMasks.classStatistic AllFieldHistoryMasks.classStatistic
        (AllFieldHistoryMasks.leftSymbol i) (AllFieldHistoryMasks.rightSymbol i)
        (AllFieldHistoryMasks.pairWidth ε i.1) (AllFieldHistoryMasks.center allocation side i) v)
    (fun v => by
      change ¬AllFieldHistoryRawMasks.rawPass allocation m ε side
        ((coordinates allocation m e).symm v) ↔ _
      rw [← AllFieldHistoryRawMasks.passes_pairEquiv_iff_rawPass allocation m ε side e]
      change ¬AllFieldHistoryMasks.passes allocation m ε side
        ((coordinates allocation m e) ((coordinates allocation m e).symm v)) ↔ _
      rw [Equiv.apply_symm_apply]
      simp only [AllFieldHistoryMasks.passes, not_forall, not_not])
  exact htransport.trans_le (hcanonical.trans_le
    (AllFieldHistoryMasks.full_filter_loss_le allocation hm hε side
      (coordinates allocation m e w) hw))

theorem ideal_support_marginals (F : Type*) [CommRing F] (allocation : Allocation)
    (m : ℕ) (ε : ℝ) (e : Targets (K := K) (tick := tick) allocation m)
    (x y z : Raw (K := K) (tick := tick) allocation m) (hq : ideal F allocation m ε e x y z ≠ 0) :
    JointCanonicalMixed.sideMask (activeCounts allocation m)
        activeHalfLength activeHalfLength halfLength_le_eight 0 x ∧
    JointCanonicalMixed.sideMask (activeCounts allocation m)
        activeHalfLength activeHalfLength halfLength_le_eight 1 y ∧
    JointCanonicalMixed.sideMask (activeCounts allocation m)
        activeHalfLength activeHalfLength halfLength_le_eight 2 z := by
  exact JointCanonicalMixed.ideal_support_masks (activeCounts allocation m)
    activeHalfLength activeHalfLength activeParentShape (fun _ => true)
    halfLength_le_eight e _ _ _ x y z hq

def sideWeights (allocation : Allocation) (m : ℕ) (side : Fin 3)
    (e : Targets (K := K) (tick := tick) allocation m) (w : Raw (K := K) (tick := tick) allocation m) : Prop :=
  ∀ h j,
    CWStrands.weight (w h j).1 = (shapeSide side ((e h).val j)).val ∧
    CWStrands.weight (w h j).2 = activeParentShape h side -
      (shapeSide side ((e h).val j)).val

theorem ideal_support_weights (F : Type*) [CommRing F] (allocation : Allocation)
    (m : ℕ) (ε : ℝ) (e : Targets (K := K) (tick := tick) allocation m)
    (x y z : Raw (K := K) (tick := tick) allocation m) (hq : ideal F allocation m ε e x y z ≠ 0) :
    sideWeights allocation m 0 e x ∧ sideWeights allocation m 1 e y ∧
      sideWeights allocation m 2 e z := by
  have hb : coarseIdeal (activeCounts allocation m)
      (Left activeHalfLength) (Right activeHalfLength) (parents F)
      (coarse activeHalfLength activeHalfLength halfLength_le_eight) e x y z ≠ 0 := by
    intro hz
    apply hq
    simp only [ideal, JointCanonicalization.ideal, ExactRecovery.delete, hz, ite_self]
  have hc :
      coarseMask (activeCounts allocation m) (Left activeHalfLength) (Right activeHalfLength)
        (coarse activeHalfLength activeHalfLength halfLength_le_eight) 0 e x ∧
      coarseMask (activeCounts allocation m) (Left activeHalfLength) (Right activeHalfLength)
        (coarse activeHalfLength activeHalfLength halfLength_le_eight) 1 e y ∧
      coarseMask (activeCounts allocation m) (Left activeHalfLength) (Right activeHalfLength)
        (coarse activeHalfLength activeHalfLength halfLength_le_eight) 2 e z := by
    by_contra hn
    exact hb (by simp only [coarseIdeal, ExactRecovery.delete, ite_eq_right hn])
  have hs : rawSource F allocation m x y z ≠ 0 := by
    intro hz
    apply hb
    change (if _ then rawSource F allocation m x y z else 0) = 0
    simp only [hz, ite_self]
  have ht (h : Active K tick) (j : JointPopulation.Positions (activeCounts allocation m) h) :
      parents F h (x h j) (y h j) (z h j) ≠ 0 := by
    intro hz
    apply hs
    unfold rawSource sourceTensor InheritedMasks.classProduct
    exact Finset.prod_eq_zero (Finset.mem_univ h)
      (Finset.prod_eq_zero (Finset.mem_univ j) hz)
  have hp (h : Active K tick) (j : JointPopulation.Positions (activeCounts allocation m) h) :
      CWStrands.weight (x h j).1 + CWStrands.weight (x h j).2 = activeParentShape h 0 ∧
      CWStrands.weight (y h j).1 + CWStrands.weight (y h j).2 = activeParentShape h 1 ∧
      CWStrands.weight (z h j).1 + CWStrands.weight (z h j).2 = activeParentShape h 2 := by
    have hh := ht h j
    change CWStrands.shapeTensor
      (Fin (activeHalfLength h) ⊕ Fin (activeHalfLength h)) (activeParentShape h)
      (Sum.elim (x h j).1 (x h j).2) (Sum.elim (y h j).1 (y h j).2)
      (Sum.elim (z h j).1 (z h j).2) ≠ 0 at hh
    simpa only [CWStrands.weight_sum_elim] using
      CWStrands.shapeTensor_support (activeParentShape h) _ _ _ hh
  have hx (h : Active K tick) (j : JointPopulation.Positions (activeCounts allocation m) h) :
      CWStrands.weight (x h j).1 = (shapeSide 0 ((e h).val j)).val :=
    congrArg Fin.val (hc.1 h j)
  have hy (h : Active K tick) (j : JointPopulation.Positions (activeCounts allocation m) h) :
      CWStrands.weight (y h j).1 = (shapeSide 1 ((e h).val j)).val :=
    congrArg Fin.val (hc.2.1 h j)
  have hz (h : Active K tick) (j : JointPopulation.Positions (activeCounts allocation m) h) :
      CWStrands.weight (z h j).1 = (shapeSide 2 ((e h).val j)).val :=
    congrArg Fin.val (hc.2.2 h j)
  refine ⟨?_, ?_, ?_⟩
  · intro h j
    refine ⟨hx h j, ?_⟩
    have hh := (hp h j).1
    rw [hx h j] at hh
    omega
  · intro h j
    refine ⟨hy h j, ?_⟩
    have hh := (hp h j).2.1
    rw [hy h j] at hh
    omega
  · intro h j
    refine ⟨hz h j, ?_⟩
    have hh := (hp h j).2.2
    rw [hz h j] at hh
    omega

theorem stageCWeights_of_sideWeights (allocation : Allocation) (m : ℕ) (side : Fin 3)
    (e : Targets (K := K) (tick := tick) allocation m) (w : Raw (K := K) (tick := tick) allocation m)
    (hw : sideWeights allocation m side e w) :
    AllFieldHistoryIncomingMasks.stageCWeights allocation m side e w := by
  intro h phi ht j
  have hh := hw (AllFieldHistoryStageCIncoming.stageCActive h phi ht) j
  have hleft := Fin.sum_univ_one (fun i : Fin 1 => CWLeafStatistics.weight
    ((w (AllFieldHistoryStageCIncoming.stageCActive h phi ht) j).1 i))
  have hright := Fin.sum_univ_one (fun i : Fin 1 => CWLeafStatistics.weight
    ((w (AllFieldHistoryStageCIncoming.stageCActive h phi ht) j).2 i))
  exact ⟨hleft.symm.trans hh.1, hright.symm.trans hh.2⟩

theorem completeKeep_of_supported (allocation : Allocation) {m : ℕ} (hm : 0 < m)
    {ε : ℝ} (hε : 0 ≤ ε) (side : Fin 3)
    (e : Targets (K := K) (tick := tick) allocation m) (w : Raw (K := K) (tick := tick) allocation m)
    (hmarginal : JointCanonicalMixed.sideMask (activeCounts allocation m)
      activeHalfLength activeHalfLength halfLength_le_eight side w)
    (hweights : sideWeights allocation m side e w)
    (hpass : AllFieldHistoryRawMasks.rawPass allocation m ε side w) :
    completeKeep allocation m ε side w :=
  ⟨hmarginal, AllFieldHistoryIncomingMasks.received_of_rawPass allocation hm hε side e w
    hpass (stageCWeights_of_sideWeights allocation m side e w hweights), hpass⟩

theorem occupied_split_le (allocation : Allocation) (m : ℕ)
    (h : Active K tick) (u : JointPopulation.Shape)
    (hu : 0 < activeCounts allocation m h u) :
    ∀ s, shapeNat u s ≤ activeParentShape h s :=
  jointCounts_support_le allocation m h.val u hu

theorem ideal_smul (F : Type*) [CommRing F] (allocation : Allocation) (m : ℕ) (ε : ℝ)
    (e : Targets (K := K) (tick := tick) allocation m) :
    letI : MulAction (Symmetries (K := K) (tick := tick) allocation m) (Raw (K := K) (tick := tick) allocation m) := rawAction allocation m e
    ∀ (g : Symmetries (K := K) (tick := tick) allocation m) x y z,
      ideal F allocation m ε e (g • x) (g • y) (g • z) = ideal F allocation m ε e x y z := by
  exact JointCanonicalSymmetry.rawIdeal_smul (activeCounts allocation m)
    activeHalfLength activeHalfLength activeParentShape (fun _ => true)
    halfLength_le_eight childStatistic childStatistic leftPrescription rightPrescription
    (outputWidth ε) (outputWidth ε)
    (fun h u hu _ => occupied_split_le allocation m h u hu) e

def Used (F : Type*) [CommRing F] (allocation : Allocation) (m : ℕ) (ε : ℝ)
    (e : Targets (K := K) (tick := tick) allocation m) (side : Fin 3)
    (w : Raw (K := K) (tick := tick) allocation m) : Prop :=
  ∃ x y z, ideal F allocation m ε e x y z ≠ 0 ∧ sideVariable side x y z = w

theorem used_windows (F : Type*) [CommRing F] (allocation : Allocation)
    (m : ℕ) (ε : ℝ) (e : Targets (K := K) (tick := tick) allocation m)
    (side : Fin 3) (w : Raw (K := K) (tick := tick) allocation m) (hw : Used F allocation m ε e side w) :
    AllFieldHistoryMasks.childWindows allocation m ε side (coordinates allocation m e w) := by
  obtain ⟨x, y, z, hq, rfl⟩ := hw
  have hh := ideal_support_windows F allocation m ε e x y z hq
  fin_cases side
  · exact hh.1
  · exact hh.2.1
  · exact hh.2.2

theorem used_keep_iff_rawPass (F : Type*) [CommRing F] (allocation : Allocation)
    {m : ℕ} (hm : 0 < m) {ε : ℝ} (hε : 0 ≤ ε)
    (e : Targets (K := K) (tick := tick) allocation m)
    (side : Fin 3) (w : Raw (K := K) (tick := tick) allocation m) (hw : Used F allocation m ε e side w) :
    completeKeep allocation m ε side w ↔ AllFieldHistoryRawMasks.rawPass allocation m ε side w := by
  refine ⟨fun h => h.2.2, ?_⟩
  intro hp
  obtain ⟨x, y, z, hq, rfl⟩ := hw
  have hmg := ideal_support_marginals F allocation m ε e x y z hq
  have hwt := ideal_support_weights F allocation m ε e x y z hq
  fin_cases side
  · exact completeKeep_of_supported allocation hm hε 0 e x hmg.1 hwt.1 hp
  · exact completeKeep_of_supported allocation hm hε 1 e y hmg.2.1 hwt.2.1 hp
  · exact completeKeep_of_supported allocation hm hε 2 e z hmg.2.2 hwt.2.2 hp

theorem used_smul (F : Type*) [CommRing F] (allocation : Allocation)
    (m : ℕ) (ε : ℝ) (e : Targets (K := K) (tick := tick) allocation m)
    (side : Fin 3) (w : Raw (K := K) (tick := tick) allocation m) :
    letI : MulAction (Symmetries (K := K) (tick := tick) allocation m) (Raw (K := K) (tick := tick) allocation m) := rawAction allocation m e
    ∀ g : Symmetries (K := K) (tick := tick) allocation m, Used F allocation m ε e side w →
      Used F allocation m ε e side (g • w) := by
  let _ : MulAction (Symmetries (K := K) (tick := tick) allocation m) (Raw (K := K) (tick := tick) allocation m) := rawAction allocation m e
  intro g hw
  obtain ⟨x, y, z, hq, rfl⟩ := hw
  refine ⟨g • x, g • y, g • z, ?_, ?_⟩
  · rwa [ideal_smul]
  · fin_cases side <;> rfl

theorem deterministic_loss_le (F : Type*) [CommRing F] (allocation : Allocation)
    {m : ℕ} (hm : 2 ≤ m) {ε : ℝ} (hε : 0 < ε)
    (e : Targets (K := K) (tick := tick) allocation m)
    (side : Fin 3) (w : Raw (K := K) (tick := tick) allocation m) (hw : Used F allocation m ε e side w) :
    letI : MulAction (Symmetries (K := K) (tick := tick) allocation m) (Raw (K := K) (tick := tick) allocation m) := rawAction allocation m e
    (((OrbitCounting.orbitSet (G := Symmetries (K := K) (tick := tick) allocation m) w).filter
      (fun v => ¬completeKeep allocation m ε side v)).card : ℝ) /
        (OrbitCounting.orbitSet (G := Symmetries (K := K) (tick := tick) allocation m) w).card ≤
      AllFieldHistoryMasks.lossConstant (K := K) (tick := tick) allocation ε / m := by
  let _ : MulAction (Symmetries (K := K) (tick := tick) allocation m) (Raw (K := K) (tick := tick) allocation m) := rawAction allocation m e
  have hmpos : 0 < m := lt_of_lt_of_le (by decide : 0 < 2) hm
  have heq : ((OrbitCounting.orbitSet (G := Symmetries (K := K) (tick := tick) allocation m) w).filter
      (fun v => ¬completeKeep allocation m ε side v)) =
      ((OrbitCounting.orbitSet (G := Symmetries (K := K) (tick := tick) allocation m) w).filter
      (fun v => ¬AllFieldHistoryRawMasks.rawPass allocation m ε side v)) := by
    apply Finset.filter_congr
    intro v hv
    obtain ⟨g, _, rfl⟩ := Finset.mem_image.mp hv
    rw [used_keep_iff_rawPass F allocation hmpos hε.le e side (g • w)
      (used_smul F allocation m ε e side w g hw)]
  rw [heq]
  exact raw_pair_loss_le allocation hm hε side e w
    (used_windows F allocation m ε e side w hw)

def holedIdeal (F : Type*) [CommRing F] (allocation : Allocation) (m : ℕ) (ε : ℝ)
    (e : Targets (K := K) (tick := tick) allocation m)
    (assigned : Fin 3 → Raw (K := K) (tick := tick) allocation m → Prop) :
    Tensor F (Raw (K := K) (tick := tick) allocation m) (Raw (K := K) (tick := tick) allocation m) (Raw (K := K) (tick := tick) allocation m) :=
  ExactRecovery.delete (ideal F allocation m ε e)
    (fun w => assigned 0 w ∧ completeKeep allocation m ε 0 w)
    (fun w => assigned 1 w ∧ completeKeep allocation m ε 1 w)
    (fun w => assigned 2 w ∧ completeKeep allocation m ε 2 w)

theorem ideal_eq_delete_source (F : Type*) [CommRing F] (allocation : Allocation)
    (m : ℕ) (ε : ℝ) (e : Targets (K := K) (tick := tick) allocation m) :
    ideal F allocation m ε e = ExactRecovery.delete (rawSource F allocation m)
      (idealSide allocation m ε 0 e) (idealSide allocation m ε 1 e)
      (idealSide allocation m ε 2 e) := by
  have hdelete (cx cy cz wx wy wz : Prop) (q : F)
      [dw : Decidable (wx ∧ wy ∧ wz)] [dc : Decidable (cx ∧ cy ∧ cz)]
      (dk : Decidable ((cx ∧ wx) ∧ (cy ∧ wy) ∧ (cz ∧ wz))) :
      @ite F (wx ∧ wy ∧ wz) dw (@ite F (cx ∧ cy ∧ cz) dc q 0) 0 =
        @ite F ((cx ∧ wx) ∧ (cy ∧ wy) ∧ (cz ∧ wz)) dk q 0 := by
    let _ : Decidable ((cx ∧ wx) ∧ (cy ∧ wy) ∧ (cz ∧ wz)) := dk
    by_cases hw : wx ∧ wy ∧ wz
    · by_cases hc : cx ∧ cy ∧ cz
      · have hk : (cx ∧ wx) ∧ (cy ∧ wy) ∧ (cz ∧ wz) :=
          ⟨⟨hc.1, hw.1⟩, ⟨hc.2.1, hw.2.1⟩, ⟨hc.2.2, hw.2.2⟩⟩
        rw [ite_eq_left hw, ite_eq_left hc, ite_eq_left hk]
      · have hk : ¬((cx ∧ wx) ∧ (cy ∧ wy) ∧ (cz ∧ wz)) :=
          fun h => hc ⟨h.1.1, h.2.1.1, h.2.2.1⟩
        rw [ite_eq_left hw, ite_eq_right hc, ite_eq_right hk]
    · have hk : ¬((cx ∧ wx) ∧ (cy ∧ wy) ∧ (cz ∧ wz)) :=
        fun h => hw ⟨h.1.2, h.2.1.2, h.2.2.2⟩
      rw [ite_eq_right hw, ite_eq_right hk]
  funext x y z
  simp only [ideal, JointCanonicalization.ideal, coarseIdeal, rawSource,
    idealSide, ExactRecovery.delete]
  exact @hdelete _ _ _ _ _ _ _ _ _ _

@[simp] theorem sideVariable_zero {V : Type*} (x y z : V) :
    sideVariable 0 x y z = x := rfl

@[simp] theorem sideVariable_one {V : Type*} (x y z : V) :
    sideVariable 1 x y z = y := rfl

@[simp] theorem sideVariable_two {V : Type*} (x y z : V) :
    sideVariable 2 x y z = z := rfl

theorem branch_eq_holedIdeal {I : Type*} (F : Type*) [CommRing F]
    (allocation : Allocation) (m : ℕ) (ε : ℝ)
    (a : JointExtraction.Assignment (Raw (K := K) (tick := tick) allocation m)
      (Raw (K := K) (tick := tick) allocation m) (Raw (K := K) (tick := tick) allocation m) I)
    (i : I) (e : Targets (K := K) (tick := tick) allocation m)
    (hx : ∀ w, a.x w = some i → idealSide allocation m ε 0 e w)
    (hy : ∀ w, a.y w = some i → idealSide allocation m ε 1 e w)
    (hz : ∀ w, a.z w = some i → idealSide allocation m ε 2 e w) :
    JointExtraction.branch
      (ExactRecovery.delete (rawSource F allocation m)
        (completeKeep allocation m ε 0) (completeKeep allocation m ε 1)
        (completeKeep allocation m ε 2)) a i =
      holedIdeal F allocation m ε e
        (fun side w => sideVariable side (a.x w = some i) (a.y w = some i) (a.z w = some i)) := by
  funext x y z
  simp only [holedIdeal, sideVariable_zero, sideVariable_one, sideVariable_two]
  by_cases ha : a.x x = some i ∧ a.y y = some i ∧ a.z z = some i
  · have hix := hx x ha.1
    have hiy := hy y ha.2.1
    have hiz := hz z ha.2.2
    rw [JointExtraction.branch, ite_eq_left ha, ideal_eq_delete_source]
    simp only [ExactRecovery.delete, hix, hiy, hiz, ha.1, ha.2.1, ha.2.2,
      true_and, ite_true]
  · have hnot : ¬((a.x x = some i ∧ completeKeep allocation m ε 0 x) ∧
        (a.y y = some i ∧ completeKeep allocation m ε 1 y) ∧
        (a.z z = some i ∧ completeKeep allocation m ε 2 z)) :=
      fun h => ha ⟨h.1.1, h.2.1.1, h.2.2.1⟩
    rw [JointExtraction.branch, ite_eq_right ha]
    simp only [ExactRecovery.delete, ite_eq_right hnot]

theorem support_filter_eq {F X Y Z : Type*} [Zero F]
    [Fintype X] [Fintype Y] [Fintype Z] (Q : Tensor F X Y Z) :
    (@Finset.filter (X × Y × Z) (fun p => Q p.1 p.2.1 p.2.2 ≠ 0)
      (Classical.decPred _) Finset.univ) = RecoverySupport.support Q := by
  ext p
  simp only [RecoverySupport.support, Finset.mem_filter]

theorem repair_selected (F : Type*) [CommRing F] (allocation : Allocation)
    {m : ℕ} {ε : ℝ} (hε : 0 < ε)
    (hm : minimumDilation (K := K) (tick := tick) allocation ε ≤ m)
    (e : Targets (K := K) (tick := tick) allocation m)
    (assigned : Fin 3 → Raw (K := K) (tick := tick) allocation m → Prop)
    (hcollision :
      letI : MulAction (Symmetries (K := K) (tick := tick) allocation m) (Raw (K := K) (tick := tick) allocation m) := rawAction allocation m e
      ∀ side w, Used F allocation m ε e side w →
        (((OrbitCounting.orbitSet (G := Symmetries (K := K) (tick := tick) allocation m) w).filter
          (fun v => completeKeep allocation m ε side v ∧ ¬assigned side v)).card : ℝ) /
          (OrbitCounting.orbitSet (G := Symmetries (K := K) (tick := tick) allocation m) w).card ≤ 6 / m) :
    InverseLinearRecovery.RecoveredBy (ideal F allocation m ε e)
      (holedIdeal F allocation m ε e assigned) (shiftCount (K := K) (tick := tick) allocation ε m) := by
  let _ : MulAction (Symmetries (K := K) (tick := tick) allocation m) (Raw (K := K) (tick := tick) allocation m) := rawAction allocation m e
  have hm' := minimumDilation_spec allocation ε hm
  have hc : 0 < AllFieldHistoryMasks.lossConstant (K := K) (tick := tick) allocation ε + 6 := by
    have := AllFieldHistoryMasks.lossConstant_nonneg (K := K) (tick := tick) allocation ε
    linarith
  have hloss (side : Fin 3) (w : Raw (K := K) (tick := tick) allocation m)
      (hw : Used F allocation m ε e side w) :
      (((OrbitCounting.orbitSet (G := Symmetries (K := K) (tick := tick) allocation m) w).filter
        (fun v => ¬(assigned side v ∧ completeKeep allocation m ε side v))).card : ℝ) /
        (OrbitCounting.orbitSet (G := Symmetries (K := K) (tick := tick) allocation m) w).card ≤
      (AllFieldHistoryMasks.lossConstant (K := K) (tick := tick) allocation ε + 6) / m := by
    have heq : ((OrbitCounting.orbitSet (G := Symmetries (K := K) (tick := tick) allocation m) w).filter
        (fun v => ¬(assigned side v ∧ completeKeep allocation m ε side v))) =
        ((OrbitCounting.orbitSet (G := Symmetries (K := K) (tick := tick) allocation m) w).filter
        (fun v => ¬(completeKeep allocation m ε side v ∧ assigned side v))) := by
      ext v
      simp only [Finset.mem_filter]
      exact and_congr Iff.rfl (not_congr and_comm)
    rw [heq]
    rw [OrbitLoss.missing_fraction_partition
      (OrbitCounting.orbitSet (G := Symmetries (K := K) (tick := tick) allocation m) w)
      (completeKeep allocation m ε side) (assigned side), add_div]
    exact add_le_add (deterministic_loss_le F allocation hm'.1 hε e side w hw)
      (hcollision side w hw)
  unfold holedIdeal shiftCount
  apply InverseLinearRecovery.repair_inverse_linear (G := Symmetries (K := K) (tick := tick) allocation m)
    (ideal F allocation m ε e)
    (fun w => assigned 0 w ∧ completeKeep allocation m ε 0 w)
    (fun w => assigned 1 w ∧ completeKeep allocation m ε 1 w)
    (fun w => assigned 2 w ∧ completeKeep allocation m ε 2 w)
    (ideal_smul F allocation m ε e) (supportRate_pos (K := K) (tick := tick) allocation).le hc hm'.2
  · rw [support_filter_eq]
    exact raw_support_card_le_exp allocation m (ideal F allocation m ε e)
  · intro x hx
    obtain ⟨y, z, hq⟩ := hx
    exact hloss 0 x ⟨x, y, z, hq, rfl⟩
  · intro y hy
    obtain ⟨x, z, hq⟩ := hy
    exact hloss 1 y ⟨x, y, z, hq, rfl⟩
  · intro z hz
    obtain ⟨x, y, hq⟩ := hz
    exact hloss 2 z ⟨x, y, z, hq, rfl⟩

theorem repair_selected_branch {I : Type*} (F : Type*) [CommRing F]
    (allocation : Allocation) {m : ℕ} {ε : ℝ} (hε : 0 < ε)
    (hm : minimumDilation (K := K) (tick := tick) allocation ε ≤ m)
    (a : JointExtraction.Assignment (Raw (K := K) (tick := tick) allocation m)
      (Raw (K := K) (tick := tick) allocation m) (Raw (K := K) (tick := tick) allocation m) I)
    (i : I) (e : Targets (K := K) (tick := tick) allocation m)
    (hx : ∀ w, a.x w = some i → idealSide allocation m ε 0 e w)
    (hy : ∀ w, a.y w = some i → idealSide allocation m ε 1 e w)
    (hz : ∀ w, a.z w = some i → idealSide allocation m ε 2 e w)
    (hcollision :
      letI : MulAction (Symmetries (K := K) (tick := tick) allocation m) (Raw (K := K) (tick := tick) allocation m) := rawAction allocation m e
      ∀ side w, Used F allocation m ε e side w →
        (((OrbitCounting.orbitSet (G := Symmetries (K := K) (tick := tick) allocation m) w).filter
          (fun v => completeKeep allocation m ε side v ∧
            ¬sideVariable side (a.x v = some i) (a.y v = some i) (a.z v = some i))).card : ℝ) /
          (OrbitCounting.orbitSet (G := Symmetries (K := K) (tick := tick) allocation m) w).card ≤ 6 / m) :
    InverseLinearRecovery.RecoveredBy (ideal F allocation m ε e)
      (JointExtraction.branch
        (ExactRecovery.delete (rawSource F allocation m)
          (completeKeep allocation m ε 0) (completeKeep allocation m ε 1)
          (completeKeep allocation m ε 2)) a i) (shiftCount (K := K) (tick := tick) allocation ε m) := by
  rw [branch_eq_holedIdeal F allocation m ε a i e hx hy hz]
  exact repair_selected F allocation hε hm e _ hcollision

end MatrixMultiplication.AllFieldHistoryRecovery

end

end OAI
