import Mathlib
import OAI.LinearAlgebra.MatrixFields.Construction.JointCanonicalSymmetry

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

noncomputable section

namespace MatrixMultiplication.PermutationMatching

open MatrixMultiplication.InheritedMasks
open scoped BigOperators

attribute [local instance] Classical.propDecidable Classical.decEq

def fullOrbitFilter (G : Type*) {V : Type*} [SMul G V] [Fintype V]
    (v : V) : Finset V :=
  @Finset.filter V (fun w => ∃ g : G, g • v = w)
    (fun w => Classical.propDecidable (∃ g : G, g • v = w)) Finset.univ

def rejectedFilter {V : Type*} (orbit : Finset V) (bad : V → Prop) : Finset V :=
  @Finset.filter V bad (fun v => Classical.propDecidable (bad v)) orbit

theorem orbitSet_eq_fullOrbitFilter {G V : Type*} [Group G] [Fintype G]
    [MulAction G V] [Fintype V] [DecidableEq V] (v : V) :
    OrbitCounting.orbitSet (G := G) v = fullOrbitFilter G v := by
  ext w
  simp only [OrbitCounting.orbitSet, fullOrbitFilter, Finset.mem_image,
    Finset.mem_univ, true_and, Finset.mem_filter]

theorem rejectedFilter_congr {V : Type*} (orbit : Finset V) (p q : V → Prop)
    (h : ∀ v, p v ↔ q v) : rejectedFilter orbit p = rejectedFilter orbit q := by
  ext v
  simp only [rejectedFilter, Finset.mem_filter, h]

theorem fullOrbitFilter_bad_fraction_eq_orbit {G V : Type*}
    [Group G] [Fintype G] [MulAction G V] [Fintype V] [DecidableEq V]
    (w : V) (bad : V → Prop) [DecidablePred bad] :
    ((rejectedFilter (fullOrbitFilter G w) bad).card : ℝ) /
        (fullOrbitFilter G w).card =
      (((OrbitCounting.orbitSet (G := G) w).filter bad).card : ℝ) /
        (OrbitCounting.orbitSet (G := G) w).card := by
  have horbit := orbitSet_eq_fullOrbitFilter (G := G) w
  have hbad : (OrbitCounting.orbitSet (G := G) w).filter bad =
      rejectedFilter (fullOrbitFilter G w) bad := by
    ext v
    simp only [Finset.mem_filter, rejectedFilter, horbit]
  rw [hbad, horbit]

theorem orbit_bad_fraction_eq_fullOrbitFilter_of_iff {G V : Type*}
    [Group G] [Fintype G] [MulAction G V] [Fintype V] [DecidableEq V]
    (w : V) (bad canonical : V → Prop) [DecidablePred bad]
    (h : ∀ v, bad v ↔ canonical v) :
    (((OrbitCounting.orbitSet (G := G) w).filter bad).card : ℝ) /
        (OrbitCounting.orbitSet (G := G) w).card =
      ((rejectedFilter (fullOrbitFilter G w) canonical).card : ℝ) /
        (fullOrbitFilter G w).card := by
  rw [← fullOrbitFilter_bad_fraction_eq_orbit (G := G) w bad,
    rejectedFilter_congr (fullOrbitFilter G w) bad canonical h]

theorem full_orbitSet_as_filter {G V : Type*} [Group G] [Fintype G]
    [MulAction G V] [Fintype V] [DecidableEq V] (v : V) :
    OrbitCounting.orbitSet (G := G) v =
      Finset.univ.filter (fun w => ∃ g : G, g • v = w) := by
  ext w
  simp only [OrbitCounting.orbitSet, Finset.mem_image, Finset.mem_univ,
    true_and, Finset.mem_filter]

variable {C : Type*} {P X Y : C → Type*}
variable [Fintype C] [DecidableEq C]
  [∀ c, Fintype (P c)] [∀ c, DecidableEq (P c)]
  [Fintype (CompleteWordPair P X Y)]
variable {I : Type*} [Fintype I] {SL SR : I → C → Type*}

theorem finite_selectedWordPair_full_filter_inverse_linear_of_windows
    (D : I → Finset C) (w : CompleteWordPair P X Y)
    (sl : ∀ i c, X c → SL i c) (sr : ∀ i c, Y c → SR i c)
    (s : ∀ i c, SL i c) (t : ∀ i c, SR i c)
    (hn : ∀ i c, c ∈ D i → 2 ≤ Fintype.card (P c))
    (mass : I → ℝ) (N : ℝ) (hN : 0 < N) (hmass : ∀ i, 0 < mass i)
    (hsize : ∀ i, populationSize (fun c : D i => P c) = mass i * N)
    (left right : I → C → ℝ) (η τ α ν : I → ℝ) (hη : ∀ i, 0 < η i)
    (hright0 : ∀ i c, c ∈ D i → 0 ≤ right i c)
    (hright1 : ∀ i c, c ∈ D i → right i c ≤ 1)
    (hleft : ∀ i c, c ∈ D i →
      |classDensity (wordPairLeftPositions w (sl i) (s i)) c - left i c| ≤ τ i)
    (hright : ∀ i c, c ∈ D i →
      |classDensity (wordPairRightPositions w (sr i) (t i)) c - right i c| ≤ τ i)
    (happrox : ∀ i, |classProductMixture (fun c : D i => P c)
      (fun c => left i c) (fun c => right i c) - ν i| ≤ α i)
    (hτ : ∀ i, τ i ≤ η i / 8) (hα : ∀ i, α i ≤ η i / 4) :
    ((rejectedFilter (fullOrbitFilter (HalfClassPermutations P) w)
        (fun v => ∃ i, selectedWordPairMaskBad (D i) (sl i) (sr i)
          (s i) (t i) (η i) (ν i) v)).card : ℝ) /
      (fullOrbitFilter (HalfClassPermutations P) w).card ≤
        (∑ i, 1 / (2 * mass i * (η i) ^ 2)) / N := by
  classical
  have h := finite_selectedWordPair_orbit_inverse_linear_of_windows
    D w sl sr s t hn mass N hN hmass hsize left right η τ α ν hη
    hright0 hright1 hleft hright happrox hτ hα
  exact (fullOrbitFilter_bad_fraction_eq_orbit (G := HalfClassPermutations P) w _).trans_le h

end MatrixMultiplication.PermutationMatching

namespace MatrixMultiplication.AllFieldHistoryMasks

open AllFieldHistory AllFieldHistoryChildLaws AllFieldHistorySupport
open JointCanonicalization InheritedMasks PermutationMatching HistorySymmetry
open scoped BigOperators

attribute [local instance] Classical.propDecidable Classical.decEq

variable {K tick : ℕ}

theorem testedClasses_parent (allocation : Allocation) (i : MaskIndex K tick)
    (c : Classes K tick) (hc : c ∈ testedClasses allocation i) : c.1 = i.1 :=
  (Finset.mem_filter.mp hc).2.1

theorem rightProbability_le_one (allocation : Allocation) (side : Fin 3)
    (i : MaskIndex K tick) (c : Classes K tick) (hc : c ∈ testedClasses allocation i) :
    rightProbability side i c ≤ 1 := by
  have hsum := rightLaw_normalized allocation 1 c.1 c.2
    (positiveClasses_positive allocation i.1 c hc) side
  rw [← hsum]
  exact Finset.single_le_sum (fun a _ => rightLaw_nonnegative c.1 c.2 side a)
    (Finset.mem_univ _)

theorem left_density_le (allocation : Allocation) {m : ℕ} (hm : 0 < m)
    (ε : ℝ) (side : Fin 3) (w : Words (K := K) (tick := tick) allocation m)
    (hw : childWindows allocation m ε side w) (i : MaskIndex K tick)
    (c : Classes K tick) (hc : c ∈ testedClasses allocation i) :
    |classDensity (wordPairLeftPositions w classStatistic (leftSymbol i)) c -
      leftProbability side i c| ≤ childWidth ε i.1 := by
  have hp : 0 < activeCounts allocation m c.1 c.2 :=
    (activeCounts_pos_iff allocation hm c.1 c.2).2
      (positiveClasses_positive allocation i.1 c hc)
  have ht := (hw c).1 (leftSymbol i c)
  have hh := testedClasses_parent allocation i c hc
  have ht' : |empiricalLaw (classStatistic c ∘ w.left c) (leftSymbol i c) -
      leftProbability side i c| ≤ childWidth ε c.1 := by
    simpa only [activeLaw, activeWidth, ite_eq_left hp, leftProbability] using ht
  have hd := classDensity_statisticPositions w.left classStatistic (leftSymbol i) c
  change classDensity (wordPairLeftPositions w classStatistic (leftSymbol i)) c = _ at hd
  rw [hd]
  exact ht'.trans_eq (congrArg (childWidth ε) hh)

theorem right_density_le (allocation : Allocation) {m : ℕ} (hm : 0 < m)
    (ε : ℝ) (side : Fin 3) (w : Words (K := K) (tick := tick) allocation m)
    (hw : childWindows allocation m ε side w) (i : MaskIndex K tick)
    (c : Classes K tick) (hc : c ∈ testedClasses allocation i) :
    |classDensity (wordPairRightPositions w classStatistic (rightSymbol i)) c -
      rightProbability side i c| ≤ childWidth ε i.1 := by
  have hp : 0 < activeCounts allocation m c.1 c.2 :=
    (activeCounts_pos_iff allocation hm c.1 c.2).2
      (positiveClasses_positive allocation i.1 c hc)
  have ht := (hw c).2 (rightSymbol i c)
  have hh := testedClasses_parent allocation i c hc
  have ht' : |empiricalLaw (classStatistic c ∘ w.right c) (rightSymbol i c) -
      rightProbability side i c| ≤ childWidth ε c.1 := by
    simpa only [activeLaw, activeWidth, ite_eq_left hp, rightProbability] using ht
  have hd := classDensity_statisticPositions w.right classStatistic (rightSymbol i) c
  change classDensity (wordPairRightPositions w classStatistic (rightSymbol i)) c = _ at hd
  rw [hd]
  exact ht'.trans_eq (congrArg (childWidth ε) hh)

theorem mixture_error_zero (allocation : Allocation) {m : ℕ} (hm : 0 < m)
    (side : Fin 3) (i : MaskIndex K tick) :
    |classProductMixture (fun c : testedClasses allocation i => Positions allocation m c.val)
      (fun c => leftProbability side i c.val) (fun c => rightProbability side i c.val) -
        center allocation side i| ≤ (0 : ℝ) := by
  rw [selected_classProductMixture_eq_one allocation hm]
  simp only [center, sub_self, abs_zero, le_refl]

theorem orbitSet_as_filter {G V : Type*} [Group G] [Fintype G] [MulAction G V]
    [Fintype V] [DecidableEq V] (v : V) :
    OrbitCounting.orbitSet (G := G) v =
      Finset.univ.filter (fun w => ∃ g : G, g • v = w) := by
  ext w
  simp only [OrbitCounting.orbitSet, Finset.mem_image, Finset.mem_univ,
    true_and, Finset.mem_filter]

attribute [local irreducible] activeCounts

theorem full_filter_loss_le (allocation : Allocation) {m : ℕ} (hm : 2 ≤ m)
    {ε : ℝ} (hε : 0 < ε) (side : Fin 3)
    (w : Words (K := K) (tick := tick) allocation m)
    (hw : childWindows allocation m ε side w) :
    ((rejectedFilter
      (fullOrbitFilter (HalfClassPermutations (Positions (K := K) (tick := tick) allocation m)) w)
      (fun v => ∃ i : MaskIndex K tick,
        selectedWordPairMaskBad (testedClasses allocation i) classStatistic classStatistic
          (leftSymbol i) (rightSymbol i) (pairWidth ε i.1) (center allocation side i) v)).card : ℝ) /
      (fullOrbitFilter
        (HalfClassPermutations (Positions (K := K) (tick := tick) allocation m)) w).card ≤
      lossConstant (K := K) (tick := tick) allocation ε / m := by
  have hmpos : 0 < m := lt_of_lt_of_le (by decide : 0 < 2) hm
  have hsize (i : MaskIndex K tick) :
      populationSize (fun c : testedClasses allocation i => Positions allocation m c.val) =
        selectedBasePopulation allocation (testedClasses allocation i) * m :=
    selected_populationSize allocation m (testedClasses allocation i)
  have hn (i : MaskIndex K tick) (c : Classes K tick)
      (hc : c ∈ testedClasses allocation i) : 2 ≤ Fintype.card (Positions allocation m c) := by
    exact selected_two_le allocation hm (testedClasses allocation i)
      (positiveClasses_positive allocation i.1) ⟨c, hc⟩
  have hmass (i : MaskIndex K tick) :
      0 < selectedBasePopulation allocation (testedClasses allocation i) :=
    positiveClasses_basePopulation_pos allocation i.1
  have hright0 (i : MaskIndex K tick) (c : Classes K tick)
      (_hc : c ∈ testedClasses allocation i) : 0 ≤ rightProbability side i c :=
    rightLaw_nonnegative c.1 c.2 side _
  have h := finite_selectedWordPair_full_filter_inverse_linear_of_windows
    (C := Classes K tick) (P := Positions (K := K) (tick := tick) allocation m)
    (X := Letters) (Y := Letters) (I := MaskIndex K tick)
    (SL := fun _ c => Statistic c.1) (SR := fun _ c => Statistic c.1)
    (testedClasses allocation) w (fun _ => classStatistic) (fun _ => classStatistic)
    leftSymbol rightSymbol hn
    (fun i => selectedBasePopulation allocation (testedClasses allocation i)) (m : ℝ)
    (by exact_mod_cast hmpos) hmass hsize
    (leftProbability side) (rightProbability side)
    (fun i => pairWidth ε i.1) (fun i => childWidth ε i.1) (fun _ => 0)
    (center allocation side) (fun i => pairWidth_pos hε i.1)
    hright0 (rightProbability_le_one allocation side)
    (left_density_le allocation hmpos ε side w hw)
    (right_density_le allocation hmpos ε side w hw)
    (mixture_error_zero allocation hmpos side) (fun _ => le_rfl)
    (fun i => (div_pos (pairWidth_pos hε i.1) (by norm_num : (0 : ℝ) < 4)).le)
  simpa only [lossConstant] using h

theorem orbit_loss_le (allocation : Allocation) {m : ℕ} (hm : 2 ≤ m)
    {ε : ℝ} (hε : 0 < ε) (side : Fin 3)
    (w : Words (K := K) (tick := tick) allocation m)
    (hw : childWindows allocation m ε side w) :
    (((OrbitCounting.orbitSet
      (G := HalfClassPermutations (Positions (K := K) (tick := tick) allocation m)) w).filter
        (fun v => ¬passes allocation m ε side v)).card : ℝ) /
      (OrbitCounting.orbitSet
        (G := HalfClassPermutations (Positions (K := K) (tick := tick) allocation m)) w).card ≤
      lossConstant (K := K) (tick := tick) allocation ε / m := by
  have heq := orbit_bad_fraction_eq_fullOrbitFilter_of_iff
    (G := HalfClassPermutations (Positions (K := K) (tick := tick) allocation m)) w
    (fun v => ¬passes allocation m ε side v)
    (fun v => ∃ i : MaskIndex K tick,
      selectedWordPairMaskBad (testedClasses allocation i) classStatistic classStatistic
        (leftSymbol i) (rightSymbol i) (pairWidth ε i.1) (center allocation side i) v)
    (fun v => by simp only [passes, not_forall, not_not])
  exact heq.trans_le (full_filter_loss_le allocation hm hε side w hw)

end MatrixMultiplication.AllFieldHistoryMasks

end

namespace MatrixMultiplication.OrbitLoss

variable {X : Type*} [DecidableEq X]

theorem missing_card_partition (s : Finset X) (pass assigned : X → Prop)
    [DecidablePred pass] [DecidablePred assigned] :
    (s.filter fun x => ¬(pass x ∧ assigned x)).card =
      (s.filter fun x => ¬pass x).card +
      (s.filter fun x => pass x ∧ ¬assigned x).card := by
  classical
  have heq : (s.filter fun x => ¬(pass x ∧ assigned x)) =
      (s.filter fun x => ¬pass x) ∪ (s.filter fun x => pass x ∧ ¬assigned x) := by
    ext x
    by_cases hp : pass x <;> simp [hp]
  have hd : Disjoint (s.filter fun x => ¬pass x)
      (s.filter fun x => pass x ∧ ¬assigned x) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    exact (Finset.mem_filter.mp hx).2 (Finset.mem_filter.mp hy).2.1
  rw [heq, Finset.card_union_of_disjoint hd]

theorem missing_fraction_partition (s : Finset X) (pass assigned : X → Prop)
    [DecidablePred pass] [DecidablePred assigned] :
    ((s.filter fun x => ¬(pass x ∧ assigned x)).card : ℝ) / s.card =
      ((s.filter fun x => ¬pass x).card : ℝ) / s.card +
      ((s.filter fun x => pass x ∧ ¬assigned x).card : ℝ) / s.card := by
  rw [missing_card_partition, Nat.cast_add, add_div]

theorem combined_inverse_linear (s : Finset X) (pass assigned : X → Prop)
    [DecidablePred pass] [DecidablePred assigned] (C : ℝ) (N : ℕ)
    (hmask : ((s.filter fun x => ¬pass x).card : ℝ) / s.card ≤ C / N)
    (hcollision : ((s.filter fun x => pass x ∧ ¬assigned x).card : ℝ) / s.card ≤ 1 / N) :
    ((s.filter fun x => ¬(pass x ∧ assigned x)).card : ℝ) / s.card ≤ (C + 1) / N := by
  rw [missing_fraction_partition, add_div]
  exact add_le_add hmask hcollision

end MatrixMultiplication.OrbitLoss

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

open MatrixMultiplication.Foundation

namespace MatrixMultiplication.JointOrbitRecovery

variable {K G X Y Z : Type*} [CommSemiring K] [Group G] [Fintype G]
  [MulAction G X] [MulAction G Y] [MulAction G Z]
  [Fintype X] [Fintype Y] [Fintype Z]
  [DecidableEq X] [DecidableEq Y] [DecidableEq Z]

def SeparatedLoss {V : Type*} [DecidableEq V] [MulAction G V]
    (pass assigned : V → Prop) [DecidablePred pass] [DecidablePred assigned]
    (C : ℝ) (N : ℕ) (v : V) : Prop :=
  (((OrbitCounting.orbitSet (G := G) v).filter fun w => ¬pass w).card : ℝ) /
      (OrbitCounting.orbitSet (G := G) v).card ≤ C / N ∧
  (((OrbitCounting.orbitSet (G := G) v).filter fun w => pass w ∧ ¬assigned w).card : ℝ) /
      (OrbitCounting.orbitSet (G := G) v).card ≤ 1 / N

theorem separatedLoss_transport {U V : Type*} [DecidableEq U] [DecidableEq V]
    [MulAction G V] (e : U ≃ V)
    (pass assigned : U → Prop) [DecidablePred pass] [DecidablePred assigned]
    (C : ℝ) (N : ℕ) (u : U) :
    letI : MulAction G U := EquivOrbitTransport.action e
    SeparatedLoss (G := G) pass assigned C N u ↔
      SeparatedLoss (G := G) (pass ∘ e.symm) (assigned ∘ e.symm) C N (e u) := by
  let : MulAction G U := EquivOrbitTransport.action e
  unfold SeparatedLoss
  rw [EquivOrbitTransport.rejected_fraction e (fun w => ¬pass w) u,
    EquivOrbitTransport.rejected_fraction e (fun w => pass w ∧ ¬assigned w) u]
  simp only [Function.comp_def]

theorem combined_loss {V : Type*} [DecidableEq V] [MulAction G V]
    (pass assigned : V → Prop) [DecidablePred pass] [DecidablePred assigned]
    (C : ℝ) (N : ℕ) (v : V) (h : SeparatedLoss (G := G) pass assigned C N v) :
    (((OrbitCounting.orbitSet (G := G) v).filter fun w => ¬(assigned w ∧ pass w)).card : ℝ) /
      (OrbitCounting.orbitSet (G := G) v).card ≤ (C + 1) / N := by
  simpa only [and_comm] using
    OrbitLoss.combined_inverse_linear (OrbitCounting.orbitSet (G := G) v)
      pass assigned C N h.1 h.2

theorem repair_of_separated_losses
    (Q H : Tensor K X Y Z)
    (passX assignedX : X → Prop) (passY assignedY : Y → Prop)
    (passZ assignedZ : Z → Prop)
    [DecidablePred passX] [DecidablePred assignedX]
    [DecidablePred passY] [DecidablePred assignedY]
    [DecidablePred passZ] [DecidablePred assignedZ]
    (hhole : H = ExactRecovery.delete Q
      (fun x => assignedX x ∧ passX x) (fun y => assignedY y ∧ passY y)
      (fun z => assignedZ z ∧ passZ z))
    (hpreserve : ∀ (g : G) x y z, Q (g • x) (g • y) (g • z) = Q x y z)
    {b C : ℝ} {N : ℕ} (hb : 0 ≤ b) (hC : 0 ≤ C)
    (hN : 3 * (C + 1) < (N : ℝ))
    (hsupport : ((RecoverySupport.support Q).card : ℝ) ≤ Real.exp (b * N))
    (hx : ∀ x, (∃ y z, Q x y z ≠ 0) →
      SeparatedLoss (G := G) passX assignedX C N x)
    (hy : ∀ y, (∃ x z, Q x y z ≠ 0) →
      SeparatedLoss (G := G) passY assignedY C N y)
    (hz : ∀ z, (∃ x y, Q x y z ≠ 0) →
      SeparatedLoss (G := G) passZ assignedZ C N z) :
    InverseLinearRecovery.RecoveredBy Q H (RecoveryGrowth.shiftCount b (C + 1) N) := by
  classical
  rw [hhole]
  apply InverseLinearRecovery.repair_inverse_linear Q
    (fun x => assignedX x ∧ passX x) (fun y => assignedY y ∧ passY y)
    (fun z => assignedZ z ∧ passZ z) hpreserve hb (by linarith) hN
  · have heq : (@Finset.filter (X × Y × Z)
        (fun p => Q p.1 p.2.1 p.2.2 ≠ 0) (Classical.decPred _) Finset.univ) =
        RecoverySupport.support Q := by
      ext p
      simp only [RecoverySupport.support, Finset.mem_filter]
    rw [heq]
    exact hsupport
  · intro x hused
    exact combined_loss passX assignedX C N x (hx x hused)
  · intro y hused
    exact combined_loss passY assignedY C N y (hy y hused)
  · intro z hused
    exact combined_loss passZ assignedZ C N z (hz z hused)

theorem subexponential_copies {b C : ℝ} (hb : 0 < b) (hC : 0 ≤ C) :
    Filter.Tendsto (fun N : ℕ =>
      Real.log (Fintype.card
        (InverseLinearRecovery.MaskRectangles (RecoveryGrowth.shiftCount b (C + 1) N))) / N)
      Filter.atTop (nhds 0) :=
  InverseLinearRecovery.subexponential_copies hb (by linarith)

end MatrixMultiplication.JointOrbitRecovery

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

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
    letI _rawInst : MulAction (Symmetries (K := K) (tick := tick) allocation m) (Raw (K := K) (tick := tick) allocation m) := rawAction allocation m e
    (((OrbitCounting.orbitSet (G := Symmetries (K := K) (tick := tick) allocation m) w).filter
      (fun v => ¬AllFieldHistoryRawMasks.rawPass allocation m ε side v)).card : ℝ) /
        (OrbitCounting.orbitSet (G := Symmetries (K := K) (tick := tick) allocation m) w).card ≤
      AllFieldHistoryMasks.lossConstant (K := K) (tick := tick) allocation ε / m := by
  let rawInst : MulAction (Symmetries (K := K) (tick := tick) allocation m) (Raw (K := K) (tick := tick) allocation m) := rawAction allocation m e
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
  change (∑ index : Fin 1, CWLeafStatistics.weight
      ((w (AllFieldHistoryStageCIncoming.stageCActive h phi ht) j).1 index)) = _ ∧
    (∑ index : Fin 1, CWLeafStatistics.weight
      ((w (AllFieldHistoryStageCIncoming.stageCActive h phi ht) j).2 index)) = _ at hh
  simpa only [Fin.sum_univ_one] using hh

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
    letI rawInst : MulAction (Symmetries (K := K) (tick := tick) allocation m) (Raw (K := K) (tick := tick) allocation m) := rawAction allocation m e
    ∀ (g : Symmetries (K := K) (tick := tick) allocation m) (x y z : Raw (K := K) (tick := tick) allocation m),
      ideal F allocation m ε e ((@SMul.smul _ _ rawInst.toSMul g x)) ((@SMul.smul _ _ rawInst.toSMul g y)) ((@SMul.smul _ _ rawInst.toSMul g z)) = ideal F allocation m ε e x y z := by
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
    letI rawInst : MulAction (Symmetries (K := K) (tick := tick) allocation m) (Raw (K := K) (tick := tick) allocation m) := rawAction allocation m e
    ∀ g : Symmetries (K := K) (tick := tick) allocation m, Used F allocation m ε e side w →
      Used F allocation m ε e side ((@SMul.smul _ _ rawInst.toSMul g w)) := by
  let rawInst : MulAction (Symmetries (K := K) (tick := tick) allocation m) (Raw (K := K) (tick := tick) allocation m) := rawAction allocation m e
  intro g hw
  obtain ⟨x, y, z, hq, rfl⟩ := hw
  refine ⟨(@SMul.smul _ _ rawInst.toSMul g x), (@SMul.smul _ _ rawInst.toSMul g y), (@SMul.smul _ _ rawInst.toSMul g z), ?_, ?_⟩
  · rwa [ideal_smul]
  · fin_cases side <;> rfl

theorem deterministic_loss_le (F : Type*) [CommRing F] (allocation : Allocation)
    {m : ℕ} (hm : 2 ≤ m) {ε : ℝ} (hε : 0 < ε)
    (e : Targets (K := K) (tick := tick) allocation m)
    (side : Fin 3) (w : Raw (K := K) (tick := tick) allocation m) (hw : Used F allocation m ε e side w) :
    letI _rawInst : MulAction (Symmetries (K := K) (tick := tick) allocation m) (Raw (K := K) (tick := tick) allocation m) := rawAction allocation m e
    (((OrbitCounting.orbitSet (G := Symmetries (K := K) (tick := tick) allocation m) w).filter
      (fun v => ¬completeKeep allocation m ε side v)).card : ℝ) /
        (OrbitCounting.orbitSet (G := Symmetries (K := K) (tick := tick) allocation m) w).card ≤
      AllFieldHistoryMasks.lossConstant (K := K) (tick := tick) allocation ε / m := by
  let rawInst : MulAction (Symmetries (K := K) (tick := tick) allocation m) (Raw (K := K) (tick := tick) allocation m) := rawAction allocation m e
  have hmpos : 0 < m := lt_of_lt_of_le (by decide : 0 < 2) hm
  have heq : ((OrbitCounting.orbitSet (G := Symmetries (K := K) (tick := tick) allocation m) w).filter
      (fun v => ¬completeKeep allocation m ε side v)) =
      ((OrbitCounting.orbitSet (G := Symmetries (K := K) (tick := tick) allocation m) w).filter
      (fun v => ¬AllFieldHistoryRawMasks.rawPass allocation m ε side v)) := by
    apply Finset.filter_congr
    intro v hv
    obtain ⟨g, _, rfl⟩ := Finset.mem_image.mp hv
    exact not_congr (used_keep_iff_rawPass F allocation hmpos hε.le e side _
      (used_smul F allocation m ε e side w g hw))
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
  funext x y z
  simp only [ideal, JointCanonicalization.ideal, coarseIdeal, rawSource,
    idealSide, ExactRecovery.delete]
  split_ifs <;> simp_all
  rename_i hnot
  symm
  apply ite_eq_right
  intro hkeep
  exact hnot hkeep.1.2 hkeep.2.1.2 hkeep.2.2.2

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
      letI _rawInst : MulAction (Symmetries (K := K) (tick := tick) allocation m) (Raw (K := K) (tick := tick) allocation m) := rawAction allocation m e
      ∀ side w, Used F allocation m ε e side w →
        (((OrbitCounting.orbitSet (G := Symmetries (K := K) (tick := tick) allocation m) w).filter
          (fun v => completeKeep allocation m ε side v ∧ ¬assigned side v)).card : ℝ) /
          (OrbitCounting.orbitSet (G := Symmetries (K := K) (tick := tick) allocation m) w).card ≤ 6 / m) :
    InverseLinearRecovery.RecoveredBy (ideal F allocation m ε e)
      (holedIdeal F allocation m ε e assigned) (shiftCount (K := K) (tick := tick) allocation ε m) := by
  let rawInst : MulAction (Symmetries (K := K) (tick := tick) allocation m) (Raw (K := K) (tick := tick) allocation m) := rawAction allocation m e
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
  refine InverseLinearRecovery.repair_inverse_linear (G := Symmetries (K := K) (tick := tick) allocation m)
    (ideal F allocation m ε e)
    (fun w => assigned 0 w ∧ completeKeep allocation m ε 0 w)
    (fun w => assigned 1 w ∧ completeKeep allocation m ε 1 w)
    (fun w => assigned 2 w ∧ completeKeep allocation m ε 2 w)
    (ideal_smul F allocation m ε e) (supportRate_pos (K := K) (tick := tick) allocation).le hc hm'.2 ?_ ?_ ?_ ?_
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
      letI _rawInst : MulAction (Symmetries (K := K) (tick := tick) allocation m) (Raw (K := K) (tick := tick) allocation m) := rawAction allocation m e
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

end MatrixAllFields

end OAI
