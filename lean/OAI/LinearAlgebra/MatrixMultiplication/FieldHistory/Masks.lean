import OAI.LinearAlgebra.MatrixMultiplication.FieldHistory.MaskCore
import OAI.LinearAlgebra.MatrixMultiplication.FieldHistory.ChildLaws
import OAI.LinearAlgebra.MatrixMultiplication.FieldHistory.Support
import OAI.LinearAlgebra.MatrixMultiplication.Recovery.HistorySymmetry
import OAI.LinearAlgebra.MatrixMultiplication.Recovery.InheritedMaskAction
import OAI.LinearAlgebra.MatrixMultiplication.Recovery.InheritedMaskOrbitFilter

namespace OAI

/-! Finite extraction histories, inherited masks and recovery bounds. -/

noncomputable section

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

end OAI
