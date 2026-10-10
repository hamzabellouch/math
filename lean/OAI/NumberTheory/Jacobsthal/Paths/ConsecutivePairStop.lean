import OAI.NumberTheory.Jacobsthal.Estimates.CanonicalPairCylinders

namespace OAI

namespace Erdos970

section

namespace Erdos970Dependency.MarkedVisits
open Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal Classical

noncomputable def boundedPairCylinder (a N n : ℕ) (v H : ℝ) : Set (RawHistory N) :=
  if hn : a+2*n+1 ≤ N then firstPairHitEvent a n N hn v H else ∅

lemma boundedPairCylinder_measurable (a N n : ℕ) (v H : ℝ) : MeasurableSet (boundedPairCylinder a N n v H) := by
  unfold boundedPairCylinder
  split_ifs with hn
  · exact firstPairHitEvent_measurable a n N hn v H
  · exact MeasurableSet.empty

lemma boundedPairCylinder_disjoint (a N : ℕ) (v H : ℝ) :
    Pairwise (fun n m : ℕ => Disjoint (boundedPairCylinder a N n v H) (boundedPairCylinder a N m v H)) := by
  intro n m hnm
  unfold boundedPairCylinder
  split_ifs with hn hm
  · exact firstPairHitEvent_disjoint hn hm hnm v H
  all_goals simp

noncomputable def anyPairHit (a N : ℕ) (v H : ℝ) : Set (RawHistory N) :=
  {h | ∃ n : ℕ, ∃ hn : a+2*n+1 ≤ N, h ∈ pairHitTest a n N hn v H}

lemma anyPairHit_measurable (a N : ℕ) (v H : ℝ) : MeasurableSet (anyPairHit a N v H) := by
  unfold anyPairHit
  simp only [ofPred_exists]
  apply MeasurableSet.iUnion
  intro n
  apply MeasurableSet.iUnion
  intro hn
  exact pairHitTest_measurable a n N hn v H

theorem firstPairHit_union_eq_any (a N : ℕ) (v H : ℝ) :
    (⋃ n ∈ Finset.range (N+1), boundedPairCylinder a N n v H)=anyPairHit a N v H := by
  ext h
  constructor
  · intro hh
    obtain ⟨n,hh⟩ := mem_iUnion.mp hh
    obtain ⟨_hn,hh⟩ := mem_iUnion.mp hh
    by_cases hn : a+2*n+1 ≤ N
    · rw [boundedPairCylinder,dite_eq_left hn] at hh
      exact ⟨n,hn,hh.2⟩
    · simp [boundedPairCylinder,hn] at hh
  · intro hh
    have hex : ∃ n : ℕ, ∃ hn : a+2*n+1 ≤ N, h ∈ pairHitTest a n N hn v H := hh
    obtain ⟨hn,hHit⟩ := Nat.find_spec hex
    have hNo : h ∈ noPairHits a (Nat.find hex) N (by omega) v H := by
      intro k hk
      exact (Nat.find_min hex k.2) ⟨(by have h:=k.2; omega),hk⟩
    refine mem_iUnion.mpr ⟨Nat.find hex,mem_iUnion.mpr ⟨?_,?_⟩⟩
    · exact Finset.mem_range.mpr (by omega)
    · rw [boundedPairCylinder,dite_eq_left hn]
      exact ⟨hNo,hHit⟩

theorem canonical_first_hit_measure (a N : ℕ) (v H : ℝ) (past : RawHistory a) :
    rawExtension a N past (anyPairHit a N v H)=
      ∑ n ∈ Finset.range (N+1), rawExtension a N past (boundedPairCylinder a N n v H) := by
  rw [← firstPairHit_union_eq_any]
  exact measure_biUnion_finset (fun n _hn m _hm hnm => boundedPairCylinder_disjoint a N v H hnm)
    (fun n _hn => boundedPairCylinder_measurable a N n v H)

end Erdos970Dependency.MarkedVisits

end

section

namespace Erdos970Dependency.MarkedVisits
open Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal Classical

noncomputable def completedPairHit (a N n : ℕ) (v H : ℝ) : Kernel (RawHistory a) (RawHistory N) :=
  (rawExtension a N).restrict (boundedPairCylinder_measurable a N n v H)

instance completedPairHit_isFiniteKernel (a N n : ℕ) (v H : ℝ) : IsFiniteKernel (completedPairHit a N n v H) := by
  unfold completedPairHit
  infer_instance

theorem completedPairHit_eq_extension {a N n : ℕ} (hn : a+2*n+1 ≤ N) (v H : ℝ) :
    completedPairHit a N n v H=rawExtension (a+2*n+1) N ∘ₖ pairStoppedHistory a n v H := by
  unfold completedPairHit pairStoppedHistory
  have hB := firstPairHitEvent_measurable a n (a+2*n+1) le_rfl v H
  have he := rawExtension_restrict_comp (show a ≤ a+2*n+1 by omega) hn hB MeasurableSet.univ
  rw [Kernel.restrict_univ] at he
  have hc : boundedPairCylinder a N n v H=
      rawPrefix hn ⁻¹' firstPairHitEvent a n (a+2*n+1) le_rfl v H ∩ univ := by
    rw [boundedPairCylinder,dite_eq_left hn,inter_univ,firstPairHitEvent_prefix]
  ext past S hS
  have heS := congrArg (fun K : Kernel (RawHistory a) (RawHistory N) => K past S) he
  rw [Kernel.restrict_apply' _ _ _ hS] at heS
  rw [Kernel.restrict_apply' _ _ _ hS,hc]
  exact heS

lemma completedPairHit_le (a N n : ℕ) (v H : ℝ) (past : RawHistory a) :
    completedPairHit a N n v H past ≤ rawExtension a N past := by
  rw [completedPairHit,Kernel.restrict_apply]
  exact Measure.restrict_le_self

lemma boundedPairCylinder_empty {a N n : ℕ} (hn : N < a+2*n+1) (v H : ℝ) :
    boundedPairCylinder a N n v H=∅ := by
  rw [boundedPairCylinder,dite_eq_right (not_le_of_gt hn)]

lemma firstPairHit_iUnion_eq_any (a N : ℕ) (v H : ℝ) :
    (⋃ n : ℕ, boundedPairCylinder a N n v H)=anyPairHit a N v H := by
  rw [← firstPairHit_union_eq_any]
  apply Subset.antisymm
  · intro h hh
    obtain ⟨n,hC⟩ := mem_iUnion.mp hh
    have hn : a+2*n+1 ≤ N := by
      by_contra hn
      simp [boundedPairCylinder,hn] at hC
    exact mem_iUnion.mpr ⟨n,mem_iUnion.mpr ⟨Finset.mem_range.mpr (by omega),hC⟩⟩
  · intro h hh
    obtain ⟨n,hh⟩ := mem_iUnion.mp hh
    obtain ⟨_hn,hC⟩ := mem_iUnion.mp hh
    exact mem_iUnion.mpr ⟨n,hC⟩

theorem completedPairHit_sum (a N : ℕ) (v H : ℝ) :
    Kernel.sum (fun n : ℕ => completedPairHit a N n v H)=
      (rawExtension a N).restrict (anyPairHit_measurable a N v H) := by
  ext past S hS
  rw [Kernel.sum_apply' _ _ hS,Kernel.restrict_apply]
  have he := Measure.restrict_iUnion (μ := rawExtension a N past)
    (boundedPairCylinder_disjoint a N v H) (fun n => boundedPairCylinder_measurable a N n v H)
  rw [firstPairHit_iUnion_eq_any] at he
  rw [he,Measure.sum_apply _ hS]
  apply tsum_congr
  intro n
  rw [completedPairHit,Kernel.restrict_apply]

theorem completedPairHit_sum_le (a N : ℕ) (v H : ℝ) (past : RawHistory a) :
    (Kernel.sum (fun n : ℕ => completedPairHit a N n v H)) past ≤ rawExtension a N past := by
  rw [completedPairHit_sum,Kernel.restrict_apply]
  exact Measure.restrict_le_self

lemma completedPairHit_sum_mass_le_one (a N : ℕ) (v H : ℝ) (past : RawHistory a) :
    (Kernel.sum (fun n : ℕ => completedPairHit a N n v H)) past univ ≤ 1 :=
  (completedPairHit_sum_le a N v H past univ).trans_eq measure_univ

end Erdos970Dependency.MarkedVisits

end

section

namespace Erdos970Dependency.MarkedVisits
open Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal Classical
open NumberTheoryLean.FinitePathMeasures NumberTheoryLean.FirstHitKernels
open NumberTheoryLean.KernelPotential

noncomputable def regenerativeCostWindow (v H : ℝ) : Set CostState :=
  regenerationSet ∩ (Prod.snd ⁻¹' Icc v (v+H))

lemma regenerativeCostWindow_measurable (v H : ℝ) : MeasurableSet (regenerativeCostWindow v H) :=
  regenerationSet_measurable.inter (measurableSet_Icc.preimage measurable_snd)

noncomputable def markedArrival : Set CostState := {z | firstArrivalMark z=true}
lemma markedArrival_measurable : MeasurableSet markedArrival := firstArrivalMark_measurable (measurableSet_singleton true)

noncomputable def consecutiveCapture (v H : ℝ) : Kernel CostState CostState :=
  (costKernel.restrict markedArrival_measurable) ∘ₖ stateFilter (regenerativeCostWindow_measurable v H)

noncomputable def consecutiveFirstContinue (v H : ℝ) : Kernel CostState CostState :=
  Kernel.piecewise (regenerativeCostWindow_measurable v H)
    (costKernel.restrict markedArrival_measurable.compl) costKernel

noncomputable def consecutiveContinue (v H : ℝ) : Kernel CostState CostState :=
  costKernel ∘ₖ consecutiveFirstContinue v H

instance consecutiveCapture_isFiniteKernel (v H : ℝ) : IsFiniteKernel (consecutiveCapture v H) := by
  unfold consecutiveCapture
  infer_instance

instance consecutiveFirstContinue_isFiniteKernel (v H : ℝ) : IsFiniteKernel (consecutiveFirstContinue v H) := by
  unfold consecutiveFirstContinue
  infer_instance

instance consecutiveContinue_isFiniteKernel (v H : ℝ) : IsFiniteKernel (consecutiveContinue v H) := by
  unfold consecutiveContinue
  infer_instance

theorem consecutive_first_partition (v H : ℝ) :
    consecutiveCapture v H+consecutiveFirstContinue v H=costKernel := by
  ext z S hS
  rw [_root_.add_apply,Measure.add_apply,consecutiveCapture,stateFilter_input,
    consecutiveFirstContinue,Kernel.piecewise_apply]
  by_cases hz : z ∈ regenerativeCostWindow v H
  · rw [ite_eq_left hz,ite_eq_left hz,Kernel.restrict_apply,Kernel.restrict_apply,
      ← Measure.add_apply,Measure.restrict_add_restrict_compl markedArrival_measurable]
  · rw [ite_eq_right hz,ite_eq_right hz]
    simp

instance consecutive_stop_isMarkov (v H : ℝ) : IsMarkovKernel (consecutiveCapture v H+consecutiveContinue v H) := by
  constructor
  intro z
  constructor
  rw [_root_.add_apply,Measure.add_apply,consecutiveContinue,Kernel.comp_apply' _ _ _ MeasurableSet.univ]
  have hm : (∫⁻ y, costKernel y univ ∂consecutiveFirstContinue v H z)=consecutiveFirstContinue v H z univ := by
    simp
  rw [hm,← Measure.add_apply,← _root_.add_apply,consecutive_first_partition]
  exact measure_univ

noncomputable def consecutiveMarkedHit (v H : ℝ) : Kernel CostState CostState :=
  potential (consecutiveCapture v H) (consecutiveContinue v H)

lemma consecutiveMarkedHit_mass_le_one (v H : ℝ) (z : CostState) : consecutiveMarkedHit v H z univ ≤ 1 :=
  capturePotential_mass_le_one _ _ z

end Erdos970Dependency.MarkedVisits

end

end Erdos970

end OAI
