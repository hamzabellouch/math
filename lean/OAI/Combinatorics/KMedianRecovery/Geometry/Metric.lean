import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.Produce

namespace OAI

namespace MetricKMedianRecovery.RationalMetricInput

@[instance_reducible]
noncomputable def metric (I : RationalMetricInput) : PseudoMetricSpace (Fin I.pointCount) where
  dist x y := I.distance x y
  dist_self x := by exact_mod_cast I.distance_self x
  dist_comm x y := by exact_mod_cast I.distance_symm x y
  dist_triangle x y z := by exact_mod_cast I.distance_triangle x y z

lemma cast_inf' {V : Type*} (S : Finset V) (hS : S.Nonempty) (f : V → ℚ) :
    ((S.inf' hS f:ℚ):ℝ) = S.inf' hS (fun x => (f x:ℝ)) := by
  apply le_antisymm
  · exact Finset.le_inf' hS _ (fun i hi => by exact_mod_cast Finset.inf'_le f hi)
  · obtain ⟨i,hi,he⟩ := Finset.exists_mem_eq_inf' hS f
    rw [he]
    exact Finset.inf'_le _ hi

lemma metric_cost (I : RationalMetricInput) (S : Finset (Fin I.pointCount)) :
    @LocalSearch.cost _ I.metric I.clients S = (I.cost S:ℝ) := by
  by_cases hS : S.Nonempty
  · simp only [cost,LocalSearch.cost,LocalSearch.connection,dite_eq_left hS,Rat.cast_sum]
    apply Finset.sum_congr rfl
    intro p _
    exact (cast_inf' S hS (I.distance p)).symm
  · simp only [cost,LocalSearch.cost,LocalSearch.connection,dite_eq_right hS,
      Finset.sum_const_zero,Rat.cast_zero]

lemma metric_optimum (I : RationalMetricInput) :
    @LocalSearch.optimum _ I.metric I.facilities I.clients I.budget = (I.optimum:ℝ) := by
  let := I.metric
  have h : (LocalSearch.feasibleSets I.facilities I.budget).Nonempty :=
    LocalSearch.feasibleSets_nonempty _ I.facilities_nonempty _ I.budget_pos
  have hf : LocalSearch.cost I.clients = fun S => (I.cost S:ℝ) := funext (metric_cost I)
  rw [LocalSearch.optimum,dite_eq_left h,hf,optimum,cast_inf']
  rfl

lemma cost_nonneg (I : RationalMetricInput) (S : Finset (Fin I.pointCount)) : 0 ≤ I.cost S := by
  have h := @LocalSearch.cost_nonneg _ I.metric I.clients S
  rw [metric_cost] at h
  exact_mod_cast h

lemma optimum_nonneg (I : RationalMetricInput) : 0 ≤ I.optimum := by
  have h := @LocalSearch.optimum_nonneg _ I.metric I.facilities I.clients I.budget
  rw [metric_optimum] at h
  exact_mod_cast h

def outputBits (I : RationalMetricInput) (S : Finset (Fin I.pointCount)) : List Bool :=
  List.ofFn (fun i : Fin I.pointCount => decide (i ∈ S))

lemma decode_outputBits (I : RationalMetricInput) (S : Finset (Fin I.pointCount)) (hSF : S ⊆ I.facilities) :
    I.decodeOutput (I.outputBits S) = S := by
  ext i
  simp only [decodeOutput,outputBits,Finset.mem_filter,List.getElem?_ofFn,i.isLt,
    dite_true,Option.getD_some,Fin.eta,decide_eq_true_eq]
  exact and_iff_right_of_imp (fun hi => hSF hi)

end MetricKMedianRecovery.RationalMetricInput

end OAI
