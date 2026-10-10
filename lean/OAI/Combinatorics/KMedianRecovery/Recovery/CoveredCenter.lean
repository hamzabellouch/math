import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.Virtual
import OAI.Combinatorics.KMedianRecovery.Recovery.Cluster
import OAI.Combinatorics.KMedianRecovery.Recovery.SingleRadiusRatio

namespace OAI

namespace MetricKMedianRecovery.Sampling.Comparison
variable {V : Type*} [LinearOrder V] [PseudoMetricSpace V] {D S O : Finset V}
noncomputable def coveredCenter (C : Comparison D S O) (s : State V)
    (i : Fin s.leaves.length) : V := C.assign s.leaves[i.val].1
lemma coveredCenter_mem (C : Comparison D S O) (s : State V) (i : Fin s.leaves.length) :
    C.coveredCenter s i ∈ C.covered s := by
  apply List.mem_toFinset.mpr
  exact List.mem_map.mpr ⟨s.leaves[i.val],List.getElem_mem i.isLt,rfl⟩
lemma exists_coveredCenter (C : Comparison D S O) (s : State V) (o : V)
    (ho : o ∈ C.covered s) : ∃ i, C.coveredCenter s i = o := by
  obtain ⟨z,hz,hzo⟩ := List.mem_map.mp (List.mem_toFinset.mp ho)
  obtain ⟨j,hj,hjz⟩ := List.mem_iff_getElem.mp hz
  refine ⟨⟨j,hj⟩,?_⟩
  simp only [coveredCenter,hjz,hzo]
lemma coveredCenter_injective (C : Comparison D S O) (hD : D.Nonempty)
    (kappa : ℝ) (s : State V) (hs : C.Correct hD kappa s) :
    Function.Injective (C.coveredCenter s) := by
  intro i j hij
  apply Fin.ext
  have hi : i.val < (s.leaves.map (fun z => C.assign z.1)).length := by simp
  have hj : j.val < (s.leaves.map (fun z => C.assign z.1)).length := by simp
  have he : (s.leaves.map (fun z => C.assign z.1))[i.val]'hi =
      (s.leaves.map (fun z => C.assign z.1))[j.val]'hj := by
    simpa only [List.getElem_map, coveredCenter] using hij
  exact hs.2.1.getElem_inj_iff.mp he
lemma covered_card_eq_length (C : Comparison D S O) (hD : D.Nonempty)
    (kappa : ℝ) (s : State V) (hs : C.Correct hD kappa s) :
    (C.covered s).card = s.leaves.length := by
  rw [covered,List.toFinset_card_of_nodup hs.2.1,List.length_map]
lemma coveredCenter_ball (C : Comparison D S O) (hD : D.Nonempty)
    (kappa : ℝ) (s : State V) (hs : C.Correct hD kappa s) (i : Fin s.leaves.length) :
    dist s.leaves[i.val].1 (C.coveredCenter s i) ≤ s.leaves[i.val].2 :=
  (hs.2.2 _ (List.getElem_mem i.isLt)).2.2.2.2.1
lemma coveredCenter_facility (C : Comparison D S O) (hD : D.Nonempty)
    (kappa : ℝ) (s : State V) (hs : C.Correct hD kappa s)
    (F : Finset V) (hOF : O ⊆ F) (i : Fin s.leaves.length) : C.coveredCenter s i ∈ F := by
  have hh := C.correct_covered_subset hD kappa s hs (C.coveredCenter_mem s i)
  exact hOF (Finset.mem_sdiff.mp hh).1
lemma leaderPair_eq_indexed (C : Comparison D S O) (hD : D.Nonempty)
    (kappa : ℝ) (s : State V) (hs : C.Correct hD kappa s) (i : Fin s.leaves.length) :
    C.leaderPair s (C.coveredCenter s i) = s.leaves[i.val] := by
  have hh := C.leaderPair_spec s (C.coveredCenter s i) (C.coveredCenter_mem s i)
  exact List.inj_on_of_nodup_map hs.2.1 hh.1 (List.getElem_mem i.isLt) hh.2

lemma exact_completion_counts (C : Comparison D S O) (hD : D.Nonempty)
    (kappa : ℝ) (s : State V) (hs : C.Correct hD kappa s) :
    s.leaves.length + (C.bad \ C.covered s).card = C.bad.card ∧
    s.deleted.card + (C.nonproxy \ s.deleted).card = C.bad.card := by
  have hcov := C.correct_covered_subset hD kappa s hs
  rw [Finset.card_sdiff_of_subset hcov,Finset.card_sdiff_of_subset hs.1,
    C.covered_card_eq_length hD kappa s hs,C.nonproxy_card]
  have hc := C.correct_lengths hD kappa s hs
  omega

noncomputable def coveredIndex (C : Comparison D S O) (s : State V) (o : V)
    (ho : o ∈ C.covered s) : Fin s.leaves.length :=
  Classical.choose (C.exists_coveredCenter s o ho)
lemma coveredIndex_spec (C : Comparison D S O) (s : State V) (o : V)
    (ho : o ∈ C.covered s) : C.coveredCenter s (C.coveredIndex s o ho) = o :=
  Classical.choose_spec (C.exists_coveredCenter s o ho)
lemma leafPair_index (C : Comparison D S O) (hD : D.Nonempty)
    (kappa : ℝ) (s : State V) (hs : C.Correct hD kappa s) (o : V)
    (ho : o ∈ C.covered s) :
    s.leaves[(C.coveredIndex s o ho).val] = C.leaderPair s o := by
  have hh := C.leaderPair_eq_indexed hD kappa s hs (C.coveredIndex s o ho)
  simpa only [C.coveredIndex_spec s o ho] using hh.symm
end MetricKMedianRecovery.Sampling.Comparison
namespace MetricKMedianRecovery.Sampling
open Completion
variable {V : Type*} [LinearOrder V] [PseudoMetricSpace V]

def leafCenter (s : State V) (i : Fin s.leaves.length) : V := s.leaves[i.val].1
def leafRadius (s : State V) (i : Fin s.leaves.length) : ℝ := s.leaves[i.val].2

def toVirtual (s : State V) (t : Tag V) : Virtual V s.leaves.length :=
  match ofLex t with
  | .inl v => .real v
  | .inr 0 => .permanent
  | .inr (j+1) => if h : j < s.leaves.length then .ball ⟨j,h⟩ else .permanent

omit [LinearOrder V] [PseudoMetricSpace V] in
lemma toVirtual_real_iff (s : State V) (t : Tag V) (v : V) :
    toVirtual s t = .real v ↔ t = realTag v := by
  cases ht : ofLex t with
  | inl u =>
    have he : t = realTag u := congrArg toLex ht
    subst t
    simp [toVirtual,realTag]
  | inr j =>
    have he : t = leafTag j := congrArg toLex ht
    subst t
    cases j with
    | zero => simp [toVirtual,leafTag,realTag]
    | succ j => simp [toVirtual,leafTag,realTag]; split <;> simp_all

omit [PseudoMetricSpace V] in
lemma toVirtual_mem (S : Finset V) (s : State V) (t : Tag V)
    (ht : t ∈ tags S s) : toVirtual s t ∈ withGhosts (S \ s.deleted) := by
  cases he : ofLex t with
  | inl v =>
    have hh : t = realTag v := congrArg toLex he
    have hv := (real_mem_tags S s v).mp (hh ▸ ht)
    simp [toVirtual,he,hv]
  | inr j =>
    cases j with
    | zero => simp [toVirtual,he]
    | succ j => simp only [toVirtual,he]; split <;> simp

lemma toVirtual_distance (S : Finset V) (Δ : ℝ) (s : State V) (x : V) (t : Tag V)
    (ht : t ∈ tags S s) :
    virtualDistance (leafCenter s) (leafRadius s) Δ x (toVirtual s t) = tagDistance Δ s x t := by
  cases he : ofLex t with
  | inl v => simp [toVirtual,tagDistance,he,virtualDistance]
  | inr j =>
    have htag : t = leafTag j := congrArg toLex he
    have hj := (leaf_mem_tags S s j).mp (htag ▸ ht)
    cases j with
    | zero => simp [toVirtual,tagDistance,he,virtualDistance]
    | succ j =>
      have hj' : j < s.leaves.length := by omega
      simp [toVirtual,tagDistance,he,hj',virtualDistance,leafCenter,leafRadius]

lemma reference_eq_virtualNearest (S : Finset V) (Δ : ℝ) (s : State V) (x : V) :
    reference S Δ s x = virtualNearest (S \ s.deleted) (leafCenter s) (leafRadius s) Δ x := by
  apply le_antisymm
  · apply Finset.le_inf'
    intro t ht
    cases t with
    | real v =>
      exact reference_le_real S Δ s x v (real_mem_withGhosts.mp ht)
    | ball i =>
      exact reference_le_leaf S Δ s x i.val s.leaves[i.val]
        (List.getElem?_eq_getElem i.isLt)
    | permanent => exact reference_le_diameter S Δ s x
  · have hh := Finset.inf'_le (virtualDistance (leafCenter s) (leafRadius s) Δ x)
      (toVirtual_mem S s (chosen S Δ s x) (chosen_mem S Δ s x))
    simpa only [toVirtual_distance S Δ s x _ (chosen_mem S Δ s x), virtualNearest, reference] using hh

noncomputable def completionAssignment (S : Finset V) (Δ : ℝ) (s : State V) (x : V) :=
  toVirtual s (chosen S Δ s x)

lemma completionAssignment_mem (S : Finset V) (Δ : ℝ) (s : State V) (x : V) :
    completionAssignment S Δ s x ∈ withGhosts (S \ s.deleted) :=
  toVirtual_mem S s (chosen S Δ s x) (chosen_mem S Δ s x)

lemma completionAssignment_distance (S : Finset V) (Δ : ℝ) (s : State V) (x : V) :
    virtualDistance (leafCenter s) (leafRadius s) Δ x (completionAssignment S Δ s x) =
      virtualNearest (S \ s.deleted) (leafCenter s) (leafRadius s) Δ x := by
  exact (toVirtual_distance S Δ s x _ (chosen_mem S Δ s x)).trans
    (reference_eq_virtualNearest S Δ s x)

lemma completionAssignment_real_iff (S : Finset V) (Δ : ℝ) (s : State V) (x v : V) :
    completionAssignment S Δ s x = .real v ↔ chosen S Δ s x = realTag v :=
  toVirtual_real_iff s (chosen S Δ s x) v

lemma assigned_clients_agree (D S R : Finset V) (Δ : ℝ) (s : State V) :
    D.filter (fun p => ∃ v ∈ R, completionAssignment S Δ s p = .real v) =
      D.filter (fun p => ∃ v ∈ R, chosen S Δ s p = realTag v) := by
  ext p
  simp only [Finset.mem_filter,completionAssignment_real_iff]

lemma assigned_reference_total_agree (D S R : Finset V) (Δ : ℝ) (s : State V) :
    (∑ p ∈ D.filter (fun p => ∃ v ∈ R, completionAssignment S Δ s p = .real v),
      virtualNearest (S \ s.deleted) (leafCenter s) (leafRadius s) Δ p) =
    ∑ p ∈ D.filter (fun p => ∃ v ∈ R, chosen S Δ s p = realTag v), reference S Δ s p := by
  rw [assigned_clients_agree]
  apply Finset.sum_congr rfl
  intro p _
  exact (reference_eq_virtualNearest S Δ s p).symm

end MetricKMedianRecovery.Sampling

end OAI
