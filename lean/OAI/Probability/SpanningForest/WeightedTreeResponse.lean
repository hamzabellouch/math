import OAI.Probability.SpanningForest.WeightedTreeTransport

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem336.WeightedTree

theorem ustResponse_weight_eq (K : FiniteSubgraphCode) (h : Field)
    (T : USTResponse.TreeSample K) :
    USTResponse.weight K (fun e => h e.1) T = weight h T.1 := by
  classical
  have hsub : T.1 ⊆ K.2 := (USTResponse.tree_property K T).1
  unfold USTResponse.weight USTResponse.indicator weight
  congr 1
  rw [← Finset.sum_subtype K.2 (fun _ => Iff.rfl)
    (fun e => h e * if e ∈ T.1 then (1 : ℝ) else 0)]
  simp_rw [mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter, Finset.filter_mem_eq_inter,
    Finset.inter_eq_right.mpr hsub]

theorem ustResponse_partition_eq (K : FiniteSubgraphCode) (h : Field) :
    USTResponse.partition K (fun e => h e.1) = partition K h := by
  classical
  unfold USTResponse.partition
  simp_rw [ustResponse_weight_eq]
  exact (Finset.sum_subtype (spanningTrees K) (fun _ => Iff.rfl)
    (fun T => weight h T)).symm

theorem ustResponse_inclusion_eq (K : FiniteSubgraphCode) (h : Field)
    (e : USTResponse.FiniteEdge K) :
    USTResponse.inclusion K (fun f => h f.1) e = inclusion K e.1 h := by
  classical
  rw [USTResponse.inclusion_eq_ratio, ustResponse_partition_eq]
  unfold inclusion
  congr 1
  simp_rw [ustResponse_weight_eq]
  unfold USTResponse.indicator
  rw [← Finset.sum_subtype (spanningTrees K) (fun _ => Iff.rfl)
    (fun T => weight h T * if e.1 ∈ T then (1 : ℝ) else 0)]
  simp_rw [mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter]
  rfl

theorem inclusion_response_of_coordinate_bound (K : FiniteSubgraphCode)
    (hne : (spanningTrees K).Nonempty)
    (hneg : ∀ h e f, e ≠ f → USTResponse.edgeCovariance K h e f ≤ 0)
    (a b : Field) (e : ℕ × ℕ) (D : ℝ) (hD : 0 ≤ D)
    (hab : ∀ f, |b f - a f| ≤ D) :
    |inclusion K e b - inclusion K e a| ≤ D / 2 := by
  classical
  by_cases he : e ∈ K.2
  · rw [← ustResponse_inclusion_eq K b ⟨e, he⟩,
      ← ustResponse_inclusion_eq K a ⟨e, he⟩]
    exact USTResponse.inclusion_response_of_coordinate_bound K hne hneg
      (fun f => a f.1) (fun f => b f.1) ⟨e, he⟩ D hD (fun f => hab f.1)
  · rw [inclusion_eq_zero_of_not_mem he, inclusion_eq_zero_of_not_mem he]
    simpa using div_nonneg hD (by norm_num : (0 : ℝ) ≤ 2)

theorem finiteTilt_response (K : FiniteSubgraphCode)
    (hne : (spanningTrees K).Nonempty)
    (hneg : ∀ h e f, e ≠ f → USTResponse.edgeCovariance K h e f ≤ 0)
    (S : Finset (ℕ × ℕ)) (t : ℝ) (a b : Field) (e : ℕ × ℕ)
    (D : ℝ) (hD : 0 ≤ D) (hab : ∀ f ∈ S, |b f - a f| ≤ D) :
    |inclusion K e (finiteField S t b) - inclusion K e (finiteField S t a)| ≤ D / 2 := by
  apply inclusion_response_of_coordinate_bound K hne hneg _ _ e D hD
  intro f
  by_cases hf : f ∈ S
  · simpa only [finiteField, ite_eq_left hf, sub_sub_sub_cancel_right] using hab f hf
  · simpa only [finiteField, ite_eq_right hf, sub_self, abs_zero] using hD

end Problem336.WeightedTree

end

end OAI
