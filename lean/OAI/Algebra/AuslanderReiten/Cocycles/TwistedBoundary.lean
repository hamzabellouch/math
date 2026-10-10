import OAI.Algebra.AuslanderReiten.Cocycles.TwistedBoundaryFormula

namespace OAI

noncomputable section

namespace ArExplicit.CocycleData

variable {k : Type*} [Field k] (q : k)

def radicalIndices : Finset TIndex :=
  Finset.univ.filter fun i => i ≠ TIndex.vertex false ∧ i ≠ TIndex.vertex true

private theorem contraction_on_vertex (H : kˣ) (a b : T k q) (v : Bool) :
    p q a b (TrivialExtension.twist H (T.vector q (TIndex.vertex v))) = 0 := by
  rw [twist_vector]
  have hw : (TIndex.vertex v).weight = 0 := by cases v <;> rfl
  rw [hw, pow_zero, one_smul, p_normalized_third]

theorem contraction_radical_sum (H : kˣ) (a b : T k q) :
    (∑ i ∈ radicalIndices, p q a b (TrivialExtension.twist H (T.vector q i)) *
      T.vector q i.star) =
    ∑ i : TIndex, p q a b (TrivialExtension.twist H (T.vector q i)) * T.vector q i.star := by
  apply Finset.sum_subset (Finset.subset_univ _)
  intro i _ hi
  have hv : i = TIndex.vertex false ∨ i = TIndex.vertex true := by
    simpa only [radicalIndices, Finset.mem_filter, Finset.mem_univ, true_and,
      not_and_or, not_not] using hi
  rcases hv with rfl | rfl <;> rw [contraction_on_vertex, zero_mul]

variable [CharP k 2]

theorem twisted_boundary (H : kˣ) (a b : T k q) :
    (∑ i : TIndex, p q a b (TrivialExtension.twist H (T.vector q i)) *
      T.vector q i.star) =
      a * z q H b + z q H (a * b) + z q H a * TrivialExtension.twist H⁻¹ b := by
  have hz : (∑ i : TIndex, p q a b (TrivialExtension.twist H (T.vector q i)) *
      T.vector q i.star) +
      (a * z q H b + z q H (a * b) + z q H a * TrivialExtension.twist H⁻¹ b) = 0 := by
    rw [twisted_contraction_formula, twisted_boundary_formula]
    have hc := boundaryTerms_sum_zero (SparseParity.module_add_self_eq_zero (k := k))
      (evalPair q H a b)
    rw [boundaryTerms, List.map_append, List.sum_append] at hc
    convert! hc using 1
  have hd := SparseParity.module_add_self_eq_zero (k := k)
    (a * z q H b + z q H (a * b) + z q H a * TrivialExtension.twist H⁻¹ b)
  exact add_right_cancel (hz.trans hd.symm)

theorem twisted_boundary_radical (H : kˣ) (a b : T k q) :
    (∑ i ∈ radicalIndices, p q a b (TrivialExtension.twist H (T.vector q i)) *
      T.vector q i.star) =
      a * z q H b + z q H (a * b) + z q H a * TrivialExtension.twist H⁻¹ b := by
  rw [contraction_radical_sum, twisted_boundary]

end ArExplicit.CocycleData

end

end OAI
