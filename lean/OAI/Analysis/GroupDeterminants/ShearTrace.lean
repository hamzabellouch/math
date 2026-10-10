import OAI.Analysis.GroupDeterminants.WeightedTrace

namespace OAI

noncomputable section
open scoped BigOperators Pointwise

namespace GroupRingDeterminant
section IndexedShear
variable {G I : Type} [Group G] [Fintype I] [DecidableEq I]
lemma indexed_trace_log_shear (B S T : Matrix I I (MonoidAlgebra ℂ G))
    (hB : IsUnit B) (hS : S * S = 0) (hT : T * T = 0)
    (htS : ∑ i, (S i i).coeff 1 = 0) (htT : ∑ i, (T i i).coeff 1 = 0) :
    let φ := indexedComplexRepresentation (G := G) (I := I)
    groupTrace (CFC.log (star (φ ((1 + S) * B * (1 + T))) * φ ((1 + S) * B * (1 + T)))) =
      groupTrace (CFC.log (star (φ B) * φ B)) := by
  let e := Matrix.reindexAlgEquiv ℂ (MonoidAlgebra ℂ G) (Fintype.equivFin I)
  have hs : e S * e S = 0 := by rw [← map_mul, hS, map_zero]
  have ht : e T * e T = 0 := by rw [← map_mul, hT, map_zero]
  have hts : ∑ i, ((e S) i i).coeff 1 = 0 :=
    ((Fintype.equivFin I).symm.sum_comp (fun i => (S i i).coeff 1)).trans htS
  have htt : ∑ i, ((e T) i i).coeff 1 = 0 :=
    ((Fintype.equivFin I).symm.sum_comp (fun i => (T i i).coeff 1)).trans htT
  have H := groupTrace_log_shear_invariant (e B) (e S) (e T)
    (hB.map e.toRingHom) hs ht hts htt 1
  change groupTrace (CFC.log (star (complexOperator (e ((1 + S) * B * (1 + T)))) *
    complexOperator (e ((1 + S) * B * (1 + T))))) =
      groupTrace (CFC.log (star (complexOperator (e B)) * complexOperator (e B)))
  simpa only [map_mul, map_add, map_one, complexOperator_mul, complexOperator_add,
    complexOperator_one, one_smul] using H
end IndexedShear
end GroupRingDeterminant

end

end OAI
