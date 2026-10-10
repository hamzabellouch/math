import OAI.Analysis.GroupDeterminants.ProjectionData

namespace OAI

noncomputable section
open scoped BigOperators Pointwise

namespace GroupRingDeterminant
section OperatorStar
variable {G : Type} [Group G] {n : ℕ}

lemma complexOperator_star (A : Matrix (Fin n) (Fin n) (MonoidAlgebra ℂ G)) :
    complexOperator (star A) = star (complexOperator A) := by
  classical
  induction A using Matrix.induction_on' with
  | h_zero => simp [complexOperator_zero, star_zero (R := Hilbert G n →L[ℂ] Hilbert G n)]
  | h_add A B hA hB =>
    simp only [star_add, complexOperator_add, hA, hB,
      star_add (R := Hilbert G n →L[ℂ] Hilbert G n)]
  | h_std_basis i j a =>
    induction a using MonoidAlgebra.induction_linear with
    | zero => simp [complexOperator_zero, star_zero (R := Hilbert G n →L[ℂ] Hilbert G n)]
    | add a b ha hb =>
      simp only [Matrix.single_add, star_add, complexOperator_add, ha, hb,
        star_add (R := Hilbert G n →L[ℂ] Hilbert G n)]
    | single g z =>
      change complexOperator (Matrix.conjTranspose _) = _
      rw [Matrix.conjTranspose_single, star_groupAlgebra_single,
        complexOperator_single, complexOperator_single, star_smul, elementaryOperator_star]

end OperatorStar

section IndexedRepresentation
variable {G I : Type} [Group G] [Fintype I] [DecidableEq I]

def indexedComplexRepresentation : Matrix I I (MonoidAlgebra ℂ G) →ₐ[ℂ]
    (Hilbert G (Fintype.card I) →L[ℂ] Hilbert G (Fintype.card I)) :=
  complexAlgebraRepresentation.comp (Matrix.reindexAlgEquiv ℂ (MonoidAlgebra ℂ G)
    (Fintype.equivFin I)).toAlgHom

lemma indexedComplexRepresentation_trace (A : Matrix I I (MonoidAlgebra ℂ G)) :
    groupTrace (indexedComplexRepresentation A) = ∑ i, (A i i).coeff 1 := by
  rw [show indexedComplexRepresentation A = complexOperator
    (Matrix.reindex (Fintype.equivFin I) (Fintype.equivFin I) A) from rfl,
    groupTrace_complex]
  exact (Fintype.equivFin I).symm.sum_comp (fun i => (A i i).coeff 1)

lemma indexedComplexRepresentation_star (A : Matrix I I (MonoidAlgebra ℂ G)) :
    indexedComplexRepresentation (star A) = star (indexedComplexRepresentation A) := by
  change complexOperator (Matrix.reindex _ _ (Matrix.conjTranspose A)) =
    star (complexOperator (Matrix.reindex _ _ A))
  rw [← Matrix.conjTranspose_reindex]
  exact complexOperator_star _

lemma indexedComplexRepresentation_mem (A : Matrix I I (MonoidAlgebra ℂ G)) :
    indexedComplexRepresentation A ∈ closedGroupAlgebra :=
  StarSubalgebra.le_topologicalClosure _ ⟨_, rfl⟩

end IndexedRepresentation
end GroupRingDeterminant

end

end OAI
