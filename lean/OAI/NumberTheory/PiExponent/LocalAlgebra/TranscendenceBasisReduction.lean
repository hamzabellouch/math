import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis

namespace OAI

noncomputable section

namespace PiExponent

open scoped IntermediateField.algebraAdjoinAdjoin

theorem exists_intermediateField_finite_over_simple
    (C E : Type*) [Field C] [Field E] [Algebra C E]
    [Algebra.EssFiniteType C E] {Y : E} (hY : Transcendental C Y) :
    ∃ K : IntermediateField C E,
      Transcendental K Y ∧ FiniteDimensional (IntermediateField.adjoin K {Y}) E := by
  classical
  have hsingle : AlgebraicIndepOn C id ({Y} : Set E) := by
    change AlgebraicIndependent C (fun z : ({Y} : Set E) => (z : E))
    rw [algebraicIndependent_singleton_iff ⟨Y, rfl⟩]
    exact hY
  obtain ⟨t, hsub, ht⟩ := exists_isTranscendenceBasis_superset hsingle
  have hYt : Y ∈ t := hsub (Set.mem_singleton Y)
  let s : Set E := t \ {Y}
  let K : IntermediateField C E := IntermediateField.adjoin C s
  have hts : insert Y s = t := by
    ext x
    simp only [s, Set.mem_insert_iff, Set.mem_sdiff, Set.mem_singleton_iff]
    constructor
    · rintro (rfl | ⟨hx, _⟩)
      · exact hYt
      · exact hx
    · intro hx
      by_cases heq : x = Y
      · exact Or.inl heq
      · exact Or.inr ⟨hx, heq⟩
  have hind : AlgebraicIndepOn C id (insert Y s) := by
    rw [hts]
    exact ht.1
  have htr : Transcendental (Algebra.adjoin C s) Y := by
    have hnot : Y ∉ s := by simp [s]
    have hh := (AlgebraicIndepOn.insert_iff hnot).mp hind
    have heq : id '' s = s := Set.image_id s
    rw [heq] at hh
    exact hh.2
  have htrK : Transcendental K Y := by
    intro h
    exact htr (h.restrictScalars (Algebra.adjoin C s))
  refine ⟨K, htrK, ?_⟩
  let L := IntermediateField.adjoin K ({Y} : Set E)
  have hL : L.restrictScalars C = IntermediateField.adjoin C t := by
    dsimp [L, K]
    rw [IntermediateField.adjoin_adjoin_left]
    congr 1
    rw [Set.union_comm, Set.singleton_union, hts]
  have halg : Algebra.IsAlgebraic L E := by
    change Algebra.IsAlgebraic (L.restrictScalars C) E
    rw [hL]
    have hh := ht.isAlgebraic_field
    have heq : Set.range ((↑) : t → E) = t := Subtype.range_coe
    rw [heq] at hh
    exact hh
  let : Algebra.IsAlgebraic L E := halg
  let : IsScalarTower C L E := IsScalarTower.of_algebraMap_eq (fun x => rfl)
  let : Algebra.EssFiniteType L E := Algebra.EssFiniteType.of_comp C L E
  exact Algebra.finite_of_essFiniteType_of_isAlgebraic

end PiExponent

end

end OAI
