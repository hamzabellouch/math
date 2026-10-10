import OAI.GroupTheory.PolycyclicRecognition.Algebra.FiniteAlgebraicConstants

namespace OAI

/-! # Algebraic degree bounds after extending a transcendental field -/

noncomputable section
namespace PolycyclicRecognition

theorem linearIndependent_of_injective_scalar_map
    {R S V J : Type*} [Field R] [Field S] [AddCommGroup V]
    [Module R V] [Module S V] [Fintype J]
    (f : R →+* S) (v : J → V) (hv : LinearIndependent S v)
    (hsmul : ∀ (r : R) (x : V), r • x = f r • x) : LinearIndependent R v := by
  apply Fintype.linearIndependent_iff.mpr
  intro c hc j
  apply f.injective
  rw [map_zero]
  apply Fintype.linearIndependent_iff.mp hv (fun i => f (c i)) _ j
  simpa only [← hsmul] using hc

theorem constants_rank_le_in_field_extension
    {F K E L I : Type*} [Field F] [Field K] [Field E] [Field L]
    [Algebra F K] [Algebra F E] [Algebra K E] [IsScalarTower F K E]
    [Algebra F L] [Algebra L E] [IsScalarTower F L E]
    [Algebra.IsAlgebraic F L] (t : I → K) (ht : AlgebraicIndependent F t)
    [FiniteDimensional (IntermediateField.adjoin F (Set.range t)) E] :
    Module.rank F L ≤ Module.finrank (IntermediateField.adjoin F (Set.range t)) E := by
  let B := IntermediateField.adjoin F (Set.range t)
  let f := IsScalarTower.toAlgHom F K E
  let B' := IntermediateField.adjoin F (Set.range (f ∘ t))
  have hB : B.map f = B' := by
    rw [IntermediateField.adjoin_map, ← Set.range_comp]
  let e : B ≃ₐ[F] B' := (IntermediateField.equivMap B f).trans
    (IntermediateField.equivOfEq hB)
  have he (x : B) : (e.toRingEquiv.toRingHom x : E) = algebraMap K E (x : K) := rfl
  apply rank_le
  intro s hs
  have hli := algebraic_constants_linearIndependent_over_transcendental_field
    (f ∘ t) (ht.map' f.injective) (fun i : s => (i : L)) hs
  have hliB : LinearIndependent B (fun i : s => algebraMap L E (i : L)) := by
    apply linearIndependent_of_injective_scalar_map e.toRingHom _ hli
    intro r x
    simpa only [Algebra.smul_def, IsScalarTower.algebraMap_apply B K E,
      IntermediateField.algebraMap_apply] using
      congrArg (fun y : E => y * x) (he r).symm
  simpa only [Fintype.card_coe] using hliB.fintype_card_le_finrank

end PolycyclicRecognition

end

end OAI
