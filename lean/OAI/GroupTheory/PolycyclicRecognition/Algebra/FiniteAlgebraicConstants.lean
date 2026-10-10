import OAI.GroupTheory.PolycyclicRecognition.Algebra.IndependentAlgebraicConstants
import Mathlib.FieldTheory.FinTrdeg
import Mathlib.LinearAlgebra.Dimension.Free

namespace OAI

/-! # Algebraic constants in a finitely generated field form a finite extension

After choosing a transcendence basis, a finite extension of its rational
function field bounds every independent family of algebraic constants.
-/

noncomputable section
namespace PolycyclicRecognition

theorem algebraic_constants_rank_le
    {F L E I : Type*} [Field F] [Field L] [Field E]
    [Algebra F L] [Algebra F E] [Algebra L E] [IsScalarTower F L E]
    [Algebra.IsAlgebraic F L] (t : I → E) (ht : AlgebraicIndependent F t)
    [FiniteDimensional (IntermediateField.adjoin F (Set.range t)) E] :
    Module.rank F L ≤ Module.finrank (IntermediateField.adjoin F (Set.range t)) E := by
  apply rank_le
  intro s hs
  have hh := algebraic_constants_linearIndependent_over_transcendental_field
    t ht (fun i : s => (i : L)) hs
  simpa only [Fintype.card_coe] using hh.fintype_card_le_finrank

theorem finite_algebraic_constants_of_transcendental_finite_extension
    {F L E I : Type*} [Field F] [Field L] [Field E]
    [Algebra F L] [Algebra F E] [Algebra L E] [IsScalarTower F L E]
    [Algebra.IsAlgebraic F L] (t : I → E) (ht : AlgebraicIndependent F t)
    [FiniteDimensional (IntermediateField.adjoin F (Set.range t)) E] :
    FiniteDimensional F L := by
  apply Module.rank_lt_aleph0_iff.mp
  exact (algebraic_constants_rank_le t ht).trans_lt Cardinal.natCast_lt_aleph0

theorem finite_algebraicClosure_of_essFiniteType
    (F E : Type*) [Field F] [Field E] [Algebra F E]
    [Algebra.EssFiniteType F E] : FiniteDimensional F (algebraicClosure F E) := by
  obtain ⟨s, hs⟩ := exists_finset_isTranscendenceBasis F E
  have ha := hs.isAlgebraic_field
  have : Algebra.IsAlgebraic (IntermediateField.adjoin F (Set.range ((↑) : s → E))) E := ha
  have : Algebra.EssFiniteType (IntermediateField.adjoin F (Set.range ((↑) : s → E))) E :=
    Algebra.EssFiniteType.of_comp F _ E
  have := Algebra.finite_of_essFiniteType_of_isAlgebraic
    (F := IntermediateField.adjoin F (Set.range ((↑) : s → E))) (E := E)
  exact finite_algebraic_constants_of_transcendental_finite_extension
    ((↑) : s → E) hs.1

end PolycyclicRecognition

end

end OAI
