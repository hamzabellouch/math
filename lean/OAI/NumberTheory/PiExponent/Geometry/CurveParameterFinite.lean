import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis

namespace OAI

namespace PiExponent.CurveParameterFinite

theorem finiteDimensional_adjoin_singleton
    (F E : Type*) [Field F] [Field E] [Algebra F E]
    [Algebra.EssFiniteType F E] (htrdeg : Algebra.trdeg F E ≤ 1)
    {g : E} (hg : Transcendental F g) :
    FiniteDimensional (IntermediateField.adjoin F {g}) E := by
  have hind : AlgebraicIndependent F (fun z : ({g} : Set E) => (z : E)) := by
    rw [algebraicIndependent_singleton_iff ⟨g, rfl⟩]
    exact hg
  have hb := hind.isTranscendenceBasis_of_trdeg_le_of_finite (by simpa using htrdeg)
  have hrange : Set.range (fun z : ({g} : Set E) => (z : E)) = {g} :=
    Subtype.range_coe
  let : Algebra.IsAlgebraic (IntermediateField.adjoin F {g}) E := by
    have ha := hb.isAlgebraic_field
    rw [hrange] at ha
    exact ha
  let : Algebra.EssFiniteType (IntermediateField.adjoin F {g}) E :=
    Algebra.EssFiniteType.of_comp F (IntermediateField.adjoin F {g}) E
  exact Algebra.finite_of_essFiniteType_of_isAlgebraic

theorem finite_over_every_parameter
    (F E : Type*) [Field F] [Field E] [Algebra F E]
    [Algebra.EssFiniteType F E] (htrdeg : Algebra.trdeg F E = 1) :
    ∀ g : E, Transcendental F g →
      FiniteDimensional (IntermediateField.adjoin F {g}) E :=
  fun _ hg => finiteDimensional_adjoin_singleton F E htrdeg.le hg

end PiExponent.CurveParameterFinite

end OAI
