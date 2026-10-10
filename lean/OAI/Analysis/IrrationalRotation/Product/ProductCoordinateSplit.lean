import Mathlib.Probability.ProductMeasure
import Mathlib.Tactic

namespace OAI

noncomputable section
open MeasureTheory MeasureTheory.Measure Set
open scoped ENNReal BigOperators

namespace Invariant233.ProductCoordinateSplit

variable {ι : Type*} {X : ι → Type*} [∀ i, MeasurableSpace (X i)]

theorem measurePreserving_split
    (μ : (i : ι) → Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]
    (p : ι → Prop) [DecidablePred p] :
    MeasurePreserving (MeasurableEquiv.piEquivPiSubtypeProd X p)
      (Measure.infinitePi μ)
      ((Measure.infinitePi fun i : Subtype p => μ i).prod
        (Measure.infinitePi fun i : {i // ¬ p i} => μ i)) := by
  classical
  let e := (MeasurableEquiv.piEquivPiSubtypeProd X p).symm
  apply MeasurePreserving.symm e
  refine ⟨e.measurable, ?_⟩
  apply Measure.eq_infinitePi
  intro s t ht
  have heq : e ⁻¹' Set.pi (s : Set ι) t =
      (Set.pi (s.subtype p) (fun i : Subtype p => t i)) ×ˢ
      (Set.pi (s.subtype (fun i => ¬ p i)) (fun i : {i // ¬p i} => t i)) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_pi, Finset.mem_coe, Set.mem_prod,
      Finset.mem_subtype]
    constructor
    · intro h
      constructor
      · intro i hi
        have := h i hi
        simpa [e, MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd, i.property]
          using this
      · intro i hi
        have := h i hi
        simpa [e, MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd, i.property]
          using this
    · rintro ⟨hpos, hneg⟩ i hi
      by_cases hip : p i
      · simpa [e, MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd, hip]
          using hpos ⟨i, hip⟩ hi
      · simpa [e, MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd, hip]
          using hneg ⟨i, hip⟩ hi
  rw [e.map_apply, heq, Measure.prod_prod,
    Measure.infinitePi_pi (fun i : Subtype p => μ i) (fun i _ => ht i),
    Measure.infinitePi_pi (fun i : {i // ¬p i} => μ i) (fun i _ => ht i)]
  rw [Finset.prod_subtype_eq_prod_filter (s := s) (p := p) (fun i => μ i (t i)),
    Finset.prod_subtype_eq_prod_filter (s := s) (p := fun i => ¬p i) (fun i => μ i (t i)),
    Finset.prod_filter_mul_prod_filter_not]

end Invariant233.ProductCoordinateSplit

end

end OAI
